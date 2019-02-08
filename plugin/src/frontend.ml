open Util
open Constr
open Names
open Globnames
open Declarations
open Coqterms
open Lifting
open Caching
open Search
open Lift
open Desugar
open Utilities
open Pp
open Printer

(*
 * Identify an algebraic ornament between two types
 * Define the components of the corresponding equivalence
 * (Don't prove section and retraction)
 *)
let find_ornament n_o d_old d_new =
  let (evd, env) = Pfedit.get_current_context () in
  let trm_o = unwrap_definition env (intern env evd d_old) in
  let trm_n = unwrap_definition env (intern env evd d_new) in
  match map_tuple kind (trm_o, trm_n) with
  | Ind ((m_o, _), _), Ind ((m_n, _), _) ->
    let (_, _, lab_o) = KerName.repr (MutInd.canonical m_o) in
    let (_, _, lab_n) = KerName.repr (MutInd.canonical m_n) in
    let name_o = Label.to_id lab_o in
    let name_n = Label.to_string lab_n in
    let auto_n = with_suffix (with_suffix name_o "to") name_n in
    let n = Option.default auto_n n_o in
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env evd idx_n trm_o trm_n in
    ignore (define_term idx_n evd orn.indexer true);
    Printf.printf "Defined indexing function %s.\n\n" (Id.to_string idx_n);
    let promote = define_term n evd orn.promote true in
    Printf.printf "Defined promotion %s.\n\n" (Id.to_string n);
    let inv_n = with_suffix n "inv" in
    let forget = define_term inv_n evd orn.forget true in
    Printf.printf "Defined forgetful function %s.\n\n" (Id.to_string inv_n);
    (try
       save_ornament (trm_o, trm_n) (promote, forget)
     with _ ->
       Printf.printf "WARNING: Failed to cache ornamental promotion.")
  |_ ->
    failwith "Only inductive types are supported"

(*
 * Lift a definition according to a lifting configuration, defining the lifted
 * definition and declaring it as a lifting of the original definition.
 *)
let lift_definition_by_ornament env evd n l c_old =
  let lifted = do_lift_defn env evd l c_old in
  ignore (define_term n evd lifted true);
  try
    let old_gref = global_of_constr c_old in
    let new_gref = ConstRef (Lib.make_kn n |> Constant.make1) in
    declare_lifted old_gref new_gref;
  with _ ->
    Printf.printf "WARNING: Failed to cache lifting."

(*
 * Lift an inductive type according to a lifting configuration, defining the
 * new lifted version and declaring type-to-type, constructor-to-constructor,
 * and eliminator-to-eliminator liftings.
 *)
let lift_inductive_by_ornament env evm n s l c_old =
  let ind, _ = destInd c_old in
  let ind' = do_lift_ind env evm n s l ind in
  let env' = Global.env () in
  Feedback.msg_notice (str "Defined lifted inductive type " ++ pr_inductive env' ind')

(*
 * Lift the supplied definition or inductive type along the supplied ornament
 * Define the lifted version
 *)
let lift_by_ornament ?(suffix=false) n d_orn d_orn_inv d_old =
  let (evd, env) = Pfedit.get_current_context () in
  let c_orn = intern env evd d_orn in
  let c_orn_inv = intern env evd d_orn_inv in
  let c_old = intern env evd d_old in
  let n_new = if suffix then suffix_term_name c_old n else n in
  let s = if suffix then Id.to_string n else "_" ^ Id.to_string n in
  let are_inds = isInd c_orn && isInd c_orn_inv in
  let lookup os = map_tuple Universes.constr_of_global (lookup_ornament os) in
  let (c_from, c_to) = map_if lookup are_inds (c_orn, c_orn_inv) in
  let l = initialize_lifting env evd c_from c_to in
  if isInd c_old then
    lift_inductive_by_ornament env evd n_new s l c_old
  else
    lift_definition_by_ornament env evd n_new l c_old

(*
 * Translate each fix or match subterm into an equivalent application of an
 * eliminator, defining the new term with the given name.
 *
 * Mutual fix or cofix subterms are not supported.
 *)
let desugar_definition n d =
  (* TODO: Accept old/new names and lookup constant directly *)
  let (evm, env) = Pfedit.get_current_context () in
  let term = intern env evm d |> unwrap_definition env in
  let evm, term' = desugar_term env evm term in
  ignore (define_term n evm term' false);
  Flags.if_verbose Feedback.msg_info
    (seq [str "\nTranslated constant "; str "$OLD"; str " as "; Id.print n])

let desugar_constant subst const const_body =
  let ident = Constant.label const |> Label.to_id in
  let env = Global.env () in
  let evm = Evd.from_env env in
  let term = force_constant_body const_body in
  let desugar = desugar_term ~subst:subst env in
  let evm', term' = desugar evm term in
  let evm', type' = desugar evm' const_body.const_type in
  define_term ~typ:type' ident evm' term' true |> destConstRef

let flip f = fun x y -> f y x

let desugar_inductive subst ind mind_body =
  (* TODO: Clean up and refactor *)
  let ind_body = mind_body.mind_packets.(0) in
  let mind_specif = (mind_body, ind_body) in
  let env = Global.env () in
  let env, univs, arity, cons_types = open_inductive ~global:true env mind_specif in
  let evm = Evd.from_env env in
  let desugar = desugar_term ~subst:subst env in
  let evm, arity' = desugar evm arity in
  let evm, cons_types' = List.fold_left_map desugar evm cons_types in
  declare_inductive
    ind_body.mind_typename (Array.to_list ind_body.mind_consnames)
    (is_ind_body_template ind_body) univs
    mind_body.mind_nparams arity' cons_types'

let decompose_module_signature mod_sign =
  let rec aux mod_arity mod_sign =
    match mod_sign with
    | MoreFunctor (mod_name, mod_type, mod_sign) ->
      aux ((mod_name, mod_type) :: mod_arity) mod_sign
    | NoFunctor mod_fields ->
      mod_arity, mod_fields
  in
  aux [] mod_sign

(*
 * Begin an interactive (i.e., elementwise) definition of a module.
 *
 * Optional arguments allow specifying functor parameters and module signature,
 * each with the obvious default (non-functor and exposed structure).
 *)
let begin_module_structure ?(params=[]) ?(sign=(Vernacexpr.Check [])) id =
  let mod_path =
    Declaremods.start_module Modintern.interp_module_ast None id params sign
  in
  Dumpglob.dump_moddef mod_path "mod";
  mod_path

(*
 * End an interactive (i.e., elementwise) definition of a module, begun earlier
 * with begin_module_structure.
 *)
let end_module_structure () =
  let mod_path = Declaremods.end_module () in
  Dumpglob.dump_modref mod_path "mod"

(*
 * Translate fix and match expressions into eliminations, as in
 * desugar_definition, compositionally throughout a whole module.
 *)
let desugar_module mod_name mod_ref =
  let mod_path =
    Libnames.qualid_of_reference mod_ref |> CAst.with_val Nametab.locate_module
  in
  let mod_body = Global.lookup_module mod_path in
  let mod_arity, mod_fields = decompose_module_signature mod_body.mod_type in
  let mod_path' = begin_module_structure mod_name in
  let _ = (* TODO: Refactor *)
    List.fold_left
      (fun subst (label, body) ->
         try
           begin
             match body with
             | SFBconst const_body ->
               let const = Constant.make2 mod_path label in
               if Globmap.mem (ConstRef const) subst then
                 subst (* Do not re-define any schematic definitions. *)
               else
                 let const' = desugar_constant subst const const_body in
                 Globmap.add (ConstRef const) (ConstRef const') subst
             | SFBmind mind_body ->
               check_inductive_supported mind_body;
               let ind = (MutInd.make2 mod_path label, 0) in
               let ind' = desugar_inductive subst ind mind_body in
               let ncons = Inductiveops.nconstructors ind in
               let sorts = mind_body.mind_packets.(0).mind_kelim in
               Globmap.add (IndRef ind) (IndRef ind') subst |>
               List.fold_right2
                 Globmap.add
                 (List.init ncons (fun i -> ConstructRef (ind, i + 1)))
                 (List.init ncons (fun i -> ConstructRef (ind', i + 1))) |>
               List.fold_right2
                 Globmap.add
                 (List.map (Indrec.lookup_eliminator ind) sorts)
                 (List.map (Indrec.lookup_eliminator ind') sorts)
             | SFBmodule mod_body -> subst (* TODO *)
             | SFBmodtype sig_body -> subst (* TODO *)
           end
         with Pretype_errors.PretypeError _ ->
           "Failed to translate " ^ Label.to_string label |> str |>
           Feedback.msg_warning;
           subst)
      Globmap.empty
      mod_fields
  in
  end_module_structure ();
  Flags.if_verbose Feedback.msg_info
    (seq [str "\nTranslated module "; Libnames.pr_reference mod_ref; str " as "; Id.print mod_name])
