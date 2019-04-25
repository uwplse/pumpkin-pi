open Constr
open Names
open Globnames
open Coqterms
open Lifting
open Caching
open Search
open Lift
open Desugar
open Unpack
open Utilities
open Pp
open Printer
open Coherence
open Equivalence
open Options

(* --- Commands --- *)

(*
 * If the option is enabled, then prove coherence after find_ornament is called.
 * Otherwise, do nothing.
 *)
let maybe_prove_coherence n orn : unit =
  if is_search_coh () then
    let env = Global.env () in
    let evd = Evd.from_env env in
    let coh, coh_typ = prove_coherence env evd orn in
    let coh_n = with_suffix n "coh" in
    let _ = define_term ~typ:coh_typ coh_n evd coh true in
    Printf.printf "Defined coherence proof %s\n\n" (Id.to_string coh_n)
  else
    ()
      
(*
 * If the option is enabled, then prove section and retraction after find_ornament is called.
 * Otherwise, do nothing.
 *)
let maybe_prove_equivalence n inv_n : unit =
  if is_search_equiv () then
    let env = Global.env () in
    let evd = Evd.from_env env in
    let (promote, forget) = map_tuple make_constant (n, inv_n) in
    let l = initialize_lifting env evd promote forget in
    let (section, retraction) = prove_equivalence env evd l in
    let sec_n = with_suffix n "section" in
    let _ = define_term sec_n evd section true in
    Printf.printf "Defined section proof %s\n\n" (Id.to_string sec_n);
    let rec_n = with_suffix n "retraction" in
    let _ = define_term rec_n evd retraction true in
    Printf.printf "Defined retraction proof %s\n\n" (Id.to_string rec_n)
  else
    ()
       
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
    Printf.printf "Defined indexer %s\n\n" (Id.to_string idx_n);
    let promote = define_term n evd orn.promote true in
    Printf.printf "Defined promotion %s\n\n" (Id.to_string n);
    let inv_n = with_suffix n "inv" in
    let forget = define_term inv_n evd orn.forget true in
    Printf.printf "Defined forgetful function %s\n\n" (Id.to_string inv_n);
    maybe_prove_coherence n orn;
    maybe_prove_equivalence n inv_n;
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
  let us = map_tuple (unwrap_definition env) (c_orn, c_orn_inv) in
  let are_inds = isInd (fst us) && isInd (snd us) in
  let lookup os = map_tuple Universes.constr_of_global (lookup_ornament os) in
  let (c_from, c_to) = if are_inds then lookup us else (c_orn, c_orn_inv) in
  let l = initialize_lifting env evd c_from c_to in
  let u_old = unwrap_definition env c_old in
  if isInd u_old then
    let from_typ = fst (on_type ind_of_promotion_type env evd l.orn.promote) in
    if not (equal u_old from_typ) then
      lift_inductive_by_ornament env evd n_new s l c_old
    else
      lift_definition_by_ornament env evd n_new l c_old
  else
    lift_definition_by_ornament env evd n_new l c_old

(*
 * Translate each fix or match subterm into an equivalent application of an
 * eliminator, defining the new term with the given name.
 *
 * Mutual fix or cofix subterms are not supported.
 *)
let do_desugar_constant ident const_ref =
  ignore
    begin
      qualid_of_reference const_ref |> Nametab.locate_constant |>
      Global.lookup_constant |> transform_constant ident desugar_constr
    end

(*
 * Translate fix and match expressions into eliminations, as in
 * do_desugar_constant, compositionally throughout a whole module.
 *
 * The optional argument is a list of constants outside the module to include
 * in the translated module as if they were components in the input module.
 *)
let do_desugar_module ?(incl=[]) ident mod_ref =
  let open Util in
  let consts = List.map (qualid_of_reference %> Nametab.locate_constant) incl in
  let include_constant subst const =
    let ident = Label.to_id (Constant.label const) in
    let tr_constr env evm = subst_globals subst %> desugar_constr env evm in
    let const' =
      Global.lookup_constant const |> transform_constant ident tr_constr
    in
    Globmap.add (ConstRef const) (ConstRef const') subst
  in
  let init () = List.fold_left include_constant Globmap.empty consts in
  ignore
    begin
      qualid_of_reference mod_ref |> Nametab.locate_module |>
      Global.lookup_module |> transform_module_structure ~init ident desugar_constr
    end

(*
 * Unpack sigma types in the functional signature of a constant.
 *
 * This transformation assumes that the input constant was generated by
 * ornamental lifting.
 *)
let do_unpack_constant ident const_ref =
  let env = Global.env () in
  let evm = ref (Evd.from_env env) in
  let term =
    qualid_of_reference const_ref |> Nametab.locate_constant |>
    unpack_constant env evm
  in
  ignore (define_term ident !evm term true)
