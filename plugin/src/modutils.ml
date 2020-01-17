open Util
open Names
open Globnames
open Declarations
open Indutils

(*
 * Pull any functor parameters off the module signature, returning the list of
 * functor parameters and the list of module elements (i.e., fields).
 *)
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
 * Define an interactive (i.e., elementwise) module structure, with the
 * functional argument called to populate the module elements.
 *
 * The optional argument specifies functor parameters.
 *)
let declare_module_structure ?(params=[]) ident declare_elements =
  let mod_sign = Vernacexpr.Check [] in
  let mod_path =
    Declaremods.start_module Modintern.interp_module_ast None ident params mod_sign
  in
  Dumpglob.dump_moddef mod_path "mod";
  declare_elements ();
  let mod_path = Declaremods.end_module () in
  Dumpglob.dump_modref mod_path "mod";
  Flags.if_verbose Feedback.msg_info
    Pp.(str "\nModule " ++ Id.print ident ++ str " is defined");
  mod_path

let fold_module_structure_by_elem init fold_mod_elem mod_body =
  let mod_arity, mod_elems = decompose_module_signature mod_body.mod_type in
  assert (List.is_empty mod_arity); (* Functors are not yet supported *)
  List.fold_left (fun a (l, e) -> fold_mod_elem a l e) init mod_elems

(*
 * Fold over the constant/inductive definitions within a module structure,
 * skipping any module (type) components and any unsupported (e.g., mutual)
 * inductive definitions.
 *
 * Elimination schemes (e.g., `Ind_rect`) are filtered out from the definitions.
 *)
let fold_module_structure_by_decl init fold_const fold_ind mod_body =
  let mod_path = mod_body.mod_mp in
  let fold_mod_elem (globset, acc) label mod_elem =
    match mod_elem with
    | SFBconst const_body ->
      let const = Constant.make2 mod_path label in
      if Refset.mem (ConstRef const) globset then
        (globset, acc)
      else
        (globset, fold_const acc const const_body)
    | SFBmind mind_body ->
      check_inductive_supported mind_body;
      let ind_body = mind_body.mind_packets.(0) in
      let ind = (MutInd.make2 mod_path label, 0) in
      let globset' =
        List.map (Indrec.lookup_eliminator ind) ind_body.mind_kelim |>
        List.fold_left (fun gset gref -> Refset.add gref gset) globset
      in
      (globset', fold_ind acc ind (mind_body, ind_body))
    | SFBmodule mod_body ->
      Feedback.msg_warning
        Pp.(str "Skipping nested module structure " ++ Label.print label);
      (globset, acc)
    | SFBmodtype sig_body ->
      Feedback.msg_warning
        Pp.(str "Skipping nested module signature " ++ Label.print label);
      (globset, acc)
  in
  fold_module_structure_by_elem (Refset.empty, init) fold_mod_elem mod_body |> snd

(*
 * Same as `fold_module_structure_by_decl` except a single step function
 * accepting a global reference.
 *)
let fold_module_structure_by_glob init fold_global mod_body =
  fold_module_structure_by_decl
    init
    (fun acc const _ -> fold_global acc (ConstRef const))
    (fun acc ind _ -> fold_global acc (IndRef ind))
    mod_body

(*
 * Same as `fold_module_structure_by_glob` except an implicit unit accumulator.
 *)
let iter_module_structure_by_glob iter_global mod_body =
  fold_module_structure_by_glob () (const iter_global) mod_body
