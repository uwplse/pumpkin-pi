(*
 * Specialization component
 *)

open Lifting
open Hofs
open Substitution
open Utilities
open Indexing
open Abstraction
open Constr
open Inference
open Typehofs
open Reducers
open Apputils
open Sigmautils
open Envutils

(* --- Packing--- *)

(*
 * Pack inside of a sigT type
 *)
let pack env evd off unpacked =
  let typ = reduce_type env evd unpacked in
  let index = get_arg off typ in
  let index_type = infer_type env evd index in
  let packer = abstract_arg env evd off typ in
  pack_existT {index_type; packer; index; unpacked}        

(* --- Lifting --- *)

(*
 * Lift
 *)
let lift env evd l trm =
  let typ_args = non_index_typ_args l.off env evd trm in
  mkAppl (lift_to l, snoc trm typ_args)
              
(*
 * Pack arguments and lift
 *)
let pack_lift env evd l arg =
  lift env evd l (map_backward (pack env evd l.off) l arg)
       
(* --- Refolding --- *)

(* 
 * The implementation uses a refolding
 * algorithm to determine the constructor lifting rules, so that
 * they do not need to depend on ordering information. 
 *)

(*
 * Get all recursive constants
 *)
let rec all_recursive_constants env trm =
  let consts = all_const_subterms (fun _ _ -> true) (fun u -> u) () trm in
  let non_axioms =
    List.map
      Option.get
      (List.filter
         (Option.has_some)
         (List.map
            (fun c ->
              try
                let def = unwrap_definition env c in
                if not (equal def c || isInd def) then
                  Some (c, def)
                else
                  None
              with _ ->
                None)
            consts))
  in
  let non_axiom_consts = List.map fst non_axioms in
  let defs = List.map snd non_axioms in
  unique
    equal
    (List.append
       non_axiom_consts
       (List.flatten (List.map (all_recursive_constants env) defs)))

(*
 * Fold back constants after applying a function to the normalized form
 * Makes the produced lifted constructors dramatically nicer and faster
 * when they refer to functions
 *)
let fold_back_constants env f trm =
  List.fold_left
    (fun red lifted ->
      all_conv_substs env Evd.empty (lifted, lifted) red)
    (f (reduce_nf env Evd.empty trm))
    (all_recursive_constants env trm)
         
(*
 * Refolding an applied ornament in the forward direction, 
 * when the ornament application produces an existT term.
 *)
let refold_packed l evd orn env arg app_red =
  let typ_args = non_index_typ_args l.off env evd arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let orn_app_red = reduce_nf env Evd.empty orn_app in
  let app_red_ex = dest_existT app_red in
  let orn_app_red_ex = dest_existT orn_app_red in
  let abstract = abstract_arg env evd l.off in
  let packer = on_type abstract env evd orn_app_red_ex.unpacked in
  let index_type = app_red_ex.index_type in
  let arg_sigT = { index_type ; packer } in
  let arg_indexer = project_index arg_sigT (lift env evd l arg) in
  let arg_value = project_value arg_sigT (lift env evd l arg) in
  let refold_index = all_eq_substs (orn_app_red_ex.index, arg_indexer) in
  let refold_value = all_eq_substs (orn_app_red_ex.unpacked, arg_value) in
  let refolded = refold_index (refold_value app_red_ex.unpacked) in
  pack env evd l.off refolded
       
(*
 * Refolding an applied ornament in the backwards direction,
 * when the ornament application eliminates over the projections.
 *)
let refold_projected l evd orn env arg app_red =
  let typ_args = non_index_typ_args l.off env evd arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let orn_app_red = reduce_nf env Evd.empty orn_app in
  all_eq_substs (orn_app_red, lift env evd l arg) app_red

(*
 * Top-level refolding
 *)
let refold l env evd orn trm args =
  let refolder = if l.is_fwd then refold_packed else refold_projected in
  let refold_all = List.fold_right (refolder l evd orn env) args in
  fold_back_constants env refold_all trm




             

