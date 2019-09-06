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
open Stateutils

(* --- Packing--- *)

(*
 * Pack inside of a sigT type
 *)
let pack env off unpacked sigma =
  let sigma, typ = reduce_type env sigma unpacked in
  let index = get_arg off typ in
  let sigma, index_type = infer_type env sigma index in
  let sigma, packer = abstract_arg env sigma off typ in
  sigma, pack_existT {index_type; packer; index; unpacked}        

(* --- Lifting --- *)

(*
 * Lift
 *)
let lift env l trm sigma =
  let sigma, typ_args = non_index_typ_args l.off env sigma trm in
  sigma, mkAppl (lift_to l, snoc trm typ_args)
              
(*
 * Pack arguments and lift
 *)
let pack_lift env l arg sigma =
  let sigma, arg =
    map_backward
      (fun (sigma, t) -> pack env l.off t sigma)
      l
      (sigma, arg)
  in lift env l arg sigma
       
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
  bind
    (bind (fun sigma -> reduce_nf env sigma trm) f)
    (fun x ->
      fold_left_state
        (fun red lifted sigma ->
          all_conv_substs env sigma (lifted, lifted) red)
        x
        (all_recursive_constants env trm))
    
(*
 * Refolding an applied ornament in the forward direction, 
 * when the ornament application produces an existT term.
 *)
let refold_packed l orn env arg app_red sigma =
  let sigma, typ_args = non_index_typ_args l.off env sigma arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let orn_app_red = reduce_stateless reduce_nf env sigma orn_app in
  let app_red_ex = dest_existT app_red in
  let orn_app_red_ex = dest_existT orn_app_red in
  let abstract env sigma = abstract_arg env sigma l.off in
  let sigma, packer = on_red_type_default abstract env sigma orn_app_red_ex.unpacked in
  let index_type = app_red_ex.index_type in
  let arg_sigT = { index_type ; packer } in
  let sigma, arg_indexer = Util.on_snd (project_index arg_sigT) (lift env l arg sigma) in
  let sigma, arg_value = Util.on_snd (project_value arg_sigT) (lift env l arg sigma) in
  let refold_index = all_eq_substs (orn_app_red_ex.index, arg_indexer) in
  let refold_value = all_eq_substs (orn_app_red_ex.unpacked, arg_value) in
  let refolded = refold_index (refold_value app_red_ex.unpacked) in
  pack env l.off refolded sigma
       
(*
 * Refolding an applied ornament in the backwards direction,
 * when the ornament application eliminates over the projections.
 *)
let refold_projected l orn env arg app_red sigma =
  let sigma, typ_args = non_index_typ_args l.off env sigma arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let orn_app_red = reduce_stateless reduce_nf env sigma orn_app in
  let sigma, lifted = lift env l arg sigma in
  sigma, all_eq_substs (orn_app_red, lifted) app_red

(*
 * Top-level refolding
 *)
let refold l env orn trm args sigma =
  let refolder = if l.is_fwd then refold_packed else refold_projected in
  let refold_all = fold_right_state (refolder l orn env) args in
  fold_back_constants env refold_all trm sigma




             

