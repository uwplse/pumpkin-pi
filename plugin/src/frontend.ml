open Constr
open Names
open Utilities
open Coqterms
open Differencing
open Lifting
open Promotions
open Specialization

(* 
 * Identify an algebraic ornament between two types
 * Define the components of the corresponding equivalence
 * (Don't prove section and retraction)
 *)
let find_ornament n d_old d_new =
  let (evd, env) = Pfedit.get_current_context () in
  let trm_o = unwrap_definition env (intern env evd d_old) in
  let trm_n = unwrap_definition env (intern env evd d_new) in
  if isInd trm_o && isInd trm_n then
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env evd idx_n trm_o trm_n in
    Option.iter
      (fun idx ->
        define_term idx_n evd idx;
        Printf.printf "Defined indexing function %s.\n\n" (Id.to_string idx_n))
      orn.indexer;
    define_term n evd orn.promote;
    Printf.printf "Defined promotion %s.\n\n" (Id.to_string n);
    let inv_n = with_suffix n "inv" in
    define_term inv_n evd orn.forget;
    Printf.printf "Defiend forgetful function %s.\n\n" (Id.to_string inv_n)
  else
    failwith "Only inductive types are supported"

(*
 * Lift the supplied function along the supplied ornament
 * Define the lifted version
 *)
let lift_by_ornament n d_orn d_orn_inv d_old =
  let (evd, env) = Pfedit.get_current_context () in
  let c_orn = intern env evd d_orn in
  let c_orn_inv = intern env evd d_orn_inv in
  let c_old = intern env evd d_old in
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let lifted = do_lift_core env evd l c_old in
  define_term n evd lifted;
  Printf.printf "Defined lifted function %s.\n\n" (Id.to_string n);
  try
    declare_lifted evd c_old (make_constant n)
  with _ ->
    Printf.printf "WARNING: Failed to cache lifting."

