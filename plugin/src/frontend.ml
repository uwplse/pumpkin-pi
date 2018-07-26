open Constr
open Names
open Coqterms
open Lifting
open Caching
open Search
open Lift
       
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
    define_term idx_n evd orn.indexer true;
    Printf.printf "Defined indexing function %s.\n\n" (Id.to_string idx_n);
    define_term n evd orn.promote true;
    Printf.printf "Defined promotion %s.\n\n" (Id.to_string n);
    let inv_n = with_suffix n "inv" in
    define_term inv_n evd orn.forget true;
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
  let l = initialize_lifting env evd c_orn c_orn_inv in
  let lifted = do_lift_core env evd l c_old in
  define_term n evd lifted false;
  try
    declare_lifted evd c_old (make_constant n);
  with _ ->
    Printf.printf "WARNING: Failed to cache lifting."

