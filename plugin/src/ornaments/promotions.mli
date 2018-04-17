(*
 * Ornamental promotion/forgetful functions
 *)

open Term
open Environ
open Evd

(* 
 * Given the type of an ornamental promotion function, get the inductive types
 * that the function maps between, including all of their arguments 
 *)
val ind_of_promotion_type : types -> (types * types)

(*
 * Given a term that is either a promotion or a forgetful function,
 * return true if it is a promotion, and false if it is a forgetful function
 *)
val direction : env -> evar_map -> types -> bool
