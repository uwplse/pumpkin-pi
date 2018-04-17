(*
 * Ornamental promotion/forgetful functions
 *)

open Term

(* 
 * Given the type of an ornamental promotion function, get the inductive types
 * that the function maps between, including all of their arguments 
 *)
val ind_of_promotion_type : types -> (types * types)
