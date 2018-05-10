(*
 * Functions to manage the hypotheses of a term
 *)

open Term
open Environ
open Evd

(*
 * Remove the final hypothesis of a lambda
 *)
val remove_final_hypo : types -> types
       
(*
 * Remove any terms from the hypothesis of a lambda
 * that are not referenced in the body, so that the term
 * has only hypotheses that are referenced
 *)
val remove_unused_hypos : types -> types

(*
 * Get the hypotheses that are used in the body
 *)
val get_used_or_p_hypos : (types -> bool) -> types -> types list
                                     
(*
 * Get all hypotheses of a term
 *)
val get_all_hypos : types -> types list    

(*
 * Get n hypothesis of a term
 *)
val get_n_hypos : int -> types -> types list

(*
 * Eta expansion of an application or function
 *)
val expand_eta : env -> evar_map -> types -> types
