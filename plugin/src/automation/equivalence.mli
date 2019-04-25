open Constr
open Environ
open Evd
open Lifting

(* --- Automatically generated equivalence proofs about search components --- *)

(*
 * Prove section and retraction
 * Return the section term and the retraction term
 * (Don't return the types, since Coq can infer them without issue)
 *)
val prove_equivalence : env -> evar_map -> lifting -> (types * types)
