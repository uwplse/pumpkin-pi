open Constr
open Environ
open Lifting
open Evd

(* --- Automatically generated coherence proof --- *)

(*
 * Prove coherence with the components search finds
 * Return the coherence proof term and its type
 * (The type is nicer than the one Coq infers)
 *)
val prove_coherence : env -> evar_map -> promotion -> (types * types)
