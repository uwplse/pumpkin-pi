open Constr
open Environ
open Evd
open Lifting
open Stateutils

(* --- Automatically generated unpacked algebraic equivalences --- *)

(*
 * Generate the unpacked algebraic equivalence
 * Do not yet prove section and retraction
 * Return the components of the equivalence
 *)
val unpack_algebraic :
  env ->
  evar_map ->
  lifting ->
  constr -> (* proof of coherence *)
  (constr * constr) -> (* proofs of section and retraction *)
  (constr * constr) (* functions that make up new equivalence *)
