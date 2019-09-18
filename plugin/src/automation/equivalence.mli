open Constr
open Names
open Environ
open Evd
open Lifting
open Stateutils

(* --- Automatically generated equivalence proofs about search components --- *)

(*
 * Prove section and retraction
 * Return the section term and the retraction term
 * (Don't return the types, since Coq can infer them without issue)
 *)
val prove_equivalence : env -> evar_map -> lifting -> (types * types)

type pre_adjoint = {
  orn : lifting;
  sect : Constant.t;
  retr0 : Constant.t
}

(*
 * Augment the initial retraction proof in order to prove adjunction.
 *
 * The generic proof of adjunction from the HoTT book relies critically on this
 * step; wrapping the proof term for retraction in a clever way (formalized in
 * `fg_id'`) makes a later equality of equality proofs true definitionally.
 *)
val adjointify_retraction : env -> pre_adjoint -> evar_map -> constr state

(*
 * Prove adjunction.
 *)
val prove_adjunction : env -> pre_adjoint -> evar_map -> constr state
