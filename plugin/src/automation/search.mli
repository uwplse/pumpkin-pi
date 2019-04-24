(*
 * Searching for ornamental promotions between inductive types
 *)

open Constr
open Environ
open Evd
open Names
open Lifting

(* --- Top-level search --- *)

(* 
 * Search two inductive types for an ornamental promotion between them
 * Automatically infer the kind of change
 * Automatically infer the new index
 *)
val search_orn_inductive :
  env ->
  evar_map ->
  Id.t -> (* name to assign the indexer function *)
  types -> (* old inductive type *)
  types -> (* new inductive type *)
  promotion (* ornamental promotion *)

(* --- Automatically generated proofs about promotions search discovers --- *)

(*
 * Prove coherence with the components search finds
 * Return the coherence proof term and its type
 *)
val prove_coherence : env -> evar_map -> promotion -> (types * types)

(*
 * TODO explain
 * TODO clean inputs
 * Return section and retraction (TODO wrap in something)
 *)
val prove_equivalence : Id.t -> Id.t -> env -> evar_map -> lifting -> (types * types)
