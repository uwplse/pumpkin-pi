(*
 * Searching for ornamental promotions between inductive types
 *)

open Constr
open Environ
open Evd
open Names
open Lifting
open Stateutils

(* --- Top-level search --- *)

(* 
 * Search two types for an ornamental promotion between them
 * Automatically infer the kind of change
 * Automatically infer the new index
 *)
val search_orn :
  env ->
  evar_map ->
  Id.t option -> (* name to assign the indexer function, if relevant *)
  types -> (* old type *)
  types -> (* new type *)
  promotion state (* ornamental promotion *)

