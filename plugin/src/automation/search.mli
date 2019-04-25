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

