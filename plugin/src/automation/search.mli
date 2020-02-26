(*
 * Searching for ornamental promotions between inductive types
 *)

open Constr
open Environ
open Evd
open Names
open Promotion
open Stateutils

(* --- Top-level search --- *)

(* 
 * Search for an ornamental promotion between two types
 *)
val search_orn :
  env ->
  evar_map ->
  Id.t option -> (* name to assign the indexer function, if relevant *)
  int option -> (* TODO move me *)
  types -> (* old type *)
  types -> (* new type *)
  promotion state (* ornamental promotion *)

(* 
 * Try to invert a single component of an ornamental promotion isomorphism
 * (Like search, but only in one direction)
 *
 * Exactly one of promote and forget must be present, otherwise this fails
 *)
val invert_orn :
  env ->
  evar_map ->
  Id.t option -> (* name to assign the indexer function, if relevant *)
  int option -> (* TODO move me *)
  types -> (* old type *)
  types -> (* new type *)
  constr option -> (* optional promotion function *)
  constr option -> (* optional forgetful function *)
  promotion state (* ornamental promotion *)
