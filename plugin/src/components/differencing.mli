(*
 * Differencing for ornamenting inductive types
 *)

open Constr
open Environ
open Evd
open Names
open Lifting
       
(* --- Ornamental differencing --- *)

(* 
 * Search two inductive types for an ornamental promotion between them
 * Automatically infer the kind of change
 * Automatically infer the index if it is an indexing function
 *)
val search_orn_inductive :
  env ->
  evar_map ->
  Id.t -> (* name to assign an indexer function, if one is found *)
  types -> (* old inductive type *)
  types -> (* new inductive type *)
  promotion (* ornamental prmotion *)

