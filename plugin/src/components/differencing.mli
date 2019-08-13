(*
 * Differencing component
 *)

open Constr
open Environ
open Evd
open Names

(* --- Differencing terms --- *)

(* Check if two terms have the same type under some set of constraints *)
val same_type :
  env -> evar_map -> (env * types) -> (env * types) -> evar_map * bool

(* --- Differencing inductive types --- *)

(* Check if two terms are the same modulo an indexing of an inductive type *)
val same_mod_indexing :
  env -> evar_map -> types -> (types * types) -> (types * types) -> evar_map * bool

(* --- Differencing for new indices --- *)
       
(*
 * Given an environment and two eliminators, find the new index location
 * and type using the algorithm that handles ambiguity. 
 * Leave offsets to the client.
 *)
val new_index_type : env -> evar_map -> types -> types -> evar_map * (int * types)

(*
 * Given an environment and two inductive types, 
 * find the new index location and type using the simple heuristic that 
 * doesn't handle ambiguity.
 * Leave offsets to the client.
 *)
val new_index_type_simple : env -> evar_map -> inductive -> inductive -> (evar_map * (int * types)) option

