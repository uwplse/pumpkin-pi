(*
 * Searching for ornamental promotions between inductive types
 *)

open Constr
open Environ
open Evd
open Names

(* --- Differencing terms --- *)

(* Check if two terms have the same type, ignoring universe inconsinstency *)
val same_type : env -> evar_map -> (env * types) -> (env * types) -> bool

(* --- Differencing inductive types --- *)

(* Check if two terms are the same modulo an indexing of an inductive type *)
val same_mod_indexing : env -> types -> (types * types) -> (types * types) -> bool

(* --- Differencing for new indices --- *)
       
(*
 * Given an environment and two eliminators, find the new index location
 * and type using the algorithm that handles ambiguity. 
 * Leave offsets to the client.
 *)
val new_index_type : env -> types -> types -> int * types

(*
 * Given an environment, a number of parameters, and two inductive types, 
 * find the new index location and type using the simple heuristic that 
 * doesn't handle ambiguity.
 * Leave offsets to the client.
 *)
val new_index_type_simple : env -> int -> inductive -> inductive -> (int * types) option
                                                                                (*
 * Given an old and new application of a motive, find the new index.
 *)
val get_new_index : int -> types -> types -> types -> types
