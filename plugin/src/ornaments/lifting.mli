(*
 * Datatypes for promotions and lifting
 *)

open Constr
open Environ
open Evd

(* --- Datatypes --- *)

(*
 * For now, an ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, a function from T2 -> T1. Later, it will also contain
 * patches and extra premises, and these will be present both in the top-level
 * type and as premises to the functions in both directions.
 *
 * We don't represent ornaments directly, yet, but this may also be useful.
 *)
type promotion =
  {
    index_i : int option;
    indexer : types option;
    promote : types;
    forget : types;
  }

(*
 * A lifting is an ornamental promotion between types, a direction,
 * a hint whether it corresponds to an indexing function for an outer lifting,
 * and an optional indexer for the promoted function.
 *
 * I may add more things here later. This is just a convenient configuration
 * for promoting functions.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
    lifted_indexer : types option;
  }

(* --- Initialization --- *)

(* 
 * Initialize a promotion, given promotion and forgetful functions
 *)
val initialize_promotion : env -> evar_map -> types -> types -> promotion

(*
 * Initialize a lifting, given a promotion and a direction 
 *)
val initialize_lifting : promotion -> bool -> lifting

(* --- Control structures --- *)
    
(*
 * These two functions determine what function to use to go back to
 * an old type or get to a new type when lifting
 *)
val lift_back : lifting -> types
val lift_to : lifting -> types

(* Other control structures *)
val directional : lifting -> 'a -> 'a -> 'a
val map_directional : ('a -> 'b) -> ('a -> 'b) -> lifting -> 'a -> 'b
val map_forward : ('a -> 'a) -> lifting -> 'a -> 'a
val map_backward : ('a -> 'a) -> lifting -> 'a -> 'a

(* --- Database for higher lifting --- *)

(*
 * Register a lifting to the database
 *)
val declare_lifted : evar_map -> types -> types -> unit

(*
 * Search the database for a lifting (return the reduced version if it exists)
 *)                                       
val search_lifted : env -> types -> types option
