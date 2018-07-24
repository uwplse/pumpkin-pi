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
 * Initialize a lifting, given (in order):
 * 1) an environment
 * 2) an evar_map
 * 3) promote if promoting, or forget if forgetting
 * 4) forget if promoting, or promote if forgetting
 *)
val initialize_lifting : env -> evar_map -> types -> types -> lifting

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

(* --- Information retrieval --- *)

(* 
 * Given the type of an ornamental promotion function, get the inductive types
 * that the function maps between, including all of their arguments.
 * It is up to the client to adjust the offsets appropriately.
 *)
val ind_of_promotion_type : types -> (types * types)
