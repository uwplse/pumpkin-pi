(*
 * Datatypes for promotions and lifting
 *)

open Constr
open Environ
open Evd
open Caching

(* --- Datatypes --- *)

(*
 * An ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, and a function from T2 -> T1.
 *)
type promotion =
  {
    indexer : types option;
    promote : types;
    forget : types;
    kind : kind_of_orn;
  }

(*
 * A lifting is an ornamental promotion between types, a direction,
 * and the offset of the index if applicable. This is a convenience 
 * configuration for lifting functions and proofs, which wraps the promotion
 * with extra useful information.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
    off : int option;
  }

(* --- Initialization --- *)

(*
 * Initialize a lifting, given (in order):
 * 1) an environment
 * 2) an evar_map
 * 3) the old type or user-supplied ornament function
 * 4) the new type or user-supplied ornament function
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

(* --- Directionality --- *)
       
(* 
 * Flip the direction of a lifting
 *)
val flip_dir : lifting -> lifting

(*
 * Apply a function twice, once in each direction.
 * Compose the result into a tuple.
 *)
val twice_directional : (lifting -> 'a) -> lifting -> ('a * 'a)
