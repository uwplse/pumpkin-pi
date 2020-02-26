(*
 * Datatypes for promotions and lifting
 *)

open Constr
open Environ
open Evd
open Promotion
open Stateutils

(* --- Datatypes --- *)

(*
 * A lifting is an ornamental promotion between types and a direction,
 * This is a convenience configuration for lifting functions and proofs,
 * which wraps the promotion with extra useful information.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
  }

(* --- Initialization --- *)

(*
 * Initialize a lifting for a cached ornament, given (in order):
 * 1) an environment
 * 2) an evar_map
 * 3) the old type
 * 4) the new type
 *)
val initialize_lifting_cached :
  env -> evar_map -> types -> types -> lifting state

(*
 * Initialize a lifting for a user-supplied ornament, given (in order):
 * 1) an environment
 * 2) an evar_map
 * 3) the old user-supplied ornament function
 * 4) the new user-supplied ornament function
 *)
val initialize_lifting_provided :
  env -> evar_map -> types -> types -> lifting state

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
 * Given the type of an ornamental promotion function, get the types
 * that the function maps between, including all of their arguments.
 * It is up to the client to adjust the offsets appropriately.
 *)
val promotion_type_to_types : types -> (types * types)

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

(* --- Indexing for algebraic ornaments --- *)

(*
 * Insert/remove the index at the appropriate offset.
 * Raise NotAlgebraic if not an algebraic ornament.
 *)                                                    
val index : lifting -> constr -> constr list -> constr list
val deindex : lifting -> constr list -> constr list

