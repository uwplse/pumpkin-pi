(*
 * Dealing with arguments of applications for indexing inductive types
 *)

open Constr
open Environ
open Evd

(* --- Generic functions --- *)

(*
 * Insert a value into a list at a given index location
 *)
val insert_index : int -> 'a -> 'a list -> 'a list

(*
 * Remove a value from a list at a given index location
 *)
val remove_index : int -> 'a list -> 'a list

(*
 * Replace the value at a location with the supplied value
 *)
val reindex : int -> 'a -> 'a list -> 'a list

(* --- Managing inductive property arguments --- *)

(*
 * Apply the term to a dummy index, when we would like the other arguments,
 * but we are not sure if the term is a lambda or curried
 *)
val dummy_index : env -> types -> types
                           
(*
 * Reindex the arguments of an application using a reindexer
 *)
val reindex_app : (types list -> types list) -> types -> types
                                                           
(*
 * Reindex the body of a lambda
 *)
val reindex_body : (types -> types) -> types -> types

(*
 * Unshift all arguments after the location of an argument, since
 * the index is no longer a hypothesis
 *)
val adjust_no_index : int -> types list -> types list

(*
 * Returns true if the hypothesis is used to compute the index at the supplied
 * location in some application of the inductive property in an inductive
 * hypothesis of the supplied eliminator type.
 * 
 * This is useful for checking for hypotheses that represent a new index when 
 * searching for ornaments.
 *)
val computes_ih_index :
  int -> (* index location *)
  types -> (* inductive property *)
  types -> (* hypothesis *)
  types -> (* eliminator type *)
  bool

(* --- Getting arguments to indexed types --- *)

(*
 * Given a type we are promoting to/forgetting from,
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
val non_index_args : int -> env -> types -> types list

(*
 * Given a term with the type we are promoting to/forgetting from,
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
val non_index_typ_args : int -> env -> evar_map -> types -> types list
