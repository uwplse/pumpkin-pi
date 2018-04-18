(*
 * Dealing with arguments of applications for indexing inductive types
 *)

open Term
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
 * Unshift all arguments after the location of an argument, since
 * the index is no longer a hypothesis
 *)
val adjust_no_index : int -> types list -> types list

(*
 * Given (in order) an index location, an inductive property, a hypothesis,
 * the type of a constructor body, and a number of arguments to a constructor 
 * left in that body, return the first inductive hypothesis in the body 
 * for which the hypothesis is used to compute the index at the supplied
 * location.
 *
 * The return type is a pair of the index hypothesis location in the inductive
 * type and the inductive hypothesis that first references that hypothesis,
 * or None if no such index exists.
 *)
val index_ih : int -> types -> types -> types -> int -> (types * types) option

(*
 * Returns true if the hypothesis is used to compute the index at the supplied
 * location in some application of the inductive property, and furthermore,
 * is not used to compute any other indices (or parameters). 
 * 
 * This is useful for checking for hypotheses that represent a new index when 
 * searching for ornaments, since the new hypotheses will not be used to
 * compute other indices, since they were not present in the old term
 * and the relationship is an ornamental indexing relationship.
 *)
val computes_only_index :
  env ->
  evar_map ->
  int -> (* index location *)
  types -> (* inductive property *)
  types -> (* hypothesis *)
  types -> (* eliminator type *)
  bool
