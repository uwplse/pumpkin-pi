(*
 * Dealing with arguments of applications for indexing inductive types
 *)

open Term

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
