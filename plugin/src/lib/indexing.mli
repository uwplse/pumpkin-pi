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
