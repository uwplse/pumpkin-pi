(*
 * Basic utilities for collections, optionals, and so on
 *)

(* --- Optionals --- *)

(*
 * Map a function on an optional, and return a default value if it's none
 * This should be in the standard library, but for some reason locally is not
 *)
val map_default : ('a -> 'b) -> 'b -> 'a option -> 'b

(* --- Lists --- *)
                                                     
val last : 'a list -> 'a
val snoc : 'a -> 'a list -> 'a list
val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list

(*
 * Take n elements of a list
 *)
val take : int -> 'a list -> 'a list

(*
 * Take all but n elements of a list
 *)
val take_except : int -> 'a list -> 'a list

(*
 * Split a list l into (l1, l2) where |l1| = n and |l2| = |l| - n
 *)
val take_split : int -> 'a list -> ('a list * 'a list)
                                     
(*
 * [min, max)
 *)
val range : int -> int -> int list

(*
 * [1, max]
 *)
val from_one_to : int -> int list

(* --- Tuples --- *)

val map_tuple : ('a -> 'b) -> ('a * 'a) -> ('b * 'b)
val twice : ('a -> 'a -> bool -> 'b) -> 'a -> 'a -> ('b * 'b)
val reverse: ('a * 'b) -> ('b * 'a)

(* --- Propositions --- *)

val always_true : 'a -> bool
val and_p : ('a -> bool) -> 'a -> 'a -> bool
