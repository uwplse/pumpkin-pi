(*
 * Debruijn managenent
 *)

open Term

(* --- Numbers --- *)

(*
 * Shifting and unshifting by an amount
 *)
val unshift_i_by : int -> int -> int
val shift_i_by : int -> int -> int

(*
 * Shifting and unshifting
 *)
val unshift_i : int -> int 
val shift_i : int -> int

(* --- Terms --- *)

(*
 * Shifting and unshifting all indices greater than some amount by an amount
 *)
val unshift_local : int -> int -> types -> types
val shift_local : int -> int -> types -> types


(*
 * Shifting and unshifting all indices greater than 0 by an amount
 *)
val unshift_by : int -> types -> types
val shift_by : int -> types -> types

(*
 * Shifting and unshifting all indices greater than 0
 *)
val shift : types -> types
val unshift : types -> types

