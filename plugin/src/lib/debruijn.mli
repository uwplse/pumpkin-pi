(*
 * Debruijn managenent
 *)

open Term
open Environ

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

(* --- Lists --- *)

(*
 * Shifting and unshifting a list 
 *)
val shift_all : types list -> types list
val unshift_all : types list -> types list

(*
 * Shifting and unshifting a list by an amount
 *)
val shift_all_by : int -> types list -> types list
val unshift_all_by : int -> types list -> types list

(* --- Substitutions --- *)

(*
 * Shifting a list of substitutions or its projections
 *)
val shift_subs : (types * types) list -> (types * types) list
val shift_from : (types * types) list -> (types * types) list
val shift_to : (types * types) list -> (types * types) list

(* --- Adjusting to new environments --- *)

(* 
 * Shift a term from the old (first) environment to the new (second) environment
 *)
val shift_to_env : (env * env) -> types -> types
