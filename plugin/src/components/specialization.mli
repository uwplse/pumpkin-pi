(*
 * Specialization component
 *)

open Constr
open Environ
open Evd
open Lifting
open Stateutils

(* --- Packing --- *)

(* Pack the index at the supplied offset *)
val pack : env -> int -> types -> evar_map -> types state

(* --- Applying promote/forget --- *)

(*
 * Apply promote/forget (forwards/backwards) to a term
 *)
val lift : env -> lifting -> types -> evar_map -> types state

(*
 * Pack arguments and lift
 *)
val pack_lift : env -> lifting -> types -> evar_map -> types state

(* --- Refolding --- *)

(*
 * Apply and refold by an ornament function. This takes, in order:
 * 1) the lifting
 * 2) the environment
 * 3) the promote/forget function that is applied
 * 4) a term which is that promote/forget function applied to some arguments
 * 5) the evar map
 * 6) the inner arguments to refold by
 *)
val refold :
  lifting -> env -> types -> types -> types list -> evar_map -> types state
