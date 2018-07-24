(*
 * Specialization component
 *)

open Constr
open Environ
open Evd
open Lifting

(* --- Packing --- *)

(* Pack the index at the supplied offset *)
val pack : env -> evar_map -> int -> types -> types
       
(* --- Applying promote/forget --- *)

(*
 * Apply promote/forget (forwards/backwards) to a term
 *)
val lift : env -> evar_map -> lifting -> types -> types
              
(*
 * Pack arguments and lift
 *)
val pack_lift : env -> evar_map -> lifting -> types -> types

(* --- Refolding --- *)

(*
 * Apply and refold by an ornament function. This takes, in order:
 * 1) the lifting
 * 2) the environment
 * 3) the evar map
 * 4) the promote/forget function that is applied
 * 5) a term which is that promote/forget function applied to some arguments
 * 6) the inner arguments to refold by
 *)
val refold : lifting -> env -> evar_map -> types -> types -> types list -> types
