(*
 * Specialization component
 *)

open Constr
open Environ
open Evd
open Lifting
open Stateutils
open Reducers
open Sigmautils

(* --- Packing --- *)

(* Pack a term before lifting *)
val pack : env -> lifting -> types -> evar_map -> types state

(* --- Unpacking for unpack ornaments --- *)

val unpack_typ_args : env -> constr -> evar_map -> (constr list) state

(* --- Specialization --- *)

val specialize_using :
  reducer -> env -> constr -> constr list -> evar_map -> constr state

val specialize :
  env -> constr -> constr list -> evar_map -> constr state

val specialize_delta_f :
  env -> constr -> constr list -> evar_map -> constr state

(* --- Applying promote/forget --- *)

(*
 * Apply promote/forget (forwards/backwards) to a term
 *)
val lift :
  env -> lifting -> constr -> types list -> evar_map -> constr state

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
