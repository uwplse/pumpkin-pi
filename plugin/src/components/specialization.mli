(*
 * Specialization component for ornamental search
 *)

open Constr
open Environ
open Evd
open Lifting

(*
 * Lift a proof along lifted functions it refers to
 *)
val do_lift_core :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* unlifted function *)
  types (* lifted function *)
