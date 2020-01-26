open Constr
open Environ

(* --- Utilities for delta reduction --- *)

(*
 * Delta-reduce until we hit an inductive type, or otherwise return the original
 *)
val try_delta_inductive : env -> constr -> constr
