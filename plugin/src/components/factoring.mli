(*
 * Factoring
 *)

open Constr
open Environ

(* --- Type-level factoring --- *)

val factor_product : env -> types -> types list
