(*
 * A generalized version of the factoring component from PUMPKIN PATCH
 *)

open Term
open Environ
open Evd
open Lifting

(* --- Type-level factoring --- *)

val factor_product : types -> types list
