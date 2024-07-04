(*
 * Factoring
 *)

open Constr
open Debruijn
open Environ

(* --- Type-level factoring --- *)

(* Deconstruct a product type (A -> B -> ... -> D) into A, B, ..., D *)
let rec factor_product (env: env) (trm : types) : types list =
  match kind trm with
  | Prod (n, t, b) ->
     t :: factor_product env (unshift env b)
  | _ ->
     []
