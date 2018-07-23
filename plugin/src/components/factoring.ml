(*
 * Factoring
 *)

open Constr
open Debruijn

(* --- Type-level factoring --- *)

(* Deconstruct a product type (A -> B -> ... -> D) into A, B, ..., D *)
let rec factor_product (trm : types) : types list =
  match kind trm with
  | Prod (n, t, b) ->
     t :: factor_product (unshift b)
  | _ ->
     []
