(*
 * A generalized version of the factoring component from PUMPKIN PATCH
 *)

open Term
open Environ
open Printing
open Coqterms
open Evd
open Names
open Debruijn
open Zooming
open Hofs
open Lifting
open Utilities

(* --- Type-level factoring --- *)

(* Deconstruct a product type (A -> B -> ... -> D) into A, B, ..., D *)
let rec factor_product (trm : types) : types list =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     t :: factor_product (unshift b)
  | _ ->
     []
