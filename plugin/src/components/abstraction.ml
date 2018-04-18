(*
 * Abstraction specific to ornamental search
 *)

open Term
open Environ
open Debruijn
open Coqterms
open Indexing

(* 
 * Given an application and the index of the argument, abstract by the argument
 *)
let abstract_arg env evd i typ =
  let arg = get_arg i typ in
  let arg_typ = reduce_type env evd arg in
  let args = reindex i (mkRel 1) (shift_all (unfold_args typ)) in
  mkLambda (Anonymous, arg_typ, mkAppl (first_fun typ, args))
