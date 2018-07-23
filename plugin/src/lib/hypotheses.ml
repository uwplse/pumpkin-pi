(*
 * Functions to manage the hypotheses of a term
 *)

open Term
open Hofs
open Debruijn
open Utilities
open Coqterms
open Environ
open Evd
open Zooming

(* --- Eta expansion --- *)
               
(* Eta expansion of an application or function *)
let expand_eta (env : env) (evd : evar_map) (trm : types) : types =
  let typ = reduce_type env evd trm in
  let num_args = List.length (unfold_args trm) in
  let curried_args = mk_n_rels (arity typ - num_args) in
  let expanded_app = mkAppl (trm, curried_args) in
  reconstruct_lambda_n
    (zoom_env zoom_product_type empty_env typ)
    (mkAppl (shift_by (List.length curried_args) trm, curried_args))
    (arity typ - List.length curried_args)
