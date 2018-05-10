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
open Printing

(* Remove the final hypothesis of a lambda *)
let rec remove_final_hypo trm =
  match kind_of_term trm with
  | Lambda (n, t, b) when isLambda b ->
     mkLambda (n, t, remove_final_hypo b)
  | Lambda (n, t, b) ->
     unshift b
  | _ ->
     failwith "not a lambda"
       
(*
 * This function removes any terms from the hypothesis of a lambda
 * that are not referenced in the body, so that the term
 * has only hypotheses that are referenced.
 *)
let rec remove_unused_hypos (trm : types) : types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let b' = remove_unused_hypos b in
     if contains_term (mkRel 1) b' then
       mkLambda (n, t, b')
     else
       remove_unused_hypos (unshift b')
  | _ ->
     trm

(*
 * Get the hypotheses that are used in the body, or that match
 * a certain predicate on the type
 *)
let get_used_or_p_hypos (p : types -> bool) (trm : types) : types list =
  let rec get_used trm i =
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       let bs = get_used b (unshift_i i) in
       if p t then
         mkRel i :: bs
       else
         let b' = remove_unused_hypos b in
         if contains_term (mkRel 1) b' then
           mkRel i :: bs
         else
           bs
    | _ ->
       []
  in get_used trm (arity trm)

(*
 * Get all hypotheses of a term
 *)
let get_all_hypos = get_used_or_p_hypos (always_true)

(*
 * Get n hypothesis of a term
 *)
let get_n_hypos nhs trm =
  List.rev (take nhs (List.rev (get_all_hypos trm)))

(* --- Eta expansion --- *)
               
(* Eta expansion of an application or function *)
(* TODO clean *)
let expand_eta (env : env) (evd : evar_map) (trm : types) : types =
  let typ = reduce_type env evd trm in
  let num_args = List.length (unfold_args trm) in
  let curried_args = mk_n_rels (arity typ - num_args) in
  let expanded_app = mkAppl (trm, curried_args) in
  reconstruct_lambda_n
    (zoom_env zoom_product_type empty_env typ)
    (mkAppl (shift_by (List.length curried_args) trm, curried_args))
    (arity typ - List.length curried_args)
