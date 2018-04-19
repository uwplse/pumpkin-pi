(*
 * Zooming into environments and reconstructing terms from environments
 *)

open Term
open Environ
open Coqterms
open Debruijn
open Utilities

(* --- Zooming --- *)

(* Zoom into a term *)
let rec zoom_n_prod env npm typ : env * types =
  if npm = 0 then
    (env, typ)
  else
    match kind_of_term typ with
    | Prod (n1, t1, b1) ->
       zoom_n_prod (push_local (n1, t1) env) (npm - 1) b1
    | _ ->
       failwith "more parameters expected"

(* Lambda version *)
let zoom_n_lambda env npm trm : env * types =
  let (env, typ) = zoom_n_prod env npm (lambda_to_prod trm) in
  (env, prod_to_lambda typ)

(* Zoom all the way into a lambda term *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_local (n, t) env) b
  | _ ->
     (env, trm)

(* Zoom all the way into a product type *)
let rec zoom_product_type (env : env) (typ : types) : env * types =
  match kind_of_term typ with
  | Prod (n, t, b) ->
     zoom_product_type (push_local (n, t) env) b
  | _ ->
     (env, typ)

(* Zoom into the environment *)
let zoom_env zoom (env : env) (trm : types) : env =
  fst (zoom env trm)

(* Zoom into the term *)
let zoom_term zoom (env : env) (trm : types) : types =
  snd (zoom env trm)

(* Get the last argument of a sigma *)
let zoom_sig_lambda t =
  last (unfold_args t)

(* Get the very first function from the body of the last argument of a sigma *)
let zoom_sig t =
  let lambda = zoom_sig_lambda t in
  first_fun (zoom_term zoom_lambda_term empty_env lambda)

(* zoom_sig if t actually applies sigT *)
let zoom_if_sig_lambda t =
  if applies sigT t then
    zoom_sig_lambda t
  else
    t

(* zoom if t actually applies sigT *)
let zoom_if_sig t =
  if applies sigT t then
    zoom_sig t
  else
    t

(* --- Reconstruction --- *)

(* Reconstruct a lambda from an environment, but stop when i are left *)
let rec reconstruct_lambda_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n env' (mkLambda (n, t, b)) i

(* Reconstruct a lambda from an environment *)
let reconstruct_lambda (env : env) (b : types) : types =
  reconstruct_lambda_n env b 0

(* Like reconstruct_lambda_n, but first skip j elements *)
let rec reconstruct_lambda_n_skip (env : env) (b : types) (i : int) (j : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    if j <= 0 then
      reconstruct_lambda_n_skip env' (mkLambda (n, t, b)) i j
    else
      reconstruct_lambda_n_skip env' (unshift b) (i - 1) (j - 1)
                

(* Reconstruct a product from an environment, but stop when i are left *)
let rec reconstruct_product_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_product_n env' (mkProd (n, t, b)) i

(* Reconstruct a product from an environment *)
let reconstruct_product (env : env) (b : types) : types =
  reconstruct_product_n env b 0

(* Like reconstruct_product_n, but first skip j elements *)
let rec reconstruct_product_n_skip (env : env) (b : types) (i : int) (j : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    if j <= 0 then
      reconstruct_product_n_skip env' (mkProd (n, t, b)) i j
    else
      reconstruct_product_n_skip env' (unshift b) (i - 1) (j - 1)
