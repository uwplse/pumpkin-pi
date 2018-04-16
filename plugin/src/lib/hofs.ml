(*
 * Higher-order functions on terms
 *)

open Term
open Environ
open Debruijn
open Coqterms

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env_if p f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if p f d in
  if p env a trm then
    f env a trm
  else
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_let_in (n, e, typ') env) (d a) e in
       mkLetIn (n, trm', typ', e')
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' = Array.map (map_rec env a) args in
       mkApp (fu', args')
    | Case (ci, ct, m, bs) ->
       let ct' = map_rec env a ct in
       let m' = map_rec env a m in
       let bs' = Array.map (map_rec env a) bs in
       mkCase (ci, ct', m', bs')
    | Fix ((is, i), (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       mkFix ((is, i), (ns, ts', ds'))
    | CoFix (i, (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       mkCoFix (i, (ns, ts', ds'))
    | Proj (pr, c) ->
       let c' = map_rec env a c in
       mkProj (pr, c')
    | _ ->
       trm

(*
 * Like map_term_env_if, but just return true if the proposition is satisfied,
 * and false otherwise.
 *
 * We can make this even more general and just take a combinator
 * and a mapping function and so on, in the future.
 *)
let rec exists_subterm_env p d (env : env) (a : 'a) (trm : types) : bool =
  let exists p a = List.exists p (Array.to_list a) in
  let map_rec = exists_subterm_env p d in
  if p env a trm then
    true
  else
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       c' || t'
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       t' || b'
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       t' || b'
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_let_in (n, e, typ) env) (d a) e in
       trm' || typ' || e'
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' = exists (map_rec env a) args in
       fu' || args'
    | Case (ci, ct, m, bs) ->
       let ct' = map_rec env a ct in
       let m' = map_rec env a m in
       let bs' = exists (map_rec env a) bs in
       ct' || m' || bs'
    | Fix ((is, i), (ns, ts, ds)) ->
       let ts' = exists (map_rec env a) ts in
       let ds' = exists (map_rec_env_fix map_rec d env a ns ts) ds in
       ts' || ds'
    | CoFix (i, (ns, ts, ds)) ->
       let ts' = exists (map_rec env a) ts in
       let ds' = exists (map_rec_env_fix map_rec d env a ns ts) ds in
       ts' || ds'
    | Proj (pr, c) ->
       map_rec env a c
    | _ ->
       false

(*
 * Lazy version
 *)
let rec map_term_env_if_lazy p f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if_lazy p f d in
  let trm' =
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_let_in (n, e, typ') env) (d a) e in
       mkLetIn (n, trm', typ', e')
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' = Array.map (map_rec env a) args in
       mkApp (fu', args')
    | Case (ci, ct, m, bs) ->
       let ct' = map_rec env a ct in
       let m' = map_rec env a m in
       let bs' = Array.map (map_rec env a) bs in
       mkCase (ci, ct', m', bs')
    | Fix ((is, i), (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       mkFix ((is, i), (ns, ts', ds'))
    | CoFix (i, (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       mkCoFix (i, (ns, ts', ds'))
    | Proj (pr, c) ->
       let c' = map_rec env a c in
       mkProj (pr, c')
    | _ ->
       trm
  in if p env a trm' then f env a trm' else trm'

(* Locally empty environment *)
let empty = Global.env ()

(* Map_term_env_if with an empty environment *)
let map_term_if p f d =
  map_term_env_if
    (fun _ a t -> p a t)
    (fun _ a t -> f a t)
    d
    empty

(* Lazy version *)
let map_term_if_lazy p f d =
  map_term_env_if_lazy
    (fun _ a t -> p a t)
    (fun _ a t -> f a t)
    d
    empty

(* exists_subterm_env with an empty environment *)
let exists_subterm p d =
  exists_subterm_env
    (fun _ a t -> p a t)
    d
    empty

(* --- Substitution --- *)

(* Map a substitution over a term *)
let all_substs p env (src, dst) trm : types =
  map_term_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs =
  all_substs convertible

(* Same, but eq_constr *)
let all_eq_substs =
  all_substs (fun _ -> eq_constr) empty

(* --- Variations --- *)

(* map env without any a *)
let map_unit_env mapper p f env trm =
  mapper (fun en _ t -> p en t) (fun en _ t -> f en t) (fun _ -> ()) env () trm
         
(* map without any a *)
let map_unit mapper p f trm =
  mapper (fun _ t -> p t) (fun _ t -> f t) (fun _ -> ()) () trm

(* Some simple combinations *)
let map_unit_env_if = map_unit_env map_term_env_if
let map_unit_env_if_lazy = map_unit_env map_term_env_if_lazy
let map_unit_if = map_unit map_term_if
let map_unit_if_lazy = map_unit map_term_if_lazy
