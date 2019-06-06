(*
 * Higher-order functions on terms
 *)

open Constr
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
let rec map_term_env_if p f d env sigma (a : 'a) (trm : types) : evar_map * types =
  let map_rec = map_term_env_if p f d in
  if p env sigma a trm then
    f env sigma a trm
  else
    match kind trm with
    | Cast (c, k, t) ->
       let sigma, c' = map_rec env sigma a c in
       let sigma, t' = map_rec env sigma a t in
       sigma, mkCast (c', k, t')
    | Prod (n, t, b) ->
       let sigma, t' = map_rec env sigma a t in
       let sigma, b' = map_rec (push_local (n, t') env) sigma (d a) b in
       sigma, mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let sigma, t' = map_rec env sigma a t in
       let sigma, b' = map_rec (push_local (n, t') env) (d a) b in
       sigma, mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let sigma, trm' = map_rec env sigma a trm in
       let sigma, typ' = map_rec env sigma a typ in
       let sigma, e' = map_rec (push_let_in (n, e, typ') env) (d a) e in
       sigma, mkLetIn (n, trm', typ', e')
    | App (fu, args) ->
       let sigma, fu' = map_rec env sigma a fu in
       let sigma, args' = map_rec_args map_rec env sigma a args in
       sigma, mkApp (fu', args')
    | Case (ci, ct, m, bs) ->
       let sigma, ct' = map_rec env sigma a ct in
       let sigma, m' = map_rec env sigma a m in
       let sigma, bs' = map_rec_args map_rec env sigma a bs in
       sigma, mkCase (ci, ct', m', bs')
    | Fix ((is, i), (ns, ts, ds)) ->
       let sigma, ts' = map_rec_args map_rec env sigma a ts in
       let sigma, ds' = map_rec_args (map_rec_env_fix map_rec d env sigma a ns ts) env sigma a ds in
       sigma, mkFix ((is, i), (ns, ts', ds'))
    | CoFix (i, (ns, ts, ds)) ->
       let sigma, ts' = map_rec_args map_rec env sigma a ts in
       let sigma, ds' = map_rec_args (map_rec_env_fix map_rec d env sigma a ns ts) env sigma a ds in
       sigma, mkCoFix (i, (ns, ts', ds'))
    | Proj (pr, c) ->
       let sigma, c' = map_rec env sigma a c in
       sigma, mkProj (pr, c')
    | _ ->
       sigma, trm

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
    match kind trm with
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
    match kind trm with
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

(*
 * Old and lazy version
 *)
let rec map_term_env_if_lazy_old p f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if_lazy_old p f d in
  let trm' =
    match kind trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_let_in (n, e, typ) env) (d a) e in
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

                                              
(*
 * Like map_term_env_if, but make a list of subterm results
 *)
let rec map_term_env_if_list p f d (env : env) (a : 'a) (trm : types) : (env * types) list =
  let map_rec = map_term_env_if_list p f d in
  if p env a trm then
    [(env, f env a trm)]
  else
    match kind trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       List.append c' t'
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       List.append t' b'
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       List.append t' b'
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_let_in (n, e, typ) env) (d a) e in
       List.append trm' (List.append typ' e')
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' = Array.map (map_rec env a) args in
       List.append fu' (List.flatten (Array.to_list args'))
    | Case (ci, ct, m, bs) ->
       let ct' = map_rec env a ct in
       let m' = map_rec env a m in
       let bs' = Array.map (map_rec env a) bs in
       List.append ct' (List.append m' (List.flatten (Array.to_list bs')))
    | Fix ((is, i), (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       List.append (List.flatten (Array.to_list ts')) (List.flatten (Array.to_list ds'))
    | CoFix (i, (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       List.append (List.flatten (Array.to_list ts')) (List.flatten (Array.to_list ds'))
    | Proj (pr, c) ->
       map_rec env a c
    | _ ->
       []

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

(* all subterms that match a predicate *)
let all_const_subterms p d a t =
  List.map
    snd
    (map_term_env_if_list
       (fun _ a t -> isConst t && p a t)
       (fun en _ t -> t)
       d
       empty
       a
       t)

(* --- Substitution --- *)

(* Map a substitution over a term *)
let all_substs p env sigma (src, dst) trm : types =
  map_term_env_if
    (fun en si (s, _) t -> p en si s t)
    (fun _ _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    sigma
    (src, dst)
    trm

(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs =
  all_substs (fun en tr convertible

(* Same, but equal *)
let all_eq_substs =
  all_substs (fun _ -> equal) empty

(* --- Containment --- *)
             
(*
 * Check recursively whether a term contains another term
 *)
let contains_term c trm =
  exists_subterm equal shift c trm
                 
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


