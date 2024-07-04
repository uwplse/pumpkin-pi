(*
 * Datatypes for promotions and lifting
 *)

open Utilities
open Constr
open Apputils
open Sigmautils
open Typehofs
open Zooming
open Envutils
open Hofimpls
open Caching
open Inference
open Indexing
open Ornerrors
open Stateutils
open Promotion
open Reducers
open Equtils
open Funutils
open Hypotheses
open Unificationutils

(* --- Datatypes --- *)

(*
 * A lifting is an ornamental promotion between types and a direction,
 * This is a convenience configuration for lifting functions and proofs,
 * which wraps the promotion with extra useful information.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
  }

(* --- Control structures --- *)
    
(*
 * These two functions determine what function to use to go back to
 * an old type or get to a new type when lifting
 *)
let lift_back (l : lifting) = if l.is_fwd then l.orn.forget else l.orn.promote
let lift_to (l : lifting) = if l.is_fwd then l.orn.promote else l.orn.forget

(* Other control structures *)
let directional l a b = if l.is_fwd then a else b
let map_directional f g l x = map_if_else f g l.is_fwd x
let map_forward f l x = map_if f l.is_fwd x
let map_backward f l x = map_if f (not l.is_fwd) x
               
(* --- Information retrieval --- *)

(* 
 * Given the type of an ornamental promotion function, get the types
 * that the function maps between, including all of their arguments 
 *)
let rec promotion_type_to_types (typ : types) : types * types =
  match kind typ with
  | Prod (n, t, b) when isProd b ->
     promotion_type_to_types b
  | Prod (n, t, b) ->
     (t, b)
  | _ ->
     failwith "not an ornamental promotion/forgetful function type"

(* 
 * Same, but at the term level
 *)
let promotion_term_to_types env sigma trm =
  on_red_type_default (ignore_env promotion_type_to_types) env sigma trm

(*
 * Determine whether a type is the type we are ornamenting from
 * (A in forward direction, B in backward direction) using unification.
 * We optimize this in liftconfig.ml depending on the kind of ornament.
 *)
let e_is_from env goal_typ typ sigma =
  try
    let nargs = arity goal_typ in
    let sigma, eargs = mk_n_evars nargs env sigma in
    let sigma, typ_app = reduce_term env sigma (mkAppl (goal_typ, eargs)) in
    let sigma, unifies = unify env typ typ_app sigma in
    if unifies then
      sigma, Some eargs
    else
      sigma, None
  with _ ->
    sigma, None

(* --- Utilities for initialization --- *)
                         
(*
 * Determine if the direction is forwards or backwards
 * That is, if trm is a promotion or a forgetful function
 * True if forwards, false if backwards
 *)
let direction_cached env from_typ promote k sigma : bool state =
  let sigma, promote_typ = reduce_type env sigma promote in
  let promote_env = zoom_env zoom_product_type env promote_typ in
  let sigma, promote_typ = infer_type promote_env sigma (mkRel 1) in
  if is_or_applies from_typ promote_typ then
    sigma, true
  else
    let sigma, from_typ = expand_eta promote_env sigma from_typ in
    Util.on_snd
      Option.has_some
      (e_is_from promote_env from_typ promote_typ sigma)

(* 
 * Unpack a promotion
 *)
let unpack_promotion env promotion =
  let (env_promotion, body) = zoom_lambda_term env promotion in
  reconstruct_lambda env_promotion (last_arg body)

(*
 * Get the direction for an uncached ornament.
 *)
let get_direction (from_typ_app, to_typ_app) orn_kind =
  match orn_kind with
  | Algebraic _ ->
     let rec get_direction_algebraic (from_ind, to_ind) =
       if not (applies sigT from_ind) then
         true
       else
         if not (applies sigT to_ind) then
           false
         else
           let (from_args, to_args) = map_tuple unfold_args (from_ind, to_ind) in
           get_direction_algebraic (map_tuple last (from_args, to_args))
     in get_direction_algebraic (from_typ_app, to_typ_app)
  | CurryRecord ->
     not (equal Produtils.prod (first_fun from_typ_app))
  | SwapConstruct _ ->
     (* just set forward to be the initial direction *)
     true
  | UnpackSigma ->
     equal sigT (first_fun from_typ_app)
  | _ ->
     failwith "not yet supported"

(*
 * For an uncached ornament, get the kind and its direction
 *)
let get_kind_of_ornament env typs (o, n) is_custom sigma =
  if is_custom then
    sigma, (true, Custom typs)
  else
    let (from_typ_app, to_typ_app) = promotion_term_to_types env sigma o in
    let sigma, prelim_kind =
      if applies sigT from_typ_app || applies sigT to_typ_app then
        let s = if applies sigT from_typ_app then from_typ_app else to_typ_app in
        let packer = (dest_sigT s).packer in
        let env_b, packer_b = zoom_lambda_term env packer in
        let sigma, packer_b = reduce_nf env_b sigma packer_b in
        if is_or_applies eq packer_b then
          sigma, UnpackSigma
        else
          sigma, Algebraic (mkRel 1, 0)
      else if isInd (first_fun from_typ_app) && isInd (first_fun to_typ_app) then
        sigma, SwapConstruct []
      else
        sigma, CurryRecord
    in
    match prelim_kind with
    | Algebraic _ ->
       let is_fwd = get_direction (from_typ_app, to_typ_app) prelim_kind in
       let (promote, _) = map_if reverse (not is_fwd) (o, n) in
       let promote_unpacked = unpack_promotion env (unwrap_definition env promote) in
       let to_ind = snd (promotion_term_to_types env sigma promote_unpacked) in
       let to_args = unfold_args to_ind in
       let to_args_idx = List.mapi (fun i t -> (i, t)) to_args in
       let (o, i) = List.find (fun (_, t) -> contains_term env (mkRel 1) t) to_args_idx in
       let indexer = first_fun i in
       sigma, (is_fwd, Algebraic (indexer, o))
    | SwapConstruct _ ->
       let a = first_fun from_typ_app in
       let b = first_fun to_typ_app in
       let sigma, swap_map_cs = swap_map_of_promote_or_forget env a b (Some o) None sigma in
       let swap_map =
         List.map
           (fun (((_, i), _), (((_, j), _))) -> i, j)
           swap_map_cs
       in sigma, (true, SwapConstruct swap_map)
    | UnpackSigma | CurryRecord ->
       let is_fwd = get_direction (from_typ_app, to_typ_app) prelim_kind in
       sigma, (is_fwd, prelim_kind)
    | _ ->
       failwith "Not yet supported"

(* --- Directionality --- *)
       
(* 
 * Flip the direction of a lifting
 *)
let flip_dir l =
  let is_fwd = not l.is_fwd in
  let orn =
    match l.orn.kind with
    | SwapConstruct swaps ->
       { l.orn with kind = SwapConstruct (List.map reverse swaps) }
    | _ ->
       l.orn
  in { orn; is_fwd }

(*
 * Apply a function twice, once in each direction.
 * Compose the result into a tuple.
 *)
let twice_directional f l = map_tuple f (l, flip_dir l)

(* --- Initialization --- *)

(*
 * Initialize a lifting for a cached ornament
 *)
let initialize_lifting_cached env sigma o n =
  let sigma, (is_fwd, (promote, forget), kind) =
    let (promote, forget, k) =
      try
        Option.get (lookup_ornament (o, n))
      with _ ->
        failwith "Cannot find cached ornament! Please report a bug in DEVOID"
    in
    let sigma, is_fwd = direction_cached env o promote k sigma in
    sigma, (is_fwd, (promote, forget), k)
  in
  let orn = { promote; forget; kind } in
  let lifting = { orn ; is_fwd = true } in
  if is_fwd then
    sigma, lifting
  else
    sigma, flip_dir lifting

(*
 * Initialize a lifting for a user-provided ornament
 *)
let initialize_lifting_provided env sigma typs funs is_custom =
  let sigma, (is_fwd, (promote, forget), kind) =
    let sigma, (is_fwd, k) = get_kind_of_ornament env typs funs is_custom sigma in
    let orns = map_if reverse (not is_fwd) funs in
    sigma, (is_fwd, orns, k)
  in
  let orn = { promote; forget; kind } in
  sigma, { orn ; is_fwd }

(* --- Indexing for algebraic ornaments --- *)

let index l =
  match l.orn.kind with
  | Algebraic (_, off) ->
     insert_index off
  | _ ->
     raise NotAlgebraic

let deindex l =
  match l.orn.kind with
  | Algebraic (_, off) ->
     remove_index off
  | _ ->
     raise NotAlgebraic
