(*
 * Datatypes for promotions and lifting
 *)

open Utilities
open Constr
open Evd
open Environ
open Apputils
open Sigmautils
open Typehofs
open Zooming
open Envutils
open Hofimpls
open Caching
open Universes
open Names
open Funutils
open Inference

(* --- Datatypes --- *)

(*
 * An ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, and a function from T2 -> T1.
 *)
type promotion =
  {
    indexer : types option;
    promote : types;
    forget : types;
  }

(*
 * A lifting is an ornamental promotion between types, a direction,
 * and the offset of the index. This is a convenience configuration for
 * lifting functions and proofs, which wraps the promotion with extra
 * useful information.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
    off : int option;
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
 * Given the type of an ornamental promotion function, get the inductive types
 * that the function maps between, including all of their arguments 
 *)
let rec ind_of_promotion_type (typ : types) : types * types =
  match kind typ with
  | Prod (n, t, b) when isProd b ->
     ind_of_promotion_type b
  | Prod (n, t, b) ->
     (t, b)
  | _ ->
     failwith "not an ornamental promotion/forgetful function type"

(* 
 * TODO rename before merging, now
 *)
let ind_of_promotion env sigma trm =
  on_red_type_default (ignore_env ind_of_promotion_type) env sigma trm

(* --- Utilities for initialization --- *)

(*
 * Determine if the direction is forwards or backwards
 * That is, if trm is a promotion or a forgetful function
 * True if forwards, false if backwards
 *)
let direction_cached env sigma from_typ to_typ k : bool =
  match k with
  | Algebraic ->
     let ((i_o, ii_o), _) = destInd from_typ in
     let ((i_n, ii_n), _) = destInd to_typ in
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     let arity_o = arity (type_of_inductive env ii_o m_o) in
     let arity_n = arity (type_of_inductive env ii_n m_n) in
     arity_n > arity_o
  | CurryRecord ->
     not (equal Produtils.prod (first_fun from_typ))

(*
 * Determine if the direction is forwards or backwards
 * That is, if trm is a promotion or a forgetful function
 * True if forwards, false if backwards
 *
 * TODO move is_alg to a config somewhere. Logic here is redundant
 * and also not exactly the same as other places that determine is_alg.
 * What we really want is to cache the user-supplied ornament, I think,
 * and then look it up. Or, remove support for passing orn directly,
 * and add a command to provide/cache your own (probably better) that replaces
 * whatever is last in the cache.
 *
 * TODO redundant comment, code, etc.
 *)
let direction_user_supplied env sigma trm : bool =
  let rec wrapped (from_ind, to_ind) =
    if not (applies sigT from_ind) then
      true
    else
      if not (applies sigT to_ind) then
        false
      else
        let (from_args, to_args) = map_tuple unfold_args (from_ind, to_ind) in
        wrapped (map_tuple last (from_args, to_args))
  in
  let from_typ_app, to_typ_app = ind_of_promotion env sigma trm in
  if applies sigT from_typ_app || applies sigT to_typ_app then
    (* algebraic ornament *)
    wrapped (from_typ_app, to_typ_app)
  else
    (* curry record *)
    not (equal Produtils.prod (first_fun from_typ_app))
        
(* --- Initialization --- *)

(* 
 * Unpack a promotion
 *)
let unpack_promotion env promotion =
  let (env_promotion, body) = zoom_lambda_term env promotion in
  reconstruct_lambda env_promotion (last_arg body)
    
(*
 * Initialize a promotion
 *)
let initialize_promotion env sigma promote forget =
  let promote_unpacked = unpack_promotion env (unwrap_definition env promote) in
  let to_ind = snd (ind_of_promotion env sigma promote_unpacked) in
  let to_args = unfold_args to_ind in
  let to_args_idx = List.mapi (fun i t -> (i, t)) to_args in
  let off, indexer =
    try
      let (off, index) = List.find (fun (_, t) -> contains_term (mkRel 1) t) to_args_idx in
      Some off, Some (first_fun index)
    with _ ->
      None, None
  in (off, { indexer; promote; forget } )

(*
 * Initialize a lifting
 *)
let initialize_lifting env sigma o n =
  let orn_not_supplied = isInd o || isInd n in
  let is_fwd, (promote, forget) =
    if orn_not_supplied then
      (* Cached ornament *)
      let (orn_o, orn_n, k) = lookup_ornament (o, n) in
      let is_fwd = direction_cached env sigma o n k in
      let orns = map_tuple constr_of_global (orn_o, orn_n) in
      is_fwd, orns
    else
      (* User-supplied ornament *)
      let is_fwd = direction_user_supplied env sigma o in
      let orns = map_if reverse (not is_fwd) (o, n) in
      is_fwd, orns
  in
  let (off, orn) = initialize_promotion env sigma promote forget in
  { orn ; is_fwd ; off }
                                
(* --- Directionality --- *)
       
(* 
 * Flip the direction of a lifting
 *)
let flip_dir l = { l with is_fwd = (not l.is_fwd) }

(*
 * Apply a function twice, once in each direction.
 * Compose the result into a tuple.
 *)
let twice_directional f l = map_tuple f (l, flip_dir l)
