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
    off : int;
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

let ind_of_promotion env sigma trm =
  on_red_type_default (ignore_env ind_of_promotion_type) env sigma trm

(* --- Utilities for initialization --- *)

(*
 * Determine if the direction is forwards or backwards
 * That is, if trm is a promotion or a forgetful function
 * True if forwards, false if backwards
 *)
let direction (env : env) (sigma : evar_map) (trm : types) : bool =
  let rec wrapped (from_ind, to_ind) =
    if not (applies sigT from_ind) then
      true
    else
      if not (applies sigT to_ind) then
        false
      else
        let (from_args, to_args) = map_tuple unfold_args (from_ind, to_ind) in
        wrapped (map_tuple last (from_args, to_args))
  in wrapped (ind_of_promotion env sigma trm)

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
  let (off, index) = List.find (fun (_, t) -> contains_term (mkRel 1) t) to_args_idx in
  let indexer = Some (first_fun index) in
  (off, { indexer; promote; forget } )

(*
 * Initialize a lifting
 *)
let initialize_lifting env sigma c_orn c_orn_inv =
  let is_fwd = direction env sigma c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
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
