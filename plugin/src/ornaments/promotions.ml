(*
 * Ornamental promotion/forgetful functions
 *)

open Term
open Evd
open Environ
open Coqterms
open Utilities

(* 
 * Given the type of an ornamental promotion function, get the inductive types
 * that the function maps between, including all of their arguments 
 *)
let rec ind_of_promotion_type (typ : types) : types * types =
  match kind_of_term typ with
  | Prod (n, t, b) when isProd b ->
     ind_of_promotion_type b
  | Prod (n, t, b) ->
     (t, b)
  | _ ->
     failwith "not an ornamental promotion/forgetful function type"

(*
 * Determine if the direction is forwards or backwards
 * That is, if trm is a promotion or a forgetful function
 * True if forwards, false if backwards
 *)
let direction (env : env) (evd : evar_map) (trm : types) : bool =
  let rec wrapped (from_ind, to_ind) =
    if not (applies sigT from_ind) then
      true
    else
      if not (applies sigT to_ind) then
        false
      else
        let (from_args, to_args) = map_tuple unfold_args (from_ind, to_ind) in
        wrapped (map_tuple last (from_args, to_args))
  in wrapped (on_type ind_of_promotion_type env evd trm)
