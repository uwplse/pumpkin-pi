(*
 * These are the produtils from the library, but extended to automatically
 * also preprocess rather than produce terms with match statements
 *)

open Constr
open Envutils
open Apputils
open Nametab
open Libnames
open Produtils

(* --- Constants --- *)

let prod : types = prod
let pair : constr = pair
let prod_rect : constr = prod_rect

(*
 * Override fst and snd
 *)
let fst_elim () : constr =
  mkConst (locate_constant (qualid_of_string "Ornamental.Prod.fst"))

(* Second projection *)
let snd_elim () : constr =
  mkConst (locate_constant (qualid_of_string "Ornamental.Prod.snd"))

(* --- Representations --- *)

let apply_pair = apply_pair
let dest_pair = dest_pair
let apply_prod = apply_prod
let dest_prod = dest_prod
let elim_prod = elim_prod
let dest_prod_elim = dest_prod_elim

(*
 * First projection of a prod
 *)
let prod_fst_elim (app : prod_app) trm =
  mkAppl (fst_elim (), Produtils.[app.typ1; app.typ2; trm])

(*
 * Second projection of a prod
 *)
let prod_snd_elim (app : prod_app) trm =
  mkAppl (snd_elim (), Produtils.[app.typ1; app.typ2; trm])

(*
 * Both projections of a prod
 *)
let prod_projections_elim (app : prod_app) trm =
  (prod_fst_elim app trm, prod_snd_elim app trm)
