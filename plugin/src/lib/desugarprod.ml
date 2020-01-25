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

(* --- Extra utilities --- *)

(*
 * Both types of a prod
 *)
let prod_typs (p : prod_app) =
  p.typ1, p.typ2

(*
 * All types of a nested prod
 *)
let prod_typs_rec typ =
  let rec prod_args typ =
    if is_or_applies prod typ then
      let typ_prod = dest_prod typ in
      let (typ1, typ2) = prod_typs typ_prod in
      typ1 :: prod_args typ2
    else
      [typ]
  in prod_args typ

(*
 * n types of a nested prod
 *)
let prod_typs_rec_n typ n =
  let rec prod_args typ n =
    if n <= 1 then
      [typ]
    else
      if is_or_applies prod typ then
        let typ_prod = dest_prod typ in
        let (typ1, typ2) = prod_typs typ_prod in
        typ1 :: prod_args typ2 (n - 1)
      else
        [typ]
  in prod_args typ n

(*
 * Eta expansion of a nested prod
 *)
let eta_prod_rec trm typ =
  let rec eta trm typ =
    if is_or_applies prod typ then
      let typ_prod = dest_prod typ in
      let (typ1, typ2) = prod_typs typ_prod in
      let (trm1, trm2) = prod_projections_elim typ_prod trm in
      let trm2 = eta trm2 typ2 in
      apply_pair {typ1; typ2; trm1; trm2}
    else
      trm
  in eta trm typ                         
