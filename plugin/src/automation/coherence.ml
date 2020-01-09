open Constr
open Utilities
open Zooming
open Lifting
open Typehofs
open Envutils
open Apputils
open Equtils
open Sigmautils

(* --- Automatically generated coherence proof --- *)

(* 
 * Prove coherence with the components search finds
 * Return the coherence proof term and its type
 *)
let prove_coherence env sigma orn =
  match orn.kind with
  | Caching.Algebraic indexer ->
     let promote = lookup_definition env orn.promote in
     let env_coh = zoom_env zoom_lambda_term env promote in
     let a = mkRel 1 in
     let is = on_red_type_default (ignore_env unfold_args) env_coh sigma a in
     let b_sig = mkAppl (orn.promote, snoc a is) in
     let b_sig_typ = on_red_type_default (ignore_env dest_sigT) env_coh sigma b_sig in
     let ib = mkAppl (indexer, snoc a is) in
     let ib_typ = b_sig_typ.index_type in
     let proj_ib = project_index b_sig_typ b_sig in
     let refl = apply_eq_refl { typ = ib_typ; trm = proj_ib } in
     let refl_typ = apply_eq { at_type = ib_typ; trm1 = proj_ib; trm2 = ib } in
     let coh = reconstruct_lambda env_coh refl in
     let coh_typ = reconstruct_product env_coh refl_typ in
     (coh, coh_typ)
  | _ ->
     CErrors.user_err
       (Pp.str "Coherence proofs supported for only algebraic ornaments. Please report an error if you see this message.")
