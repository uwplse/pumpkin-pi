open Names (* TODO clean *)
open Constr
open Environ
open Coqterms
open Utilities
open Debruijn
open Indexing
open Hofs
open Factoring
open Zooming
open Abstraction
open Lifting
open Declarations
open Util
open Differencing
open Hypotheses (* TODO same *)
open Specialization (* TODO same *)

(* --- Automatically generated coherence proof --- *)

(* 
 * Prove coherence with the components search finds
 * Return the coherence proof term and its type
 *)
let prove_coherence env evd orn =
  let env_coh = zoom_env zoom_lambda_term env orn.promote in
  let a = mkRel 1 in
  let is = on_type unfold_args env_coh evd a in
  let b_sig = mkAppl (orn.promote, snoc a is) in
  let b_sig_typ = reduce_type env_coh evd b_sig in
  let ib = mkAppl (orn.indexer, snoc a is) in
  let ib_typ = reduce_type env_coh evd ib in
  let packer = (dest_sigT b_sig_typ).packer in
  let proj_ib = project_index { index_type = ib_typ; packer } b_sig in
  let refl = apply_eq_refl { typ = ib_typ; trm = proj_ib } in
  let refl_typ = apply_eq { at_type = ib_typ; trm1 = ib; trm2 = proj_ib } in
  let coh = reconstruct_lambda env_coh refl in
  let coh_typ = reconstruct_product env_coh refl_typ in
  (coh, coh_typ)
