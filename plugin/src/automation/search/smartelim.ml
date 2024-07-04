open Lifting
open Promotion
open Libnames
open Constr
open Nametab
open Apputils
open Reducers
open Zooming
open Environ
open Envutils
open Debruijn
open Idutils
open Sigmautils
open Names
open Utilities
open Equtils
open Nameutils

(*
 * If the appropriate option is set, DEVOID generates useful "smart eliminators"
 * in addition to the equivalences it discovers. For example, for algebraic
 * ornaments, it generates and automatically lifts a useful eliminator over
 * { a : A & indexer a = i_b } that helps the user combine proofs about A and
 * proofs about the index of a, so that later the user can get proofs about
 * unpacked B.
 *)

(* --- Constants --- *)

let packed_rect () =
  let n = qualid_of_string "Ornamental.Eliminators.packed_rect" in
  mkConst (locate_constant n)

(* --- Procedure --- *)

(*
 * Generate the list of smart eliminators
 *)
let find_smart_elims l env sigma =
  match l.orn.kind with
  | Algebraic (indexer, _) -> 
     (* Eliminate { a : A & indexer a = i_b } *)
     let promote = lift_to l in
     let sigma, elim =
       let sigma, promote_typ = reduce_type env sigma promote in
       let env_a, b_typ = zoom_product_type env promote_typ in
       let sigma, a_typ = reduce_type env_a sigma (mkRel 1) in
       let env_args = pop_rel_context 1 env_a in
       let body =
         let f = packed_rect () in
         let args =
           let (a_typ, b_typ) = map_tuple (unshift env_args) (a_typ, b_typ) in
           let i_b_typ = (dest_sigT b_typ).index_type in
           let a_args = unfold_args a_typ in
           let indexer_app = mkAppl (indexer, a_args) in
           let id_app = mkAppl (id_typ, [a_typ]) in
           let coh_app =
             let push typ = push_local (Anonymous, typ) in
             let env_coh = push (shift env_args a_typ) (push i_b_typ env_args) in
             let eq =
               let a_args = shift_all_by env_coh 2 a_args in
               let at_type = shift_by env_coh 2 i_b_typ in
               let trm1 = mkAppl (indexer, snoc (mkRel 1) a_args) in
               let trm2 = mkRel 2 in
               apply_eq { at_type; trm1; trm2 }
             in
             let body_coh = mkAppl (id_typ, [eq]) in
             reconstruct_lambda_n env_coh body_coh (nb_rel env_args)
           in [a_typ; i_b_typ; indexer_app; id_app; coh_app]
         in mkAppl (f, args)
       in sigma, reconstruct_lambda env_args body
     in
     let sigma, t = chain_reduce reduce_type remove_identities env sigma elim in
     sigma, [(suffix_term_name promote (Id.of_string "_rect"), elim, t)]
  | _ ->
     sigma, []
