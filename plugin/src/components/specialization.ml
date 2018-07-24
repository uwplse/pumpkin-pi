(*
 * Specialization component
 *)

open Lifting
open Hofs
open Coqterms
open Utilities
open Indexing
open Abstraction

(* --- Packing--- *)

(*
 * Pack inside of a sigT type
 *)
let pack env evd index_i unpacked =
  let typ = reduce_type env evd unpacked in
  let index = get_arg index_i typ in
  let index_type = infer_type env evd index in
  let packer = abstract_arg env evd index_i typ in
  pack_existT {index_type; packer; index; unpacked}

(* --- Lifting --- *)

(*
 * Lift
 *)
let lift env evd l trm =
  let typ_args = non_index_typ_args l.index_i env evd trm in
  mkAppl (lift_to l, snoc trm typ_args)
              
(*
 * Pack arguments and lift
 *)
let pack_lift env evd l arg =
  lift env evd l (map_backward (pack env evd l.index_i) l arg)
       
(* --- Refolding --- *)

(* 
 * As explained in Section 5.1.2, the implementation uses a refolding
 * algorithm to determine the constructor lifting rules, so that
 * they do not need to depend on ordering information. 
 *)
         
(*
 * Refolding an applied ornament in the forward direction, 
 * when the ornament application produces an existT term.
 *)
let refold_packed l evd orn env arg trm =
  let typ_args = non_index_typ_args l.index_i env evd arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let app_red = reduce_nf env trm in
  let orn_app_red = reduce_nf env orn_app in
  let app_red_ex = dest_existT app_red in
  let orn_app_red_ex = dest_existT orn_app_red in
  let abstract = abstract_arg env evd l.index_i in
  let packer = on_type abstract env evd orn_app_red_ex.unpacked in
  let index_type = app_red_ex.index_type in
  let arg_sigT = { index_type ; packer } in
  let arg_indexer = project_index arg_sigT arg in
  let arg_value = project_value arg_sigT arg in
  let refold_index = all_eq_substs (orn_app_red_ex.index, arg_indexer) in
  let refold_value = all_eq_substs (orn_app_red_ex.unpacked, arg_value) in
  let index = refold_index app_red_ex.index in
  let unpacked = refold_index (refold_value app_red_ex.unpacked) in
  pack_existT { app_red_ex with index; unpacked }

(*
 * Refolding an applied ornament in the backwards direction,
 * when the ornament application eliminates over the projections.
 *)
let refold_projected l evd orn env arg trm =
  let typ_args = non_index_typ_args l.index_i env evd arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let app_red = reduce_nf env trm in
  let orn_app_red = reduce_nf env orn_app in
  all_eq_substs (orn_app_red, arg) app_red

(*
 * Top-level refolding
 *)
let refold l env evd orn trm args =
  let refolder = if l.is_fwd then refold_packed else refold_projected in
  List.fold_right (refolder l evd orn env) args trm




             

