(*
 * Specialization component for ornamental search
 *)

open Term
open Environ
open Zooming
open Lifting
open Hofs
open Coqterms
open Debruijn
open Utilities
open Indexing
open Promotions
open Printing

(* --- Application of ornaments before meta-reduction --- *)
              
(*
 * Substitute the ornamented type in the hypotheses.
 * Return both the term with ornamented hypotheses and the number
 * of substitutions that occurred.
 *)
let sub_in_hypos l env from_ind to_ind hypos =
  map_unit_env_if_lazy
    (fun env trm ->
      match kind_of_term trm with
      | Lambda (_, t, _) ->
         is_or_applies from_ind (zoom_if_sig (reduce_nf env t))
      | _ ->
         false)
    (fun env trm ->
      let (n, t, b) = destLambda trm in
      let t_ind = reduce_term env (mkAppl (to_ind, unfold_args t)) in
      mkLambda (n, t_ind, b))
    env
    hypos

(* Apply the promotion/forgetful function to the arguments *)
let ornament_args env evd from_ind l trm =
  let rec ornament_arg env i typ =
    match kind_of_term typ with
    | Prod (n, t, b) ->
       let ornament_b = ornament_arg (push_local (n, t) env) (unshift_i i) b in
       if is_or_applies from_ind (zoom_if_sig (reduce_nf env t)) then
         let t_args = unfold_args (shift_by i t) in
         mkAppl (lift_back l, snoc (mkRel i) t_args) :: ornament_b
       else
         mkRel i :: ornament_b
    | _ ->
       []
  in mkAppl (trm, on_type (fun t -> ornament_arg env (arity t) t) env evd trm)

(* Apply the promotion/forgetful function to the hypotheses *)
let ornament_hypos env evd (l : lifting) (from_ind, to_ind) trm =
  let hypos = on_type prod_to_lambda env evd trm in
  let subbed_hypos = sub_in_hypos l env from_ind to_ind hypos in
  let env_hypos = zoom_env zoom_lambda_term env subbed_hypos in
  reconstruct_lambda env_hypos (ornament_args env_hypos evd from_ind l trm)

(* Apply the promotion/forgetful function to the conclusion, if applicable *)
let ornament_concls concl_typ env evd (l : lifting) (from_ind, _) trm =
  map_if
    (fun trm ->
      let (env_zoom, trm_zoom) = zoom_lambda_term env trm in
      let args =
        map_directional
          unfold_args
          (fun concl_typ ->
            let lam_typ = zoom_sig_lambda concl_typ in
            let inner_typ = zoom_term zoom_lambda_term empty_env lam_typ in
            let concl_args = unfold_args inner_typ in
            try
              remove_index (Option.get l.orn.index_i) (unshift_all concl_args)
            with _ ->
              (* curried *)
              concl_args)
          l
          concl_typ
      in reconstruct_lambda env_zoom (mkAppl (lift_to l, snoc trm_zoom args)))
    (is_or_applies from_ind (zoom_if_sig concl_typ))
    trm

                                      
(*
 * Apply an ornament, but don't reduce the result.
 *
 * Assumes indexing ornament for now.
 * For a version that dealt with eliminating the sigma type, but was messier,
 * see code prior to 3/15. For now, we leave that step to later,
 * since it's much nicer that way.
 *)
let apply_indexing_ornament env evd l trm =
  let orn_type = reduce_type env evd l.orn.promote in
  let (from_with_args, to_with_args) = ind_of_promotion_type orn_type in
  let env_to = pop_rel_context 1 (zoom_env zoom_product_type env orn_type) in
  let from_ind = first_fun from_with_args in
  let to_ind = reconstruct_lambda env_to (unshift to_with_args) in
  let inds =
    map_backward
      (fun (f, t) ->
        (zoom_sig (zoom_term zoom_lambda_term empty_env t), f))
      l
      (from_ind, to_ind)
  in
  let app_orn ornamenter = ornamenter env evd l inds in
  let (env_concl, concl_typ) = on_type (zoom_product_type env) env evd trm in
  let concl_typ = reduce_nf env_concl concl_typ in
  app_orn (ornament_concls concl_typ) (app_orn ornament_hypos trm)
