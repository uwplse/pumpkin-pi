(*
 * Searching for ornamental promotions between inductive types.
 * This implements the automation from 5.1.1.
 * Some of the useful dependencies can be found in the differencing component.
 *)

open Names
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
open Printing

(* --- Finding the new index --- *)

(* 
 * As described in "Finding the New Index" in Section 5.1.1,
 * search starts by identifying the new index and offset.
 * The bulk of this is in the differencing component.
 *)

(* Find the new index offset and type *)
let find_new_index npm o n =
  let (_, pind_o, _, _, elim_t_o) = o in
  let (env_n, pind_n, _, _, elim_t_n) = n in
  let (ind_o, ind_n) = map_tuple fst (map_tuple destInd (pind_o, pind_n)) in
  let idx_op = new_index_type_simple env_n npm ind_o ind_n in
  if Option.has_some idx_op then
    Option.get idx_op
  else
    new_index_type env_n elim_t_o elim_t_n

(* --- Finding the indexer --- *)

(*
 * As described in the paragraph "Searching for the Indexer" in Section
 * 5.1.1, once the algorithm has the index offset and type, it then
 * searches for the indexer function. It does this by
 * traversing the types of the eliminators in parallel and forming
 * the function as it goes, substituting in the appropriate motive.
 *)            

(*
 * Convenience function that rules out hypotheses that the algorithm thinks
 * compute candidate old indices that actually compute new indices, so that
 * we only have to do this much computation when we have a lead to begin with.
 *
 * The gist is that any new hypothesis in a constructor that has a different
 * type from the corresponding hypothesis in the old constructor definitely
 * computes a new index, assuming an indexing ornamental relationship
 * and no other changes. So if we find one of those we just assume it's an
 * index. But this does not capture every kind of index, so if we can't
 * make that assumption, then we need to do an extra check.
 *
 * An example might be if an inductive type already has an index of type nat,
 * and then we add a new index of type nat next to it. We then need to figure
 * out which index is the new one, and a naive (but efficient) algorithm may
 * ignore the correct index. This lets us only check that condition
 * in those situations, and otherwise just look for obvious indices by
 * comparing hypotheses.
 *)
let false_lead env evd index_i p b_o b_n =
  let same_arity = (arity b_o = arity b_n) in
  debug_term env b_n "checking b_n";
  debug_term env (mkRel 1) "index";
  let is_new_index = computes_only_index env evd index_i p (mkRel 1) b_n in
  (if is_new_index then
     debug_term env b_o "found it! b_o"
   else
     ());
  (not same_arity) && is_new_index

(*
 * Get a single case for the indexer, given:
 * 1. index_i, the location of the new index in the motive
 * 2. index_t, the type of the new index in the motive
 * 3. o, the old environment, inductive type, and constructor
 * 4. n, the new environment, inductive type, and constructor
 *
 * Eventually, it would be good to make this logic less ad-hoc,
 * though the terms we are looking at here are type signatures of
 * induction principles, and so should be very predictable.
 *
 * TODO need to fix ambiguous case with bst2 in Test.v
 *)
let index_case evd index_i p o n : types =
  let get_index = get_new_index index_i in
  let rec diff_case p_i p subs o n =
    let (e_o, ind_o, trm_o) = o in
    let (e_n, ind_n, trm_n) = n in
    match map_tuple kind (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       (* premises *)
       let p_b = shift p in
       let diff_b = diff_case (shift p_i) p_b in
       let e_n_b = push_local (n_n, t_n) e_n in
       let n_b = (e_n_b, shift ind_n, b_n) in
       let same = same_mod_indexing e_o p in
       let is_false_lead = false_lead e_n_b evd index_i p_b b_o in
       if (not (same (ind_o, t_o) (ind_n, t_n))) || (is_false_lead b_n) then
         (* index *)
         let e_o_b = push_local (n_n, t_n) e_o in
         let subs_b = shift_subs subs in
         let o_b = (e_o_b, shift ind_o, shift trm_o) in
         unshift (diff_b subs_b o_b n_b)
       else
         let e_o_b = push_local (n_o, t_o) e_o in
         let o_b = (e_o_b, shift ind_o, b_o) in
         if apply p t_o t_n then
           (* inductive hypothesis *)
           let sub_index = (shift (get_index p t_o t_n), mkRel 1) in
           let subs_b = sub_index :: shift_subs subs in
           mkLambda (n_o, mkAppl (p_i, unfold_args t_o), diff_b subs_b o_b n_b)
         else
           (* no change *)
           let subs_b = shift_subs subs in
           mkLambda (n_o, t_o, diff_b subs_b o_b n_b)
    | (App (_, _), App (_, _)) ->
       (* conclusion *)
       let index = get_index p trm_o trm_n in
       List.fold_right all_eq_substs subs index
    | _ ->
       failwith "unexpected case"
  in diff_case p (mkRel 1) [] o n

(* Get the cases for the indexer *)
let indexer_cases evd index_i p npm o n : types list =
  let (env_o, ind_o, arity_o, _, elim_t_o) = o in
  let (env_n, ind_n, arity_n, _, elim_t_n) = n in
  match map_tuple kind (elim_t_o, elim_t_n) with
  | (Prod (n_o, p_o, b_o), Prod (n_n, p_n, b_n)) ->
     let env_p_o = push_local (n_o, p_o) env_o in
     let env_p_n = push_local (n_n, p_n) env_n in
     let o c = (env_p_o, ind_o, c) in
     let n c = (env_p_n, ind_n, c) in
     List.map2
       (fun c_o c_n ->
         shift_by
           (arity_o - npm)
           (index_case evd index_i p (o c_o) (n c_n)))
       (take_except (arity_o - npm + 1) (factor_product b_o))
       (take_except (arity_n - npm + 1) (factor_product b_n))
  | _ ->
     failwith "not eliminators"

(* Search for an indexing function *)
let find_indexer evd idx npm o n : types =
  let (env_o, _, arity_o, elim, elim_t_o) = o in
  let (env_n, _, _, _, elim_t_n) = n in
  let (index_i, index_t) = idx in
  let index_t = shift_by npm index_t in
  match map_tuple kind (elim_t_o, elim_t_n) with
  | (Prod (_, p_o, _), Prod (_, p_n, _)) ->
     let env_ind = zoom_env zoom_product_type env_o p_o in
     let off = offset env_ind npm in
     let pms = shift_all_by (arity_o - npm + 1) (mk_n_rels npm) in
     let index_t_p = shift_by index_i index_t in
     let p = reconstruct_lambda_n env_ind index_t_p npm in
     let cs = indexer_cases evd index_i (shift p) npm o n in
     let final_args = mk_n_rels off in
     let p = shift_by off p in
     let app = apply_eliminator {elim; pms; p; cs; final_args} in
     reconstruct_lambda env_ind app
  | _ ->
     failwith "not eliminators"

(* --- Finding promote and forget --- *)

(*
 * This implements the "Searching for Promote and Forget" paragraph of
 * Section 5.1.1. It works a lot like searching for the indexer, but
 * it uses a different motive.
 *)

(*
 * Stretch the old motive type to match the new one
 * That is, add indices where they are missing in the old motive
 * For now just supports one index
 *)
let rec stretch_motive_type index_i env o n =
  let (ind_o, p_o) = o in
  let (ind_n, p_n) = n in
  match map_tuple kind (p_o, p_n) with
  | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
     let n_b = (shift ind_n, b_n) in
     if index_i = 0 then
       mkProd (n_n, t_n, shift p_o)
     else
       let env_b = push_local (n_o, t_o) env in
       let o_b = (shift ind_o, b_o) in
       mkProd (n_o, t_o, stretch_motive_type (index_i - 1) env_b o_b n_b)
  | _ ->
     p_o

(*
 * Stretch the old motive to match the new one at the term level
 *
 * Hilariously, this function is defined as an ornamented
 * version of stretch_motive_type.
 *)
let stretch_motive index_i env o n =
  let (ind_o, p_o) = o in
  let o = (ind_o, lambda_to_prod p_o) in
  prod_to_lambda (stretch_motive_type index_i env o n)

(*
 * Stretch out the old eliminator type to match the new one
 * That is, add indexes to the old one to match new
 *)
let stretch index_i env indexer pms o n =
  let (ind_o, elim_t_o) = o in
  let (ind_n, elim_t_n) = n in
  let (n_exp, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, _) = destProd elim_t_n in
  let p_exp = stretch_motive_type index_i env (ind_o, p_o) (ind_n, p_n) in
  let b_exp =
    map_term_if
      (fun (p, _) t -> applies p t)
      (fun (p, pms) t ->
        let non_pms = unfold_args t in
        let index = mkApp (indexer, Array.append pms (Array.of_list non_pms)) in
        mkAppl (p, insert_index index_i index non_pms))
      (fun (p, pms) -> (shift p, Array.map shift pms))
      (mkRel 1, pms)
      b_o
  in mkProd (n_exp, p_exp, b_exp)

(*
 * Utility function
 * Remove the binding at index i from the environment
 *)
let remove_rel (i : int) (env : env) : env =
  let (env_pop, popped) = lookup_pop i env in
  let push =
    List.mapi
      (fun j rel ->
        let (n, _, t) = CRD.to_tuple rel in
        (n, unshift_local (i - j - 1) 1 t))
      (List.rev (List.tl (List.rev popped)))
  in List.fold_right push_local push env_pop

(*
 * Modify a case of an eliminator application to use
 * the new motive p in its hypotheses
 *)
let with_new_motive p c : types =
  let rec sub_p sub trm =
    let (p_o, p_n) = sub in
    match kind trm with
    | Prod (n, t, b) ->
       let sub_p_n t = mkAppl (p_n, unfold_args t) in
       let t' = map_if sub_p_n (applies p_o t) t in
       mkProd (n, t', sub_p (map_tuple shift sub) b)
    | _ ->
       trm
  in sub_p (mkRel 1, p) c

(*
 * Find the motive that the ornamental promotion or forgetful function proves
 * for an indexing function
 *)
let ornament_p index_i env ind arity npm indexer_opt =
  let off = offset env npm in
  let off_args = off - (arity - npm) in
  let args = shift_all_by off_args (mk_n_rels arity) in
  let index_i_npm = npm + index_i in
  let concl =
    match indexer_opt with
    | Some indexer ->
       (* forward (indexing/promotion) direction *)
       let indexer = Option.get indexer_opt in
       let index = mkAppl (indexer, snoc (mkRel 1) args) in
       mkAppl (ind, insert_index index_i_npm index args)
    | None ->
       (* backward (deindexing/forgetful) direction *)
       mkAppl (ind, adjust_no_index index_i_npm args)
  in shift_by off (reconstruct_lambda_n env concl npm)

(*
 * Given terms that apply properties, update the
 * substitution list to include the corresponding new index
 *)
let sub_index evd f_indexer subs o n =
  let (env_o, app_o) = o in
  let (env_n, app_n) = n in
  let (args_o, args_n) = map_tuple unfold_args (app_o, app_n) in
  let args = List.combine args_o args_n in
  let new_subs =
    List.map
      (fun (a_o, a_n) ->
        if applies f_indexer a_o then
          (* substitute the inductive hypothesis *)
          (shift a_n, shift a_o)
        else
          (* substitute the index *)
          (shift a_n, mkRel 1))
      (List.filter
         (fun (a_o, a_n) ->
           let o = (env_o, a_o) in
           let n = (env_n, a_n) in
           applies f_indexer a_o || not (same_type env_o evd o n))
         args)
  in List.append new_subs subs

(* In the conclusion of each case, return c_n with c_o's indices *)
let sub_indexes evd index_i is_fwd f_indexer p subs o n : types =
  let directional a b = if is_fwd then a else b in
  let rec sub p subs o n =
    let (env_o, ind_o, c_o) = o in
    let (env_n, ind_n, c_n) = n in
    match map_tuple kind (c_o, c_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       let same = same_mod_indexing env_o p (ind_o, t_o) (ind_n, t_n) in
       let env_o_b = push_local (n_o, t_o) env_o in
       let env_n_b = push_local (n_n, t_n) env_n in
       debug_term env_n_b b_n "b_n";
       debug_term env_o_b b_o "b_o";
       let false_lead_f b_o b_n = false_lead env_n_b evd index_i p_b b_o b_n in
       let false_lead_b b_o b_n = false_lead env_o_b evd index_i p_b b_n b_o in
       let is_false_lead = directional false_lead_f false_lead_b in
       if applies p t_n || (same && not (is_false_lead b_o b_n)) then
         let o_b = (env_o_b, shift ind_o, b_o) in
         let n_b = (env_n_b, shift ind_n, b_n) in
         let subs_b =
           map_if
             (fun subs ->
               (* add the index for the IH to the substitutions *)
               sub_index evd f_indexer subs (env_o, t_o) (env_n, t_n))
             (applies p t_n) (* t_n is an IH *)
             (shift_subs subs)
         in mkProd (n_o, t_o, sub p_b subs_b o_b n_b)
       else
         let subs_b = shift_subs subs in
         let new_index = directional (n_n, t_n) (n_o, t_o) in
         let (b_o_b, b_n_b) = directional (shift c_o, b_n) (b_o, shift c_n) in
         let env_o_b = push_local new_index env_o in
         let env_n_b = push_local new_index env_n in
         let o_b = (env_o_b, shift ind_o, b_o_b) in
         let n_b = (env_n_b, shift ind_n, b_n_b) in
         let subbed_b = sub p_b subs_b o_b n_b in
         (directional unshift (fun b -> mkProd (n_o, t_o, b))) subbed_b
    | (App (f_o, args_o), App (f_n, args_n)) ->
       List.fold_right all_eq_substs subs (last (unfold_args c_n))
    | _ ->
       failwith "unexpected case substituting index"
  in sub p subs o n

(*
 * Get a case for an indexing ornamental promotion/forgetful function.
 *
 * This currently works in the following way:
 * 1. If it's forwards, then adjust the motive to have the index
 * 2. Substitute in the motive to the old case
 * 3. Substitute in the indexes (or lack thereof, if backwards)
 *
 * Eventually, we might want to think of this as (or rewrite this to)
 * abstracting the indexed type to take an indexing function, then
 * deriving the result through specialization.
 *)
let orn_index_case evd index_i is_fwd indexer_f orn_p o n : types =
  let (env_o, arity_o, ind_o, _, c_o) = o in
  let (env_n, arity_n, ind_n, p_n, c_n) = n in
  let d_arity = arity_n - arity_o in
  let adjust p = stretch_motive index_i env_o (ind_o, p) (ind_n, p_n) in
  let p_o = map_if (fun p -> adjust (unshift_by d_arity p)) is_fwd orn_p in
  let o = (env_o, ind_o, c_o) in
  let n = (env_n, ind_n, c_n) in
  let subbed = sub_indexes evd index_i is_fwd indexer_f (mkRel 1) [] o n in
  prod_to_lambda (with_new_motive (shift_by d_arity p_o) subbed)

(* Get the cases for the ornamental promotion/forgetful function. *)
let orn_index_cases evd index_i npm is_fwd indexer_f orn_p o n : types list =
  let (env_o, pind_o, arity_o, elim_t_o) = o in
  let (env_n, pind_n, arity_n, elim_t_n) = n in
  match map_tuple kind (elim_t_o, elim_t_n) with
  | (Prod (_, p_o, b_o), Prod (_, p_n, b_n)) ->
     let o c = (env_o, arity_o, pind_o, p_o, c) in
     let n c = (env_n, arity_n, pind_n, p_n, c) in
     let arity = if is_fwd then arity_o else arity_n in
     List.map2
       (fun c_o c_n ->
         shift_by
           (arity - npm)
           (orn_index_case evd index_i is_fwd indexer_f orn_p (o c_o) (n c_n)))
       (take_except (arity_o - npm + 1) (factor_product b_o))
       (take_except (arity_n - npm + 1) (factor_product b_n))
  | _ ->
     failwith "not an eliminator"

(*
 * Make a packer function for existT/sigT
 *)
let make_packer env evd typ args (index_i, index_typ) is_fwd =
  let sub_index = if is_fwd then insert_index else reindex in
  let packed_args = sub_index index_i (mkRel 1) (shift_all args) in
  let env_abs = push_local (Anonymous, index_typ) env in
  abstract_arg env_abs evd index_i (mkAppl (typ, packed_args))

(*
 * Pack the conclusion of an ornamental promotion
 *)
let pack_conclusion env evd idx f_indexer n unpacked =
  let (ind, arity) = n in
  let off = arity - 1 in
  let index_type = shift_by off (snd idx) in
  let packer = make_packer env evd ind (mk_n_rels off) idx true in
  let index = mkAppl (f_indexer, mk_n_rels arity) in
  (env, pack_existT {index_type; packer; index; unpacked})

(*
 * Pack the hypothesis type into a sigT, and update the environment
 *)
let pack_hypothesis_type env index_type packer (id, unpacked_typ) : env =
  let packer = unshift packer in
  let packed_typ = pack_sigT { index_type ; packer } in
  push_local (id, packed_typ) (pop_rel_context 1 env)

(*
 * Apply the packer to the index
 *)
let apply_packer env packer arg =
  reduce_term env (mkAppl (packer, [arg]))

(*
 * Remove the index from the environment, and adjust terms appropriately
 *)
let adjust_to_elim env index_rel packer packed =
  let env_packed = remove_rel (index_rel + 1) env in
  let adjust = unshift_local index_rel 1 in
  (env_packed, adjust packer, adjust packed)

(*
 * Pack the unpacked term to eliminate using the new hypothesis
 *)
let pack_unpacked env packer index_typ index_rel unpacked =
  let sub_typ = all_eq_substs (mkRel (4 - index_rel), mkRel 1) in
  let sub_index = all_eq_substs (mkRel (index_rel + 3), mkRel 2) in
  let adjust trm = shift_local index_rel 1 (shift trm) in
  let typ_body = sub_index (sub_typ (adjust unpacked)) in
  let packer_indexed = apply_packer env (shift packer) (mkRel 1) in
  let index_body = mkLambda (Anonymous, packer_indexed, typ_body) in
  mkLambda (Anonymous, shift index_typ, index_body)

(*
 * Pack the hypothesis of an ornamental forgetful function
 *)
let pack_hypothesis env evd idx o n unpacked =
  let (index_i, index_type) = idx in
  let (ind, arity) = o in
  let index_type = shift index_type in
  let (id, _, unpacked_typ) = CRD.to_tuple @@ lookup_rel 1 env in
  let packer = make_packer env evd ind (unfold_args unpacked_typ) idx false in
  let env_push = pack_hypothesis_type env index_type packer (id, unpacked_typ) in
  let index_rel = offset (pop_rel_context 1 env) index_i in
  let unpacked = pack_unpacked env_push packer index_type index_rel unpacked in
  let adjusted = adjust_to_elim env_push index_rel packer unpacked in
  let (env_packed, packer, unpacked) = adjusted in
  let arg = mkRel 1 in
  let arg_typ = on_type dest_sigT env_packed evd arg in
  let index = project_index arg_typ arg in
  let value = project_value arg_typ arg in
  (env_packed, reduce_term env_packed (mkAppl (unpacked, [index; value])))

(*
 * This packs an ornamental promotion to/from an indexed type like Vector A n,
 * with n at index_i, into a sigma type. The theory of this is more elegant,
 * and the types are easier to reason about automatically. However,
 * the other version may be more desirable for users.
 *
 * It is simple to extract the unpacked version from this form;
 * later it might be useful to define both separately.
 * For now we have a metatheoretic guarantee about the indexer we return
 * corresponding to the projection of the sigma type.
 *)
let pack_orn env evd idx f_indexer o n is_fwd unpacked =
  if is_fwd then
    pack_conclusion env evd idx f_indexer n unpacked
  else
    pack_hypothesis env evd idx o n unpacked

(* Search for the promotion or forgetful function *)
let find_promote_or_forget evd idx npm indexer_n o n is_fwd =
  let directional a b = if is_fwd then a else b in
  let call_directional f a b = if is_fwd then f a b else f b a in
  let (env_o, ind_o, arity_o, elim_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elin_n, elim_t_n) = n in
  let f_indexer = make_constant indexer_n in
  let f_indexer_opt = directional (Some f_indexer) None in
  match map_tuple kind (elim_t_o, elim_t_n) with
  | (Prod (n_o, p_o, b_o), Prod (n_n, p_n, b_n)) ->
     let env_o_b = push_local (n_o, p_o) env_o in
     let env_n_b = push_local (n_n, p_n) env_n in
     let env_ornament = zoom_env zoom_product_type env_o p_o in
     let off = offset env_ornament npm in
     let pms = shift_all_by off (mk_n_rels npm) in
     let (ind, arity) = directional (ind_n, arity_o) (ind_n, arity_n) in
     let nind = arity - npm in
     let align_pms = Array.of_list (unshift_all_by nind pms) in
     let (idx_i, idx_t) = idx in
     let align = stretch idx_i env_o f_indexer align_pms in
     let elim_t = call_directional align (ind_o, elim_t_o) (ind_n, elim_t_n) in
     let elim_t_o = directional elim_t elim_t_o in
     let elim_t_n = directional elim_t_n elim_t in
     let o = (env_o_b, ind_o, arity_o, elim_t_o) in
     let n = (env_n_b, ind_n, arity_n, elim_t_n) in
     let p = ornament_p idx_i env_ornament ind arity npm f_indexer_opt in
     let p_cs = unshift_by nind p in
     let adj = shift_all_by (offset2 env_ornament env_o_b - nind) in
     let cs = adj (orn_index_cases evd idx_i npm is_fwd f_indexer p_cs o n) in
     let final_args = mk_n_rels off in
     let elim = elim_o in
     let unpacked = apply_eliminator {elim; pms; p; cs; final_args} in
     let o = (ind_o, arity_o) in
     let n = (ind_n, arity_n) in
     let idx = (npm + idx_i, idx_t) in
     let packed = pack_orn env_ornament evd idx f_indexer o n is_fwd unpacked in
     reconstruct_lambda (fst packed) (snd packed)
  | _ ->
     failwith "not eliminators"

(* Find promote and forget *)
let find_promote_forget evd idx npm indexer_n o n =
  twice (find_promote_or_forget evd idx npm indexer_n) o n

(* --- Algebraic ornaments --- *)
              
(*
 * Search two inductive types for an algebraic ornament between them
 * (search algorithm from 5.1.1)
 *)
let search_algebraic env evd npm indexer_n o n =
  let (pind_o, arity_o) = o in
  let (pind_n, arity_n) = n in
  let (ind_o, _) = destInd pind_o in
  let (ind_n, _) = destInd pind_n in
  let (el_o, el_n) = map_tuple (type_eliminator env) (ind_o, ind_n) in
  let (el_t_o, el_t_n) = map_tuple (infer_type env evd) (el_o, el_n) in
  let (env_o, el_t_o') = zoom_n_prod env npm el_t_o in
  let (env_n, el_t_n') = zoom_n_prod env npm el_t_n in
  let o = (env_o, pind_o, arity_o, el_o, el_t_o') in
  let n = (env_n, pind_n, arity_n, el_n, el_t_n') in
  let idx = find_new_index npm o n in
  Printf.printf "%d\n" (fst idx);
  let indexer = find_indexer evd idx npm o n in
  debug_term env indexer "indexer";
  let (promote, forget) = find_promote_forget evd idx npm indexer_n o n in
  debug_term env promote "promote";
  debug_term env forget "forget";
  { indexer; promote; forget }

(* --- Top-level search --- *)

(*
 * Search two inductive types for an ornament between them.
 * This is more general to handle eventual extension with other 
 * kinds of ornaments.
 *)
let search_orn_inductive env evd indexer_id trm_o trm_n : promotion =
  match map_tuple kind (trm_o, trm_n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if not (npm_o = npm_n) then
       (* new parameter *)
       failwith "new parameters are not yet supported"
     else
       let npm = npm_o in
       let (typ_o, typ_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
       let (arity_o, arity_n) = map_tuple arity (typ_o, typ_n) in
       if not (arity_o = arity_n) then
         (* new index *)
         let o = (trm_o, arity_o) in
         let n = (trm_n, arity_n) in
         let (o, n) = map_if reverse (arity_n <= arity_o) (o, n) in
         search_algebraic env evd npm indexer_id o n
       else
         failwith "this kind of change is not yet supported"
  | _ ->
     failwith "this kind of change is not yet supported"
