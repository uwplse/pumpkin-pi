(*
 * Differencing for ornamenting inductive types
 *)

open Term
open Environ
open Coqterms
open Utilities
open Debruijn
open Indexing
open Hofs
open Factoring
open Zooming
open Abstraction
open Printing
open Lifting
open Declarations

(* --- Differencing terms --- *)

(* Check if two terms have the same type, ignoring universe inconsinstency *)
let same_type env evd o n =
  let (env_o, t_o) = o in
  let (env_n, t_n) = n in
  try
    convertible env (infer_type env_o evd t_o) (infer_type env_n evd t_n)
  with _ ->
    false

(*
 * Returns true if two applications contain have a different
 * argument at index i.
 *
 * For now, this uses precise equality, but we can loosen this
 * to convertibility if desirable.
 *)
let diff_arg i trm_o trm_n =
  try
    let arg_o = get_arg i trm_o in
    let arg_n = get_arg i trm_n in
    not (eq_constr arg_o arg_n)
  with _ ->
    true

(* --- Differencing inductive types --- *)

(* is_or_applies over two terms with a different check *)
let apply_old_new (o : types * types) (n : types * types) : bool =
  let (trm_o, trm_o') = o in
  let (trm_n, trm_n') = n in
  is_or_applies trm_o trm_o' && is_or_applies trm_n trm_n'

(* Check if two terms are the same modulo a change of an inductive type *)
let same_mod_change env o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  apply_old_new o n || convertible env t_o t_n

(* Check if two terms are the same modulo an indexing of an inductive type *)
let same_mod_indexing env p_index o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  are_or_apply p_index t_o t_n || same_mod_change env o n

(* --- Indexers --- *)

(*
 * Returns true if the argument at the supplied index location of the 
 * inductive property (which should be at relative index 1 before calling
 * this function) is an index to some application of the induction principle
 * in the second term that was not an index to any application of the induction
 * principle in the first term.
 *
 * In other words, this looks for applications of the property
 * in the induction principle type, checks the argument at the location,
 * and determines whether they were equal. If they are ever not equal,
 * then the index is considered to be new. Since we are ornamenting,
 * we can assume that we maintain the same inductive structure, and so
 * we should encounter applications of the induction principle in both
 * terms in exactly the same order.
 *)
let new_index i trm_o trm_n =
  let rec is_new_index p trm_o trm_n =
    match map_tuple kind_of_term (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       if applies p t_o && not (applies p t_n) then
         is_new_index p_b (shift trm_o) b_n
       else
         is_new_index p t_o t_n || is_new_index p_b b_o b_n
    | (App (_, _), App (_, _)) when applies p trm_o && applies p trm_n ->
       let args_o = List.rev (List.tl (List.rev (unfold_args trm_o))) in
       let args_n = List.rev (List.tl (List.rev (unfold_args trm_n))) in
       diff_arg i (mkAppl (p, args_o)) (mkAppl (p, args_n))
    | _ ->
       false
  in is_new_index (mkRel 1) trm_o trm_n

(*
 * Assuming there is an indexing ornamental relationship between two 
 * eliminators, get the type and location of the new index.
 *
 * If indices depend on earlier types, the types may be dependent;
 * the client needs to shift by the appropriate offset.
 *)
let new_index_type env elim_t_o elim_t_n =
  let (_, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, b_n) = destProd elim_t_n in
  let rec poss_indices e p_o p_n =
    match map_tuple kind_of_term (p_o, p_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if isProd b_o && convertible e t_o t_n then
         let e_b = push_local (n_o, t_o) e in
         let same = poss_indices e_b b_o b_n in
         let different = (0, t_n) in
         different :: (List.map (fun (i, i_t) -> (shift_i i, i_t)) same)
       else
         [(0, t_n)]
    | _ ->
       failwith "could not find indexer property"
  in List.find (fun (i, _) -> new_index i b_o b_n) (poss_indices env p_o p_n)
               
(*
 * This is Nate's simple search heuristic that works when there is no ambiguity
 * TODO env is missing parameters, need to push those somehow
 *)
let diff_context_simple env ctx_o ctx_n =
  let open Util in
  let open Context in
  let decls_o = List.rev ctx_o in
  let decls_n = List.rev ctx_n in
  let nth_type (n : int) : types = Rel.Declaration.get_type (List.nth decls_n n) in
  let rec scan env pos diff (decls_o, decls_n) : int option =
    match (decls_o, decls_n) with
    | (decl_o :: decls_o'), (decl_n :: decls_n') ->
      let type_o = Rel.Declaration.get_type decl_o in
      let type_n = Rel.Declaration.get_type decl_n in
      let env' = Environ.push_rel decl_n env in
      if convertible env type_o type_n then
        let diff' = scan env' (pos + 1) diff (decls_o', decls_n') in
        if Option.has_some diff' && Option.get diff' = pos + 1 then
          let type_i = nth_type (pos + 1) in
          if not (convertible env' (shift type_o) type_i) then
            diff'
          else
            None (* ambiguous, can't use this heuristic *)
        else
          diff'
      else
        scan env' (pos + 1) (Some pos) (decls_o, decls_n')
    | [], [] -> None
    | [], (decl_n :: decls_n) -> Some pos
    | (_ :: _), [] -> None
  in
  let diff_pos = scan env 0 None (decls_o, decls_n) in
  if Option.has_some diff_pos then
    let pos = Option.get diff_pos in
    let typ = nth_type pos in
    Some (pos, typ)
  else
    None
               
(*
 * Top-level index finder for Nate's heuristic
 *)
let new_index_type_simple env npars ind_o ind_n =
  let open Util in
  let open Constr in
  (* Applying each parameter increments the index for the next one. *)
  let pars = List.make npars (mkRel npars) in
  let pind_o = Univ.in_punivs ind_o in
  let pind_n = Univ.in_punivs ind_n in
  let indf_o = Inductiveops.make_ind_family (pind_o, pars) in
  let indf_n = Inductiveops.make_ind_family (pind_n, pars) in
  let (idcs_o, _) = Inductiveops.get_arity env indf_o in
  let (idcs_n, _) = Inductiveops.get_arity env indf_n in
  diff_context_simple env idcs_o idcs_n

(*
 * Given an old and new application of a property, find the new index.
 * This also assumes there is only one new index.
 *)
let get_new_index index_i p o n =
  match map_tuple kind_of_term (o, n) with
  | (App (f_o, _), App (f_n, _)) when are_or_apply p f_o f_n ->
     get_arg index_i n
  | _ ->
     failwith "not an application of a property"

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
  not same_arity && (computes_only_index env evd index_i p (mkRel 1) b_n)

(*
 * Get a single case for the indexer, given:
 * 1. index_i, the location of the new index in the property
 * 2. index_t, the type of the new index in the property
 * 3. o, the old environment, inductive type, and constructor
 * 4. n, the new environment, inductive type, and constructor
 *
 * Eventually, it would be good to make this logic less ad-hoc,
 * though the terms we are looking at here are type signatures of
 * induction principles, and so should be very predictable.
 *)
let index_case evd index_i p o n : types =
  let get_index = get_new_index index_i in
  let rec diff_case p_i p subs o n =
    let (e_o, ind_o, trm_o) = o in
    let (e_n, ind_n, trm_n) = n in
    match map_tuple kind_of_term (trm_o, trm_n) with
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
  let (env_o, ind_o, arity_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elim_t_n) = n in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
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
let search_for_indexer evd idx npm elim o n is_fwd : types option =
  if is_fwd then
    let (env_o, _, arity_o, elim_t_o) = o in
    let (env_n, _, _, elim_t_n) = n in
    let (index_i, index_t) = idx in
    let index_t = shift_by npm index_t in
    match map_tuple kind_of_term (elim_t_o, elim_t_n) with
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
       Some (reconstruct_lambda env_ind app)
    | _ ->
       failwith "not eliminators"
  else
    None

(* --- Indexing ornaments --- *)

(*
 * Stretch the old property type to match the new one
 * That is, add indices where they are missing in the old property
 * For now just supports one index
 *)
let rec stretch_property_type index_i env o n =
  let (ind_o, p_o) = o in
  let (ind_n, p_n) = n in
  match map_tuple kind_of_term (p_o, p_n) with
  | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
     let n_b = (shift ind_n, b_n) in
     if index_i = 0 then
       mkProd (n_n, t_n, shift p_o)
     else
       let env_b = push_local (n_o, t_o) env in
       let o_b = (shift ind_o, b_o) in
       mkProd (n_o, t_o, stretch_property_type (index_i - 1) env_b o_b n_b)
  | _ ->
     p_o

(*
 * Stretch the old property to match the new one at the term level
 *
 * Hilariously, this function is defined as an ornamented
 * version of stretch_property_type.
 *)
let stretch_property index_i env o n =
  let (ind_o, p_o) = o in
  let o = (ind_o, lambda_to_prod p_o) in
  prod_to_lambda (stretch_property_type index_i env o n)

(*
 * Stretch out the old eliminator type to match the new one
 * That is, add indexes to the old one to match new
 *)
let stretch index_i env indexer pms o n =
  let (ind_o, elim_t_o) = o in
  let (ind_n, elim_t_n) = n in
  let (n_exp, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, _) = destProd elim_t_n in
  let p_exp = stretch_property_type index_i env (ind_o, p_o) (ind_n, p_n) in
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
 * the new property p in its hypotheses
 *)
let with_new_property p c : types =
  let rec sub_p sub trm =
    let (p_o, p_n) = sub in
    match kind_of_term trm with
    | Prod (n, t, b) ->
       let sub_p_n t = mkAppl (p_n, unfold_args t) in
       let t' = map_if sub_p_n (applies p_o t) t in
       mkProd (n, t', sub_p (map_tuple shift sub) b)
    | _ ->
       trm
  in sub_p (mkRel 1, p) c

(*
 * Find the property that the ornamental promotion or forgetful function proves
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
    match map_tuple kind_of_term (c_o, c_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       let same = same_mod_indexing env_o p (ind_o, t_o) (ind_n, t_n) in
       let env_o_b = push_local (n_o, t_o) env_o in
       let env_n_b = push_local (n_n, t_n) env_n in
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
         (* new hypothesis from which the index is computed *)
         let subs_b = directional (shift_to subs) (shift_from subs) in
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
 * 1. If it's forwards, then adjust the property to have the index
 * 2. Substitute in the property to the old case
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
  let adjust p = stretch_property index_i env_o (ind_o, p) (ind_n, p_n) in
  let p_o = map_if (fun p -> adjust (unshift_by d_arity p)) is_fwd orn_p in
  let c_o = with_new_property (shift_by d_arity p_o) c_o in
  let o = (env_o, ind_o, c_o) in
  let n = (env_n, ind_n, c_n) in
  prod_to_lambda (sub_indexes evd index_i is_fwd indexer_f (mkRel 1) [] o n)

(* Get the cases for the ornamental promotion/forgetful function. *)
let orn_index_cases evd index_i npm is_fwd indexer_f orn_p o n : types list =
  let (env_o, pind_o, arity_o, elim_t_o) = o in
  let (env_n, pind_n, arity_n, elim_t_n) = n in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
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
  reduce_term env (mkAppl (packer, [mkRel 1]))

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
 * Get the body of the eliminator when packing the hypothesis
 *)
let elim_body index_type packer f args =
  let packed_type = pack_sigT { index_type; packer } in
  mkLambda (Anonymous, packed_type, shift (mkAppl (f, args)))

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
let pack env evd idx f_indexer o n is_fwd unpacked =
  if is_fwd then
    pack_conclusion env evd idx f_indexer n unpacked
  else
    pack_hypothesis env evd idx o n unpacked

(* Search two inductive types for an indexing ornament, using eliminators *)
let search_orn_index_elim evd idx npm indexer_n elim_o o n is_fwd =
  let directional a b = if is_fwd then a else b in
  let call_directional f a b = if is_fwd then f a b else f b a in
  let (env_o, ind_o, arity_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elim_t_n) = n in
  let indexer = search_for_indexer evd idx npm elim_o o n is_fwd in
  let f_indexer = make_constant indexer_n in
  let f_indexer_opt = directional (Some f_indexer) None in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
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
     let idx_i_o = directional (Some idx_i) None in
     let elim = elim_o in
     let unpacked = apply_eliminator {elim; pms; p; cs; final_args} in
     let o = (ind_o, arity_o) in
     let n = (ind_n, arity_n) in
     let idx = (npm + idx_i, idx_t) in
     let packed = pack env_ornament evd idx f_indexer o n is_fwd unpacked in
     (idx_i_o, indexer, reconstruct_lambda (fst packed) (snd packed))
  | _ ->
     failwith "not eliminators"

(*
 * Search two inductive types for an indexing ornament
 *
 * Eventually, to simplify this, we can shortcut some of this search if we
 * take the sigma type directly, so that the tool is told what the new index
 * location is. But this logic is useful for when that isn't true, like when
 * the tool is running fully automatically on existing code to generate
 * new theorems. I've factored out the indexing logic so that
 * later on, it can try to get this from the user with few code changes.
 *)
let search_orn_index env evd npm indexer_n o n is_fwd =
  let call_directional f a b = if is_fwd then f a b else f b a in
  let (pind_o, arity_o) = o in
  let (pind_n, arity_n) = n in
  let (ind_o, _) = destInd pind_o in
  let (ind_n, _) = destInd pind_n in
  let (elim_o, elim_n) = map_tuple (type_eliminator env) (ind_o, ind_n) in
  let (elim_t_o, elim_t_n) = map_tuple (infer_type env evd) (elim_o, elim_n) in
  let (env_o, elim_t_o') = zoom_n_prod env npm elim_t_o in
  let (env_n, elim_t_n') = zoom_n_prod env npm elim_t_n in
  let o = (env_o, pind_o, arity_o, elim_t_o') in
  let n = (env_n, pind_n, arity_n, elim_t_n') in
  let idx_op = call_directional (new_index_type_simple env_n npm) ind_o ind_n in
  let idx =
    if Option.has_some idx_op then
      Option.get idx_op
    else
      call_directional (new_index_type env_n) elim_t_o' elim_t_n'
  in search_orn_index_elim evd idx npm indexer_n elim_o o n is_fwd

(* --- Parameterization ornaments --- *)

(*
 * Search two inductive types for a parameterization ornament
 * This is not yet supported
 *)
let search_orn_params env ind_o ind_n is_fwd : types =
  failwith "parameterization is not yet supported"

(* --- Ornamental differencing --- *)

(*
 * Search two inductive types for an ornament between them
 *)
let search_orn_inductive env evd indexer_id trm_o trm_n : promotion =
  match map_tuple kind_of_term (trm_o, trm_n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if not (npm_o = npm_n) then
       (* new parameter *)
       let search = twice (search_orn_params env) in
       let indexer = None in
       let index_i = None in
       if npm_o < npm_n then
         let (promote, forget) = search (i_o, ii_o) (i_n, ii_n) in
         { index_i; indexer; promote; forget }
       else
         let (promote, forget) = search (i_n, ii_n) (i_o, ii_o) in
         { index_i; indexer; promote; forget }
     else
       let npm = npm_o in
       let (typ_o, typ_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
       let (arity_o, arity_n) = map_tuple arity (typ_o, typ_n) in
       if not (arity_o = arity_n) then
         (* new index *)
         let o = (trm_o, arity_o) in
         let n = (trm_n, arity_n) in
         let (o, n) = map_if reverse (arity_n <= arity_o) (o, n) in
         let search = twice (search_orn_index env evd npm indexer_id) in
         let ((index_i, indexer, promote), (_, _, forget)) = search o n in
         { index_i; indexer; promote; forget }
       else
         failwith "this kind of change is not yet supported"
  | _ ->
     failwith "this kind of change is not yet supported"
