(*
 * Core lifting algorithm
 *)

open Constr
open Environ
open Zooming
open Lifting
open Hofs
open Coqterms
open Debruijn
open Utilities
open Indexing
open Promotions
open Abstraction
open Hypotheses
open Names

(* --- Some utilities for lifting --- *)

(*
 * Given a type we are promoting to/forgetting from,
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
let non_index_args l env typ =
  let index_i = Option.get l.orn.index_i in
  let typ = reduce_nf env typ in
  if is_or_applies sigT typ then
    let packer = (dest_sigT typ).packer in
    remove_index index_i (unfold_args (dummy_index env packer))
  else
    unfold_args typ

(*
 * Given a term with the type we are promoting to/forgetting from,
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
let non_index_typ_args l env evd trm =
  if is_or_applies existT trm then
    (* don't bother type-checking *)
    let packer = (dest_existT trm).packer in
    let index_i = Option.get l.orn.index_i in
    remove_index index_i (unfold_args (dummy_index env packer))
  else
    on_type (non_index_args l env) env evd trm

(*
 * Pack inside of a sigT type
 *)
let pack env evd l unpacked =
  let index_i = Option.get l.orn.index_i in
  let typ = reduce_type env evd unpacked in
  let index = get_arg index_i typ in
  let index_type = infer_type env evd index in
  let packer = abstract_arg env evd index_i typ in
  pack_existT {index_type; packer; index; unpacked}

(*
 * Lift
 *)
let lift env evd l trm =
  let typ_args = non_index_typ_args l env evd trm in
  mkAppl (lift_to l, snoc trm typ_args)
              
(*
 * Pack arguments and lift
 *)
let pack_lift env evd l arg =
  lift env evd l (map_backward (pack env evd l) l arg)
       
(*
 * Determine whether a type is the type we are ornamenting from
 *
 * For simplicity, we assume that the function doesn't have any other
 * applications of that type that don't use the new index, otherwise
 * we would need to track the type arguments everywhere, which is tedious
 *)
let is_orn l env evd (from_typ, to_typ) typ =
  let typ = reduce_nf env (expand_eta env evd typ) in
  if l.is_fwd then
    is_or_applies from_typ typ
  else
    if is_or_applies sigT typ then
      equal to_typ (first_fun (dummy_index env (dest_sigT typ).packer))
    else
      false

(*
 * Filter the arguments to only the ones that have the type we are
 * promoting/forgetting from.
 *)
let filter_orn l env evd (from_typ, to_typ) args =
  List.filter (on_type (is_orn l env evd (from_typ, to_typ)) env evd) args

(* 
 * Get the to/from type from the ornament
 *)
let promotion_type env evd trm =
  fst (on_type ind_of_promotion_type env evd trm)

(*
 * Given the type of a case of an eliminator,
 * determine the number of inductive hypotheses
 *)
let rec num_ihs env rec_typ typ =
  match kind typ with
  | Prod (n, t, b) ->
     if is_or_applies rec_typ (reduce_term env t) then
       let (n_b_t, b_t, b_b) = destProd b in
       1 + num_ihs (push_local (n, t) (push_local (n_b_t, b_t) env)) rec_typ b_b
     else
       num_ihs (push_local (n, t) env) rec_typ b
  | _ ->
     0

(* 
 * Flip the direction of a lifting
 *)
let flip_dir l = { l with is_fwd = (not l.is_fwd) }

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
  let typ_args = non_index_typ_args l env evd arg in
  let orn_app = mkAppl (orn, snoc arg typ_args) in
  let app_red = reduce_nf env trm in
  let orn_app_red = reduce_nf env orn_app in
  let app_red_ex = dest_existT app_red in
  let orn_app_red_ex = dest_existT orn_app_red in
  let abstract = abstract_arg env evd (Option.get l.orn.index_i) in
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
  let typ_args = non_index_typ_args l env evd arg in
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

(* --- Lifting the induction principle --- *)

(*
 * This implements LIFT-ELIM. The one discrepency here is that,
 * as described in Section 5.2, Coq doesn't have primitive eliminators.
 * Because of this, we can't simply recursively lift the type we eliminate over;
 * we need to get the arguments to the induction principle by hand.
 * This is what the additional LIFT-ELIM-ARGS rule does. 
 *)
                  
(*
 * LIFT-ELIM-ARGS
 *)
let lift_elim_args env evd l index_i args =
  let arg = map_backward last_arg l (last args) in
  let typ_args = non_index_typ_args l env evd arg in
  let lifted_arg = mkAppl (lift_to l, snoc arg typ_args) in
  let value_i = List.length args - 1 in
  if l.is_fwd then
    let lifted_arg_sig = on_type dest_sigT env evd lifted_arg in
    let index = project_index lifted_arg_sig lifted_arg in
    let value = project_value lifted_arg_sig lifted_arg in
    insert_index index_i index (reindex value_i value args)
  else
    remove_index index_i (reindex value_i lifted_arg args)

(* 
 * PROMOTE-MOTIVE and FORGET-MOTIVE
 *)
let lift_motive env evd l index_i parameterized_elim motive =
  let parameterized_elim_type = reduce_type env evd parameterized_elim in
  let (_, to_motive_typ, _) = destProd parameterized_elim_type in
  let env_to_motive = zoom_env zoom_product_type env to_motive_typ in
  let off = offset2 env_to_motive env in
  let motive = shift_by off motive in
  let args = mk_n_rels off in
  let lifted_arg = pack_lift env_to_motive evd (flip_dir l) (last args) in
  let value_i = off - 1 in
  if l.is_fwd then
    (* PROMOTE-MOTIVE *)
    let args = remove_index index_i (reindex value_i lifted_arg args) in
    let motive_app = reduce_term env_to_motive (mkAppl (motive, args)) in
    reconstruct_lambda_n env_to_motive motive_app (nb_rel env)
  else
    (* FORGET-MOTIVE *)
    let lifted_arg_sig = on_type dest_sigT env_to_motive evd lifted_arg in
    let index = project_index lifted_arg_sig lifted_arg in
    let value = project_value lifted_arg_sig lifted_arg in
    let args = insert_index index_i index (reindex value_i value args) in 
    let motive_app = reduce_term env_to_motive (mkAppl (motive, args)) in
    reconstruct_lambda_n env_to_motive motive_app (nb_rel env)

(* PROMOTE-CASE-ARGS, part of LIFT-CASE-ARGS *)
let promote_case_args env evd l (_, to_typ) args =
  let index_i = Option.get l.orn.index_i in
  let rec lift_args args index =
    match args with
    | h :: tl ->
       if equal h index then
         shift h :: (lift_args (shift_all tl) index)
       else
         let h_typ = reduce_type env evd h in
         if is_or_applies to_typ h_typ then
           let h_lifted = pack_lift env evd (flip_dir l) h in
           h_lifted :: lift_args tl (get_arg index_i h_typ)
         else
           h :: lift_args tl index
    | _ -> []
  in lift_args args (mkRel 0)

(* PROMOTE-CASE-ARGS, part of LIFT-CASE-ARGS *)
let forget_case_args env_c_b env evd l (from_typ, _) args =
  let index_i = Option.get l.orn.index_i in
  let rec lift_args args (index, proj_index) =
    match args with
    | h :: tl ->
       if equal h index then
         proj_index :: (lift_args (unshift_all tl) (index, proj_index))
       else
         let h_typ = reduce_type env_c_b evd h in
         if is_or_applies from_typ h_typ then
           let h_lifted =  pack_lift env evd (flip_dir l) h in
           let h_lifted_typ = on_type dest_sigT env evd h_lifted in
           let proj_value = project_value h_lifted_typ h_lifted in
           let proj_index = project_index h_lifted_typ h_lifted in
           proj_value :: lift_args tl (get_arg index_i h_typ, proj_index)
         else
           h :: lift_args tl (index, proj_index)
    | _ -> []
  in lift_args args (mkRel 0, mkRel 0)
           
(* LIFT-CASE-ARGS, an auxiliary function for LIFT-CASE *)
let lift_case_args env_c_b env evd l (from_typ, to_typ) args =
  let lifter =
    if l.is_fwd then
      promote_case_args
    else
      forget_case_args env_c_b
  in List.rev (lifter env evd l (from_typ, to_typ) (List.rev args))
                         
(* 
 * PROMOTE-CASE and FORGET-CASE
 *)
let lift_case env evd l (from_typ, to_typ) p c_elim c =
  let c_eta = expand_eta env evd c in
  let c_elim_type = reduce_type env evd c_elim in
  let (_, to_c_typ, _) = destProd c_elim_type in
  let nihs = num_ihs env to_typ to_c_typ in
  if nihs = 0 then
    c (* base case, don't bother *)
  else
    let env_c = zoom_env zoom_product_type env to_c_typ in
    let off = offset2 env_c env in
    let c_eta = shift_by off c_eta in
    let (env_c_b, c_body) = zoom_lambda_term env_c c_eta in
    let (c_f, c_args) = destApp c_body in
    let split_i = if l.is_fwd then off - nihs else off + nihs in
    let (c_args, b_args) = take_split split_i (Array.to_list c_args) in
    let c_args = unshift_all_by (List.length b_args) c_args in
    let lift_args = lift_case_args env_c_b env_c evd l (from_typ, to_typ) in
    let c_to_args = lift_args c_args in
    let c_to_f = unshift_by (offset2 env_c_b env_c) c_f in
    let c_to_body = reduce_term env_c (mkAppl (c_to_f, c_to_args)) in
    reconstruct_lambda_n env_c c_to_body (nb_rel env)
                         
(* Lift cases *)
let lift_cases env evd l (from_typ, to_typ) p p_elim cs =
  snd
    (List.fold_left
       (fun (p_elim, cs) c ->
         let c = lift_case env evd l (from_typ, to_typ) p p_elim c in
         let p_elim = mkAppl (p_elim, [c]) in
         (p_elim, snoc c cs))
       (p_elim, [])
       cs)

(*
 * LIFT-ELIM steps before recursing into the rest of the algorithm
 *)
let lift_elim env evd l trm_app =
  let to_typ = zoom_sig (promotion_type env evd l.orn.forget) in
  let from_typ = first_fun (promotion_type env evd l.orn.promote) in
  let (from_typ, to_typ) = map_backward reverse l (from_typ, to_typ) in
  let index_i = (Option.get l.orn.index_i) - (List.length trm_app.pms) in
  let elim = type_eliminator env (fst (destInd to_typ)) in
  let param_elim = mkAppl (elim, trm_app.pms) in
  let p = lift_motive env evd l index_i param_elim trm_app.p in
  let p_elim = mkAppl (param_elim, [p]) in
  let cs = lift_cases env evd l (from_typ, to_typ) p p_elim trm_app.cs in
  let final_args = lift_elim_args env evd l index_i trm_app.final_args in
  apply_eliminator {trm_app with elim; p; cs; final_args}

(* --- Lifting constructions --- *)

(*
 * LIFT-CONSTR-ARGS and LIFT-CONSTR-FUN, but using refolding,
 * as explained in Section 5
 *)

(* 
 * LIFT-CONSTR-ARGS & LIFT-CONSTR-FUN
 *)
let lift_constr_core env evd l (from_typ, to_typ) trm =
  let typ_args = non_index_typ_args l env evd trm in
  let args =
    map_backward
      (List.map
         (fun a ->
           if on_type (is_or_applies to_typ) env evd a then
             pack env evd l a
           else
             a))
      l
      (unfold_args (map_backward last_arg l trm))
  in   
  let rec_args = filter_orn l env evd (from_typ, to_typ) args in
  let orn = lift_to l in
  let orn_app = lift env evd l trm in
  (* let orn_app = mkAppl (orn, snoc trm typ_args) in *)
  if List.length rec_args = 0 then
    (* base case - don't bother refolding *)
    reduce_nf env orn_app
  else
    (* inductive case - refold *)
    List.fold_left
      (fun t a ->
        let a_typ_args = non_index_typ_args l env evd a in
        all_eq_substs (a, mkAppl (orn, snoc a a_typ_args)) t)
      (refold l env evd orn orn_app rec_args)
rec_args
    
(*
 * Lift a construction, which in the forward direction is an application
 * of a constructor, and in the backward direction is an application
 * of a constructor inside of an existential. This assumes the input
 * term is fully eta-expanded and that it is not applied to any extra
 * arguments at the end (though I think that's not actually possible anyways).
 *
 * This looks slightly different because we use the refolding algorithm
 * to derive the constructor rules, as described in Section 5 of the paper.
 *
 * As in the paper, the arguments are recursively lifted by the higher
 * lifting algorithm.
 *)
let lift_constr env evd l trm =
  (* LIFT-CONSTR *)
  let to_typ = zoom_sig (promotion_type env evd l.orn.forget) in
  let from_typ = first_fun (promotion_type env evd l.orn.promote) in
  let inner_construction = map_backward last_arg l trm in
  let constr = first_fun inner_construction in
  let args = unfold_args inner_construction in
  let (env_c_b, c_body) = zoom_lambda_term env (expand_eta env evd constr) in
  let c_body = reduce_term env_c_b c_body in
  let to_refold = map_backward (pack env_c_b evd l) l c_body in
  let refolded = lift_constr_core env_c_b evd l (from_typ, to_typ) to_refold in
  let lifted_constr = reconstruct_lambda_n env_c_b refolded (nb_rel env) in
  reduce_term env (mkAppl (lifted_constr, args))
  
(* --- Core lifting --- *)

let type_is_orn l env evd (from_type, to_type) trm =
  on_type (is_orn l env evd (from_type, to_type)) env evd trm
             
let is_packed_constr l env evd (from_type, to_type) trm =
  let right_type = type_is_orn l env evd (from_type, to_type) in
  match kind trm with
  | Construct _  when right_type trm ->
     true
  | App (f, args) ->
     if l.is_fwd then
       isConstruct f && right_type trm
     else
       if equal existT f && right_type trm then
         let last_arg = last (Array.to_list args) in
         isApp last_arg && isConstruct (first_fun last_arg)
       else
         false
  | _ ->
     false

let is_packed l env evd (from_type, to_type) trm =
  let right_type = type_is_orn l env evd (from_type, to_type) in
  if l.is_fwd then
    false
  else
    match kind trm with
    | App (f, args) ->
       equal existT f && right_type trm
    | _ ->
       false

let is_proj l env evd (from_type, to_type) trm =
  let right_type = type_is_orn l env evd (from_type, to_type) in
  match kind trm with
  | App (f, args) ->
     if l.is_fwd then
       equal (Option.get l.orn.indexer) f && right_type (last_arg trm)
     else
       (equal projT1 f || equal projT2 f) && right_type (last_arg trm)
  | _ ->
     false

let is_eliminator l env evd (from_type, to_type) trm =
  match kind trm with
  | App (f, args) when isConst f ->
     let maybe_ind = inductive_of_elim env (destConst f) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       equal (mkInd (ind, 0)) (directional l from_type to_type)
     else
       false
  | _ ->
     false
             
(*
 * TODO comment/in progress (hooking in new alg.)
 * TODO explain differences and also guarantees (so while fix/cofix/match etc. 
 * exist to handle more terms, they just recurse naively, and so might fail
 * on terms that refer to the type you're lifting)
 * TODO for now, ignores the is_indexer option/assumes it never happens
 * TODO need to think through where we need eta more / test that
 * TODO error handling
 * TODO efficiency
 *)
let lift_core env evd l (from_type, to_type) index_type trm =
  let index_i = Option.get l.orn.index_i in
  let rec lift en index_type tr =
    let lifted_opt = search_lifted en tr in
    if Option.has_some lifted_opt then
      (* CACHING *)
      Option.get lifted_opt
    else if is_orn l en evd (from_type, to_type) tr then
      (* EQUIVALENCE *)
      let tr = reduce_nf en tr in
      if l.is_fwd then
        let t_args = unfold_args tr in
        let app = mkAppl (to_type, t_args) in
        let index = mkRel 1 in
        let abs_i = reindex_body (reindex_app (insert_index index_i index)) in
        let packer = abs_i (mkLambda (Anonymous, index_type, shift app)) in
        pack_sigT { index_type ; packer }
      else
        let packed = dummy_index en (dest_sigT tr).packer in
        let t_args = remove_index index_i (unfold_args packed) in
        mkAppl (from_type, t_args)
    else if is_packed_constr l en evd (from_type, to_type) tr then
      (* LIFT-CONSTR *)
      let tr' = lift_constr en evd l tr in
      match kind tr with
      | App (f, args) ->
         if (not l.is_fwd) && isApp (last (Array.to_list args)) then
           let (f', args') = destApp tr' in
           mkApp (f', Array.map (lift en index_type) args')
         else if l.is_fwd then
           let ex = dest_existT tr' in
           let (f', args') = destApp ex.unpacked in
           let index = lift en index_type ex.index in
           let unpacked = mkApp (f', Array.map (lift en index_type) args') in
           pack_existT { ex with index; unpacked }
         else
           tr'
      | _ ->
         tr'
    else if is_packed l en evd (from_type, to_type) tr then
      (* LIFT-PACK *)
      lift en index_type (dest_existT tr).unpacked
    else if is_proj l en evd (from_type, to_type) tr then
      (* LIFT-PROJECT *)
      let arg' = lift en index_type (last_arg tr) in
      if l.is_fwd then
        let arg_typ' = dest_sigT (lift en index_type (reduce_type en evd tr)) in
        project_index arg_typ' arg'
      else if equal projT1 (first_fun tr) then
        let indexer = Option.get l.orn.indexer in
        mkAppl (indexer, snoc arg' (non_index_typ_args l en evd tr))
      else 
        arg'
    else if is_eliminator l en evd (from_type, to_type) tr then
      (* LIFT-ELIM *)
      let tr_elim = deconstruct_eliminator en evd tr in
      let npms = List.length tr_elim.pms in
      let value_i = arity (expand_eta env evd from_type) - npms in (* may be off by 1 *)
      let (final_args, post_args) = take_split (value_i + 1) tr_elim.final_args in
      let tr' = lift_elim en evd l { tr_elim with final_args } in
      let tr'' = lift en index_type tr' in
      let post_args' = List.map (lift en index_type) post_args in
      mkAppl (tr'', post_args')
    else
      match kind tr with
      | App (f, args) ->
         if equal (lift_back l) f then
           (* SECTION-RETRACTION *)
           last_arg tr
         else if equal (lift_to l) f then
           (* INTERNALIZE *)
           lift en index_type (last_arg tr)
         else
           (* APP *)
           let args' = Array.map (lift en index_type) args in
           let f' = lift en index_type f in
           mkApp (f', args')
      | Cast (c, k, t) ->
         (* CAST *)
         let c' = lift en index_type c in
         let t' = lift en index_type t in
         mkCast (c', k, t')
      | Prod (n, t, b) ->
         (* PROD *)
         let t' = lift en index_type t in
         let en_b = push_local (n, t) en in
         let b' = lift en_b (shift index_type) b in
         mkProd (n, t', b')
      | Lambda (n, t, b) ->
         (* LAMBDA *)
         let t' = lift en index_type t in
         let en_b = push_local (n, t) en in
         let b' = lift en_b (shift index_type) b in
         mkLambda (n, t', b')
      | LetIn (n, trm, typ, e) ->
         (* LETIN *)
         let trm' = lift en index_type trm in
         let typ' = lift en index_type typ in
         let en_e = push_let_in (n, e, typ) en in
         let e' = lift en_e (shift index_type) e in
         mkLetIn (n, trm', typ', e')
      | Case (ci, ct, m, bs) ->
         (* CASE *)
         let ct' = lift en index_type ct in
         let m' = lift en index_type m in
         let bs' = Array.map (lift en index_type) bs in
         mkCase (ci, ct', m', bs')
      | Fix ((is, i), (ns, ts, ds)) ->
         (* FIX *)
         let ts' = Array.map (lift en index_type) ts in
         let ds' = Array.map (map_rec_env_fix lift shift en index_type ns ts) ds in
         mkFix ((is, i), (ns, ts', ds'))
      | CoFix (i, (ns, ts, ds)) ->
         (* COFIX *)
         let ts' = Array.map (lift en index_type) ts in
         let ds' = Array.map (map_rec_env_fix lift shift en index_type ns ts) ds in
         mkCoFix (i, (ns, ts', ds'))
      | Proj (pr, c) ->
         (* PROJ *)
         let c' = lift en index_type c in
         mkProj (pr, c')
      | Construct (((i, i_index), _), u) ->
         let ind = mkInd (i, i_index) in
         if equal ind (directional l from_type to_type) then
           (* lazy eta expansion *)
           lift en index_type (expand_eta en evd tr)
         else
           tr
      | Const _ ->
         (* CONST *)
         if equal tr projT1 || equal tr projT2 || is_elim en tr then
           tr
         else
           (try
              let def = lookup_definition en tr in
              let lifted = lift en index_type def in
              if equal def lifted then
                tr
              else
                reduce_term en lifted (* TODO cache, but only when relevant *)
            with _ ->
              tr)
      | _ ->
         (* TODO expand more eta for project, type, etc *)
         tr
  in lift env index_type trm

(*
 * TODO comment/in progress (hooking in new alg.)
 *)
let do_lift_core env evd (l : lifting) def =
  let trm = unwrap_definition env def in
  let promotion_type en t = fst (on_type ind_of_promotion_type en evd t) in
  let forget_typ = promotion_type env l.orn.forget in
  let promote_typ = promotion_type env l.orn.promote in
  let typs = (first_fun promote_typ, zoom_sig forget_typ) in
  let index_type = (dest_sigT forget_typ).index_type in
  lift_core env evd l typs index_type trm
