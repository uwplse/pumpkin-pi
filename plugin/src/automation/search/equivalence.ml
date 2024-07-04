open Util
open Constr
open Names
open Environ
open Utilities
open Debruijn
open Indexing
open Substitution
open Factoring
open Zooming
open Lifting
open Hypotheses
open Specialization
open Inference
open Typehofs
open Indutils
open Envutils
open Reducers
open Apputils
open Equtils
open Contextutils
open Sigmautils
open Stateutils
open Declarations
open Promotion
open Ornerrors
open Libnames
open Nametab

(*
 * Automatically generated equivalence proofs
 *)
       
(* --- Common code --- *)

(*
 * Construct the motive for section/retraction
 *)
let equiv_motive env_motive pms l is_packed sigma =
  let sigma, trm1 =
    if is_packed then
      pack env_motive l (mkRel 1) sigma
    else
      sigma, mkRel 1
  in
  let sigma, at_type = reduce_type env_motive sigma trm1 in
  let typ_args =
    match l.orn.kind with
    | Algebraic (_, off) ->
       non_index_args off env_motive sigma at_type
    | CurryRecord ->
       pms
    | SwapConstruct _ ->
       unfold_args at_type
    | _ ->
       failwith "not supported"
  in
  let trm1_lifted = mkAppl (lift_to l, snoc trm1 typ_args) in
  let trm2 = mkAppl (lift_back l, snoc trm1_lifted typ_args) in
  let p_b = apply_eq { at_type; trm1; trm2 } in
  sigma, shift (reconstruct_lambda_n env_motive p_b (List.length pms))

(*
 * The proofs of both section and retraction for algebraic ornaments
 * and constructor swapping apply lemmas  that show that equalities are
 * preserved in inductive cases. These lemmas are folds over substitutions of
 * recursive arguments, with refl as identity.
 *
 * The first step to constructing these is to construct the environment
 * with the appropriate hypotheses for these lemmas:
 *)
let eq_lemmas_env env recs l pack_typ pack_trm =
  fold_left_state
    (fun e r sigma ->
      let r1 = shift_by (new_rels2 e env) r in
      let sigma, r_t = reduce_type e sigma r1 in
      (* if applicable, pack the type *)
      let sigma, (e_ib, r_t) = pack_typ e r_t sigma in
      (* push new rec arg *)
      let e_r = push_local (Anonymous, r_t) e_ib in
      (* get the (possibly packed) equality type *)
      let sigma, r1 = pack_trm e_r (shift_by (new_rels2 e_r e) r1) sigma in
      let sigma, r2 = pack_trm e_r (mkRel 1) sigma in
      let sigma, r_t = reduce_type e_r sigma r1 in
      let r_eq = apply_eq {at_type = r_t; trm1 = r1; trm2 = r2} in
      (* push the equality *)
      sigma, push_local (Anonymous, r_eq) e_r)
    env
    recs

(*
 * Then, we prove the equality lemmas:
 *)
let eq_lemmas env typ l pack_typ pack_trm nindices abstract_c_app sub_c_app_trans sigma =
  let ((i, i_index), u) = destInd typ in
  map_state_array
    (fun c_index sigma ->
      let c = mkConstructU (((i, i_index), c_index + 1), u) in
      let sigma, c_exp = expand_eta env sigma c in
      let (env_c_b, c_body) = zoom_lambda_term env c_exp in
      let c_body = reduce_stateless reduce_term env_c_b sigma c_body in
      let c_args = unfold_args c_body in
      let recs = List.filter (on_red_type_default (ignore_env (is_or_applies typ)) env_c_b sigma) c_args in
      let sigma, env_lemma = eq_lemmas_env env_c_b recs l pack_typ pack_trm sigma in
      let sigma, c_body = pack_trm env_lemma (shift_by (new_rels2 env_lemma env_c_b) c_body) sigma in
      let sigma, c_body_type = reduce_type env_lemma sigma c_body in
      (* reflexivity proof: the identity case *)
      let refl = apply_eq_refl { typ = c_body_type; trm = c_body } in
      let (body, _, _) =
        List.fold_right
          (fun _ (b, h, c_app) ->
            (* fold to recursively substitute each recursive argument *)
            let h_r = destRel h in
            let (_, _, h_t) = CRD.to_tuple @@ lookup_rel h_r env_lemma in
            let app = dest_eq (shift_by h_r h_t) in
            let at_type = app.at_type in
            let r1 = app.trm1 in
            let r2 = app.trm2 in
            let c_body_b = shift c_body in
            let c_app_b = shift c_app in
            let abs_c_app = abstract_c_app (r1, r2) at_type c_app_b in
            let c_app_trans = sub_c_app_trans (r1, r2) c_app in
            let typ_b = shift c_body_type in
            let p_b = { at_type = typ_b; trm1 = c_body_b; trm2 = abs_c_app } in
            let p = mkLambda (get_rel_ctx_name Anonymous, at_type, apply_eq p_b) in
            let eq_proof_app = {at_type; p; trm1 = r1; trm2 = r2; h; b} in
            let eq_proof = apply_eq_ind eq_proof_app in
            (eq_proof, shift_by (2 + nindices) h, c_app_trans))
          recs
          (refl, mkRel 1, c_body)
      in sigma, reconstruct_lambda env_lemma body)
    (Array.mapi
       (fun i _ -> i)
       ((lookup_mind i env).mind_packets.(i_index)).mind_consnames)
    sigma

(*
 * Get a case of the proof of section/retraction
 * Take as arguments an environment, an evar_map, the parameters,
 * the motive of the section/retraction proof, the equality lemma for the case,
 * the type of the eliminator corresponding to the case, and a lifting config.
 *
 * The inner function works by tracking a list of regular hypotheses
 * and new arguments for the equality lemma, then applying them in the body.
 *)
let equiv_case env pms p eq_lemma l c dest_term sigma =
  let eq_lemma = mkAppl (eq_lemma, pms) in (* curry eq_lemma with pms *)
  let rec case e depth hypos args c =
    match kind c with
    | App (_, _) ->
       (* conclusion: apply eq lemma and beta-reduce *)
       let all_args = List.rev_append hypos (List.rev args) in
       reduce_stateless reduce_term e sigma (mkAppl (shift_by depth eq_lemma, all_args))
    | Prod (n, t, b) ->
       let case_b = case (push_local (n.binder_name, t) e) (shift_i depth) in
       let p_rel = shift_by depth (mkRel 1) in
       let h = mkRel 1 in
       if applies p_rel t then
         (* IH *)
         let t = reduce_stateless reduce_term e sigma (mkAppl (shift_by depth p, unfold_args t)) in
         let trm = (dest_eq t).trm2 in
         let args = List.rev_append (dest_term e trm sigma) args in
         mkLambda (n, t, case_b (shift_all hypos) (h :: shift_all args) b)
       else
         (* Product *)
         mkLambda (n, t, case_b (h :: shift_all hypos) (shift_all args) b)
    | _ ->
       failwith "unexpected case"
  in case env 0 [] [] c

(*
 * Get the cases of the proof of section/retraction
 * Take as arguments the environment with the motive type pushed,
 * an evar_map, the parameters, the motive, the equality lemmas,
 * the lifting, and the type of the eliminator body after the motive
 *)
let equiv_cases equiv_case env pms p lemmas l elim_typ sigma =
  List.mapi
    (fun j c -> equiv_case env pms p lemmas.(j) l c sigma)
    (take (Array.length lemmas) (factor_product elim_typ))

(*
 * Prove section/retraction for either algebraic ornaments or
 * swapping/renaming constructors
 *)
let equiv_proof eq_lemmas equiv_case is_packed unpack_env index_args unpack_eq_proof env l sigma =
  let to_body = lookup_definition env (lift_to l) in
  let env_to = zoom_env zoom_lambda_term env to_body in
  let sigma, typ_app = reduce_type env_to sigma (mkRel 1) in
  let typ = first_fun (zoom_if_sig_app typ_app) in
  let ((i, i_index), _) = destInd typ in
  let npm = (lookup_mind i env).mind_nparams in
  let nargs = new_rels env_to npm in
  let sigma, lemmas = eq_lemmas env typ l sigma in (* equality lemmas *)
  let env_eq_proof = unpack_env env_to typ_app in
  let elim = type_eliminator env_to (i, i_index) in
  let sigma, elim_typ = infer_type env sigma elim in
  let (env_pms, elim_typ_p) = zoom_n_prod env npm elim_typ in
  let (n, p_t, elim_typ) = destProd elim_typ_p in
  let env_p = push_local (n.binder_name, p_t) env_pms in
  let pms = shift_all (mk_n_rels npm) in
  let env_motive = zoom_env zoom_product_type env_pms p_t in
  let sigma, p = equiv_motive env_motive pms l is_packed sigma in
  let cs = equiv_cases equiv_case env_p pms p lemmas l elim_typ sigma in
  let args = shift_all_by (new_rels2 env_eq_proof env_to) (mk_n_rels nargs) in
  let final_args = index_args npm args in
  let depth = new_rels2 env_eq_proof env_p in
  let eq_proof =
    apply_eliminator
      {
        elim;
        pms = shift_all_by depth pms;
        p = shift_by depth p;
        cs = shift_all_by depth cs;
        final_args;
      }
  in
  let eq_typ = on_red_type_default (ignore_env dest_eq) env_eq_proof sigma eq_proof in
  let packed = reconstruct_lambda_n env_eq_proof eq_proof (nb_rel env_to) in
  let eq_proof_unpacked = unpack_eq_proof env_to typ_app eq_typ packed in
  let eq_typ = on_red_type_default (ignore_env dest_eq) env_to sigma eq_proof_unpacked in
  let equiv_b = apply_eq_sym { eq_typ; eq_proof = eq_proof_unpacked } in
  let trm = reconstruct_lambda env_to equiv_b in
  let sigma, typ = reduce_type env sigma trm in
  trm, typ

(* --- Algebraic ornaments  --- *)

(*
 * To construct these proofs, we first construct the lemmas, then
 * specialize them to the appropriate arguments.
 *
 * We construct the lemmas by calling the generic method, with some
 * special HOFs for packing indices in the backward case.
 *)
let eq_lemmas_algebraic env typ l =
  match l.orn.kind with
  | Algebraic (_, off) ->
     if l.is_fwd then
       eq_lemmas
         env
         typ
         l
         (fun env typ -> ret (env, typ)) (* no packing types *)
         (fun _ trm -> ret trm) (* no packing terms *)
         0 (* no indices *)
         (fun (r1, r2) _ -> all_eq_substs (shift r1, mkRel 1)) (* no packing *)
         all_eq_substs (* basic substitution *)
     else
       eq_lemmas
         env
         typ
         l
         (fun env typ sigma ->
           (* push index for packing in backward direction *)
           let sigma, env_ib =
             Util.on_snd
               (fun t -> push_local (Anonymous, t) env)
               (reduce_type env sigma (get_arg off typ))
           in sigma, (env_ib, reindex_app (reindex off (mkRel 1)) (shift typ)))
         (fun env -> pack env l) (* pack terms *)
         1 (* one index *)
         (fun (r1, r2) at_type c_app_b ->
           (* abstract both indices and values *)
           let (r1_ex, r2_ex) = map_tuple dest_existT (r1, r2) in
           let r1_u = r1_ex.unpacked in
           let r1_ib = r1_ex.index in
           let b_sig_typ = dest_sigT (shift at_type) in
           let (ib, u) = projections b_sig_typ (mkRel 1) in
           let abs_c_app_u = all_eq_substs (shift r1_u, u) c_app_b in
           all_eq_substs (shift r1_ib, ib) abs_c_app_u)
         (fun (r1, r2) c_app ->
           (* substitute both indices and values *)
           let (r1_ex, r2_ex) = map_tuple dest_existT (r1, r2) in
           let r1_u = r1_ex.unpacked in
           let r2_u = r2_ex.unpacked in
           let r1_ib = r1_ex.index in
           let r2_ib = r2_ex.index in
           let c_app_trans_u = all_eq_substs (r1_u, r2_u) c_app in
           all_eq_substs (r1_ib, r2_ib) c_app_trans_u)
  | _ ->
     raise NotAlgebraic
        
(*
 * Get a case of the proof of section/retraction
 * Take as arguments an environment, an evar_map, the parameters,
 * the motive of the section/retraction proof, the equality lemma for the case,
 * the type of the eliminator corresponding to the case, and a lifting config.
 *
 * The inner function works by tracking a list of regular hypotheses
 * and new arguments for the equality lemma, then applying them in the body.
 *)
let equiv_case_algebraic env pms p eq_lemma l c =
  equiv_case
    env
    pms
    p
    eq_lemma
    l
    c
    (fun env trm sigma ->
      if l.is_fwd then
        (* nothing to project *)
        [trm]
      else
        (* project index and value *)
        let (ib, u) = projections (on_red_type_default (ignore_env dest_sigT) env sigma trm) trm in
        [ib; u])

(*
 * Prove section/retraction for an algebraic ornament
 *)
let equiv_proof_algebraic env l =
  match l.orn.kind with
  | Algebraic (_, off) ->
     if l.is_fwd then
       equiv_proof
         eq_lemmas_algebraic
         equiv_case_algebraic
         false
         (fun env _ -> env)
         (fun _ args -> args)
         (fun _ _ _ eq_proof -> eq_proof)
         env
         l
     else
       equiv_proof
         eq_lemmas_algebraic
         equiv_case_algebraic
         true (* new index for retraction *)
         (fun env typ_app ->
           (* unpack env for retraction *)
           let b_sig_typ = dest_sigT typ_app in
           let ib_typ = b_sig_typ.index_type in
           let env_ib = push_local (Anonymous, ib_typ) env in
           let b_typ = mkAppl (shift b_sig_typ.packer, [mkRel 1]) in
           push_local (Anonymous, b_typ) env_ib)
         (fun npm args ->
           (* reindex the args for retraction *)
           let index_back = insert_index (off - npm) (mkRel 2) in
           let reindex_back = reindex (List.length args) (mkRel 1) in
           reindex_back (index_back args))
         (fun env typ_app eq_typ eq_proof ->
           let env_p = push_local (Anonymous, typ_app) env in
           let trm2 = unshift (all_eq_substs (eq_typ.trm1, mkRel 2) eq_typ.trm2) in
           let at_type = shift typ_app in
           let p_b = apply_eq { at_type; trm1 = mkRel 1; trm2 } in
           let p = reconstruct_lambda_n env_p p_b (nb_rel env) in
           let to_elim = dest_sigT typ_app in
           elim_sigT { to_elim; packed_type = p; unpacked = eq_proof; arg = mkRel 1 })
         env
         l
  | _ ->
     raise NotAlgebraic

(* --- Swap Constructor --- *)

(*
 * This looks very similar to algebraic, except that it swaps constructors
 * in the appropriate places, and has no packing/unpacking since the number
 * of indices does not change. First we get the equality lemmas:
 *)
let eq_lemmas_swap env typ l =
  eq_lemmas
    env
    typ
    l
    (fun env typ -> ret (env, typ)) (* no packing types *)
    (fun _ trm -> ret trm) (* no packing terms *)
    0 (* no indices *)
    (fun (r1, r2) _ -> all_eq_substs (shift r1, mkRel 1)) (* no packing *)
    all_eq_substs (* basic substitution *)

(*
 * Get a case of section/retraction
 *)
let equiv_case_swap env pms p eq_lemma l c =
  equiv_case env pms p eq_lemma l c (fun _ trm _ -> [trm])

(*
 * Prove section/retraction for swapping constructors
 *)
let equiv_proof_swap =
  equiv_proof
    eq_lemmas_swap
    equiv_case_swap
    false
    (fun env _ -> env)
    (fun _ args -> args)
    (fun _ _ _ eq_proof -> eq_proof)
                     
(* --- Curry record --- *)

(*
 * Get the body of the section/retraction proof for curry record
 *
 * In the forward case, this eliminates over the inductive type.
 * In the backward case, this recursively eliminates over product types,
 * until there are no more nested pairs to eliminate.
 *
 * This looks different from algebraic ornaments and swapping constructors,
 * mostly due to the need to recursively eliminate over products.
 *)
let equiv_proof_body_curry_record env_to sigma p pms l =
  let arg = mkRel 1 in
  let sigma, typ_app =
    map_backward
      (fun (sigma, typ_app) ->
        let f = unwrap_definition env_to (first_fun typ_app) in
        reduce_term env_to sigma (mkAppl (f, unfold_args typ_app)))
      l
      (reduce_type env_to sigma arg)
  in
  if l.is_fwd then
    let ((i, i_index), u) = destInd (first_fun typ_app) in
    let cs =
      let c = mkConstructU (((i, i_index), 1), u) in
      let sigma, c_exp = expand_eta env_to sigma c in
      let (env_c_b, c_body) = zoom_lambda_term env_to c_exp in
      let c_body = reduce_stateless reduce_term env_c_b sigma c_body in
      let sigma, c_body_type = reduce_type env_c_b sigma c_body in
      let refl = apply_eq_refl { typ = c_body_type; trm = c_body } in
      [shift (reconstruct_lambda_n env_c_b refl (nb_rel env_to + (List.length pms)))]
    in
    let elim = type_eliminator env_to (i, i_index) in
    sigma, apply_eliminator
      {
        elim;
        pms;
        p;
        cs;
        final_args = [arg];
      }
  else
    let open Produtils in
    let rec build_proof env pms at_type to_elim arg =
      let (typ1, typ2) as typs = (to_elim.typ1, to_elim.typ2) in
      let env_proof = push_local (Anonymous, shift typ2) (push_local (Anonymous, typ1) env) in
      let (typ1, typ2) as typs = map_tuple (shift_by 2) typs in
      let at_type = shift_by 2 at_type in
      let pms = shift_all_by 2 pms in
      let curr = mkRel 1 in
      let arg = all_eq_substs (mkRel 3, apply_pair { typ1; typ2; trm1 = mkRel 2; trm2 = curr }) (shift_by 2 arg) in
      let proof_body =
        if equal prod (first_fun typ2) then
          let to_elim = dest_prod typ2 in
          let p =
            let pms = shift_all pms in
            let arg_abs = all_eq_substs (shift curr, curr) (shift arg) in
            let trm2 = mkAppl (lift_back l, snoc (mkAppl (lift_to l, snoc arg_abs pms)) pms) in
            mkLambda (get_rel_ctx_name Anonymous, typ2, apply_eq { at_type = shift at_type; trm1 = arg_abs; trm2 })
          in
          let proof = build_proof env_proof pms at_type to_elim arg in
          elim_prod { to_elim; p; proof; arg = curr }
        else
          let arg_pair = dest_pair arg in
          let typ = apply_prod { typ1 = arg_pair.typ1; typ2 = arg_pair.typ2 } in
          apply_eq_refl { typ; trm = arg }
      in reconstruct_lambda_n env_proof proof_body (nb_rel env)
    in
    let to_elim = dest_prod typ_app in
    let proof = build_proof env_to pms typ_app to_elim arg in
    sigma, elim_prod { to_elim; p; proof; arg }
  
(*
 * Prove section/retraction for curry record
 *)
let equiv_proof_curry_record env l sigma =
  let to_body = lookup_definition env (lift_to l) in
  let env_to = zoom_env zoom_lambda_term env to_body in
  let npm = nb_rel env_to - 1 in
  let pms = shift_all (mk_n_rels npm) in
  let sigma, p = equiv_motive env_to pms l false sigma in
  let sigma, eq_proof = equiv_proof_body_curry_record env_to sigma p pms l in
  let eq_typ = on_red_type_default (ignore_env dest_eq) env_to sigma eq_proof in
  let equiv_b = apply_eq_sym { eq_typ; eq_proof } in
  let trm = reconstruct_lambda env_to equiv_b in
  let sigma, typ = reduce_type env sigma trm in
  trm, typ

(* --- Equivalence proofs for unpack sigma --- *)

(*
 * Much like search, this simply instantiates more general equivalences
 * to specific types
 *)

(*
 * Generic section proof
 *)
let unpack_section () =
  let n = qualid_of_string "Ornamental.Equivalences.unpack_generic_section" in
  mkConst (locate_constant n)

(*
 * Generic retraction proof
 *)
let unpack_retraction () =
  let n = qualid_of_string "Ornamental.Equivalences.unpack_generic_retraction" in
  mkConst (locate_constant n)

(*
 * Prove section/retraction for unpack
 *)
let equiv_proof_unpack env l sigma =
  let directional x y = if l.is_fwd then x else y in
  let f = (directional unpack_section unpack_retraction) () in
  let sigma, (env_args, args) =
    let sigma, forget_typ = reduce_type env sigma l.orn.forget in
    let env_b_sig_eq, b_sig_eq = zoom_product_type env forget_typ in
    let sigma, args = unpack_typ_args env_b_sig_eq b_sig_eq sigma in
    let env_args = pop_rel_context 1 env_b_sig_eq in
    sigma, (env_args, unshift_all args)
  in
  let sigma, app = reduce_term env sigma (mkAppl (f, args)) in
  let trm = reconstruct_lambda env_args app in
  let sigma, typ =
    (* The default inferred type is not very good, so we guide Coq *)
    let sigma, (env_eq, eq) =
      let sigma, (env_eq, eq_app) =
        let sigma, typ = infer_type env sigma trm in
        sigma, Util.on_snd dest_eq (zoom_product_type env typ)
      in
      let sigma, eq =
        let sigma, trm1 =
          let typ_args = shift_all (mk_n_rels (nb_rel env_args)) in
          let sigma, lifted =
            let arg = last_arg (last_arg eq_app.trm1) in
            lift env_eq l arg typ_args sigma
          in lift env_eq (flip_dir l) lifted typ_args sigma
        in sigma, apply_eq { eq_app with trm1 }
      in sigma, (env_eq, eq)
    in sigma, reconstruct_product env_eq eq
  in trm, typ

(* --- Top-level equivalence proof generation --- *)
                     
(*
 * Prove section/retraction
 *)
let prove_section_or_retraction env sigma l =
  match l.orn.kind with
  | Algebraic (indexer, off) ->
     equiv_proof_algebraic env l sigma
  | CurryRecord ->
     equiv_proof_curry_record env l sigma
  | SwapConstruct _ ->
     equiv_proof_swap env l sigma
  | UnpackSigma ->
     equiv_proof_unpack env l sigma
  | Custom _ ->
     failwith "not supported"
                        
(*
 * Prove section and retraction
 *)
let prove_equivalence env sigma =
  twice_directional (prove_section_or_retraction env sigma)

(* --- Automatically generated adjunction proof --- *)

let lookup_constant = Libnames.qualid_of_string %> Nametab.locate_constant

let fresh_constant env const =
  bind
    (fun sigma -> Evd.fresh_constant_instance env sigma const)
    (fun c -> ret (mkConstU c))

type pre_adjoint = {
  orn : lifting;
  sect : Names.Constant.t;
  retr0 : Names.Constant.t
}

(*
 * Prepare quantification for an almost-adjoint equivalence, by pulling out
 * all the type-quantified values (i.e., type parameters/indices) into a new
 * local context before giving back an argument list for the adjunction lemmas.
 *)
let quantify_pre_adjunction env { orn; sect; retr0 } =
  let apply_to xs f = mkApp (f, xs) in
  bind
    (map_tuple_state (fresh_constant env) (sect, retr0))
    (fun (sect, retr0) ->
      let equiv, inv = lift_to orn, lift_back orn in
      let domain, codomain =
        destConst equiv |> Environ.constant_type_in env |>
          Reduction.nf_betaiota env |> Term.decompose_prod_assum
      in
      let ctxt = List.tl domain in
      let left_typ = List.hd domain |> rel_type in
      let right_typ = Vars.lift (-1) codomain in
      let args = Context.Rel.to_extended_vect mkRel 0 ctxt in
      let adj_types = [|left_typ; right_typ|] in
      let adj_terms = Array.map (apply_to args) [|equiv; inv; sect; retr0|] in
      ret (ctxt, Array.append adj_types adj_terms))

(*
 * Apply the above to a constant
 *)
let quantify_pre_adjunction_const env pre_adj c =
  bind
    (fresh_constant env c)
    (fun adjointifier ->
      bind
        (quantify_pre_adjunction env pre_adj)
        (fun (ctxt, pre_adjunct) ->
          ret (recompose_lam_assum ctxt (mkApp (adjointifier, pre_adjunct)))))
    
(*
 * Augment the initial retraction proof in order to prove adjunction.
 *
 * The generic proof of adjunction from the HoTT book relies critically on this
 * step; wrapping the proof term for retraction in a clever way (formalized in
 * `fg_id'`) makes a later equality of equality proofs true definitionally.
 *)
let adjointify_retraction env pre_adj =
  let c = lookup_constant "Ornamental.Adjoint.fg_id'" in
  quantify_pre_adjunction_const env pre_adj c

(*
 * Prove adjunction.
 *)
let prove_adjunction env pre_adj sigma =
  let c = lookup_constant "Ornamental.Adjoint.f_adjoint" in
  let sigma, adjunction = quantify_pre_adjunction_const env pre_adj c sigma in
  let sigma, adjunction_typ = reduce_type env sigma adjunction in
  sigma, (adjunction, adjunction_typ)

