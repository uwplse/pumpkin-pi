(*
 * Searching for ornamental promotions between inductive types.
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
open Hypotheses (* TODO same *)
open Specialization (* TODO same *)

(* --- Finding the new index --- *)

(* 
 * The offset function (wrapped with IB for convenience)
 *)

(* Find the new index offset and type *)
let offset_and_ib env_pms a b =
  let (a_t, b_t) = map_tuple fst (map_tuple destInd (fst a, fst b)) in
  let idx_op = new_index_type_simple env_pms a_t b_t in
  if Option.has_some idx_op then
    Option.get idx_op
  else
    let (elim_t_a, elim_t_b) = map_tuple snd (a, b) in
    new_index_type env_pms elim_t_a elim_t_b

(* --- Finding the indexer --- *)

(*
 * Once the algorithm has the index offset and type, it then
 * searches for the indexer function. It does this by
 * traversing the types of the eliminators in parallel and forming
 * the function as it goes, substituting in the appropriate motive.
 *)            

(*
 * The new oracle with an optimization.
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
let optimized_is_new env off p a b =
  let (a_t, elim_a) = a in
  let (b_t, elim_b) = b in
  let (_, t_a, b_a) = destProd elim_a in
  let (_, t_b, b_b) = destProd elim_b in
  let optimize_types = not (same_mod_indexing env p (a_t, t_a) (b_t, t_b)) in
  let optimize_arity = (arity b_a = arity b_b) in
  if optimize_types then
    true
  else if optimize_arity then
    false
  else
    (* call is_new *)
    computes_ih_index off (shift p) (mkRel 1) b_b

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
 *)
let index_case env off p a b : types =
  let rec diff_case p p_a_b subs e a b =
    let (a_t, c_a) = a in
    let (b_t, c_b) = b in
    match map_tuple kind (c_a, c_b) with
    | (App (_, _), App (_, _)) ->
       (* INDEX-CONCLUSION *)
       List.fold_right all_eq_substs subs (get_arg off c_b)
    | (Prod (n_a, t_a, b_a), Prod (n_b, t_b, b_b)) ->
       let diff_b = diff_case (shift p) (shift p_a_b) in
       if optimized_is_new e off p_a_b a b then
         (* INDEX-HYPOTHESIS *)
         let a = map_tuple shift a in
         let b = (shift b_t, b_b) in
         unshift (diff_b (shift_subs subs) (push_local (n_b, t_b) e) a b)
       else
         let e_b = push_local (n_a, t_a) e in
         let a = (shift a_t, b_a) in
         let b = (shift b_t, b_b) in
         if apply p_a_b t_a t_b then
           (* INDEX-IH *)
           let sub_index = (shift (get_arg off t_b), mkRel 1) in
           let subs_b = sub_index :: shift_subs subs in
           mkLambda (n_a, mkAppl (p, unfold_args t_a), diff_b subs_b e_b a b)
         else
           (* INDEX-PROD *)
           mkLambda (n_a, t_a, diff_b (shift_subs subs) e_b a b)
    | _ ->
       failwith "unexpected case"
  in diff_case p (mkRel 1) [] env a b

(* Get the cases for the indexer *)
let indexer_cases env off p nargs a b : types list =
  let (a_t, elim_t_a) = a in
  let (b_t, elim_t_b) = b in
  match map_tuple kind (elim_t_a, elim_t_b) with
  | (Prod (n_a, p_a_t, b_a), Prod (_, _, b_b)) ->
     let env_p_a = push_local (n_a, p_a_t) env in
     List.map2
       (fun c_a c_b ->
         shift_by
           (nargs - 1)
           (index_case env_p_a off p (a_t, c_a) (b_t, c_b)))
       (take_except nargs (factor_product b_a))
       (take_except (nargs + 1) (factor_product b_b))
  | _ ->
     failwith "not eliminators"

(* Find the motive for the indexer (INDEX-MOTIVE) *)
let index_motive idx npm env_a =
  let (off, ib_t) = idx in
  let ib_t = shift_by (npm + off) ib_t in
  reconstruct_lambda_n env_a ib_t npm

(* Search for an indexing function *)
let find_indexer env_pms idx elim_a a b : types =
  let (a_t, elim_t_a) = a in
  let (b_t, elim_t_b) = b in
  let npm = nb_rel env_pms in
  let (off, _) = idx in
  match kind elim_t_a with
  | Prod (_, p_a_t, _) ->
     let env_a = zoom_env zoom_product_type env_pms p_a_t in
     let nargs = new_rels env_a npm in
     let p = index_motive idx npm env_a in
     let app =
       apply_eliminator
         {
           elim = elim_a;
           pms = shift_all_by nargs (mk_n_rels npm);
           p = shift_by nargs p;
           cs = indexer_cases env_pms off (shift p) nargs a b;
           final_args = mk_n_rels nargs;
         }
     in reconstruct_lambda env_a app
  | _ ->
     failwith "not an eliminator"

(* --- Finding promote and forget --- *)

(*
 * This implements the "Searching for Promote and Forget" paragraph
 *)

(*
 * Stretch the old motive type to match the new one
 * That is, add indices where they are missing in the old motive
 * For now just supports one index
 *)
let rec stretch_motive_type off env o n =
  let (o_typ, p_o_typ) = o in
  let (n_typ, p_n_typ) = n in
  match map_tuple kind (p_o_typ, p_n_typ) with
  | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
     let n_b = (shift n_typ, b_n) in
     if off = 0 then
       mkProd (n_n, t_n, shift p_o_typ)
     else
       let env_b = push_local (n_o, t_o) env in
       let o_b = (shift o_typ, b_o) in
       mkProd (n_o, t_o, stretch_motive_type (off - 1) env_b o_b n_b)
  | _ ->
     p_o_typ

(*
 * Stretch the old motive to match the new one at the term level
 *
 * Hilariously, this function is defined as an ornamented
 * version of stretch_motive_type.
 *)
let stretch_motive off env o n =
  let (o_typ, p_o_typ) = o in
  let o = (o_typ, lambda_to_prod p_o_typ) in
  prod_to_lambda (stretch_motive_type off env o n)

(*
 * Stretch out the old eliminator type to match the new one
 * That is, add indexes to the old one to match new
 *)
let stretch off env indexer npm o n is_fwd =
  let (a, b) = map_if reverse (not is_fwd) (o, n) in
  let (a_t, elim_a_t) = a in
  let (b_t, elim_b_t) = b in
  let (n_exp, p_a_t, b_a) = destProd elim_a_t in
  let (_, p_b_t, _) = destProd elim_b_t in
  let p_exp = stretch_motive_type off env (a_t, p_a_t) (b_t, p_b_t) in
  let b_exp =
    map_term_if
      (fun (p, _) t -> applies p t)
      (fun (p, pms) t ->
        let non_pms = unfold_args t in
        let index = mkAppl (indexer, List.append pms non_pms) in
        mkAppl (p, insert_index off index non_pms))
      (fun (p, pms) -> (shift p, shift_all pms))
      (mkRel 1, shift_all (mk_n_rels npm))
      b_a
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
 * Find the motive that the ornamental promotion or forgetful function proves
 * for an indexing function (PROMOTE-MOTIVE and FORGET-MOTIVE)
 *)
let promote_forget_motive off env t arity npm indexer_opt =
  let args = shift_all (mk_n_rels arity) in
  let concl =
    match indexer_opt with
    | Some indexer ->
       (* PROMOTE-MOTIVE *)
       let indexer = Option.get indexer_opt in
       let index = mkAppl (indexer, snoc (mkRel 1) args) in
       mkAppl (t, insert_index (npm + off) index args)
    | None ->
       (* FORGET-MOTIVE *)
       mkAppl (t, adjust_no_index (npm + off) (shift_all args))
  in reconstruct_lambda_n env concl npm

(*
 * Substitute indexes and IHs in a case of promote or forget 
 *)
let promote_forget_case env off is_fwd p o n : types =
  let directional a b = if is_fwd then a else b in
  let rec sub p p_a_b subs e o n =
    let (ind_o, c_o) = o in
    let (ind_n, c_n) = n in
    match map_tuple kind (c_o, c_n) with
    | (App (f_o, args_o), App (f_n, args_n)) ->
       (* PROMOTE-CONCLUSION / FORGET-CONCLUSION *)
       List.fold_right all_eq_substs subs (last_arg c_n)
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let sub_b = sub (shift p) (shift p_a_b) in
       if optimized_is_new e off p_a_b (directional o n) (directional n o) then
         (* PROMOTE-HYPOTHESIS and FORGET-HYPOTHESIS *)
         let o = (shift ind_o, directional (shift c_o) b_o) in
         let n = (shift ind_n, directional b_n (shift c_n)) in
         directional
           unshift
           (fun b -> mkLambda (n_o, t_o, b))
           (sub_b (shift_subs subs) (push_local (n_n, t_n) e) o n)
       else
         let e_b = push_local (n_o, t_o) e in
         let o = (shift ind_o, b_o) in
         let n = (shift ind_n, b_n) in
         if apply p_a_b t_o t_n then
           (* PROMOTE-IH / FORGET-IH *)
           let ib_sub = map_tuple shift (map_tuple (get_arg off) (t_n, t_o)) in
           let ih_sub = (shift (last_arg t_n), mkRel 1) in
           let subs_b = List.append [ib_sub; ih_sub] (shift_subs subs) in
           mkLambda (n_o, mkAppl (p, unfold_args t_o), sub_b subs_b e_b o n)
         else
           (* PROMOTE-PROD / FORGET-PROD *)
           mkLambda (n_o, t_o, sub_b (shift_subs subs) e_b o n)
    | _ ->
       failwith "unexpected case substituting index"
  in sub p (mkRel 1) [] env o n

(*
 * Get the cases for the ornamental promotion/forgetful function. 
 *
 * For each case, this currently works in the following way:
 * 1. If it's forwards, then adjust the motive to have the index
 * 2. Substitute in the motive, ih, & indices (or lack thereof, if backwards)
 *
 * Eventually, we might want to think of this as (or rewrite this to)
 * abstracting the indexed type to take an indexing function, then
 * deriving the result through specialization.
 *)
let promote_forget_cases env off is_fwd orn_p nargs o n : types list =
  let directional a b = if is_fwd then a else b in
  let (o_t, elim_o_t) = o in
  let (n_t, elim_n_t) = n in
  let (n_o, p_o_t, b_o) = destProd elim_o_t in
  let (_, p_n_t, b_n) = destProd elim_n_t in
  let env_p_o = push_local (n_o, p_o_t) env in
  let adjust p = shift (stretch_motive off env (o_t, p) (n_t, p_n_t)) in
  let p = map_if adjust is_fwd (unshift orn_p) in
  List.map2
    (fun c_o c_n ->
      shift_by
        (directional (nargs - 1) (nargs - 2))
        (promote_forget_case env off is_fwd p (o_t, c_o) (n_t, c_n)))
    (take_except nargs (factor_product b_o))
    (take_except (directional (nargs + 1) (nargs - 1)) (factor_product b_n))

(*
 * Make a packer function for existT/sigT
 *)
let make_packer env evd b_typ args (off, ib_typ) is_fwd =
  let sub_index = if is_fwd then insert_index else reindex in
  let packed_args = sub_index off (mkRel 1) (shift_all args) in
  let env_abs = push_local (Anonymous, ib_typ) env in
  abstract_arg env_abs evd off (mkAppl (b_typ, packed_args))

(*
 * Pack the conclusion of an ornamental promotion
 *)
let pack_conclusion f_indexer env evd idx b unpacked =
  let (b_typ, arity) = b in
  let off = arity - 1 in
  let index_type = shift_by off (snd idx) in
  let packer = make_packer env evd b_typ (mk_n_rels off) idx true in
  let index = mkAppl (f_indexer, mk_n_rels arity) in
  (env, pack_existT {index_type; packer; index; unpacked})

(*
 * Pack the hypothesis type into a sigT, and update the environment
 *)
let pack_hypothesis_type env ib_typ packer (id, unpacked_typ) : env =
  let packer = unshift packer in
  let packed_typ = pack_sigT { index_type = ib_typ ; packer } in
  push_local (id, packed_typ) (pop_rel_context 1 env)

(*
 * Apply the packer to the index
 *)
let apply_packer env packer arg =
  reduce_term env (mkAppl (packer, [arg]))

(*
 * Remove the index from the environment, and adjust terms appropriately
 *)
let adjust_to_elim env ib_rel packer packed =
  let env_packed = remove_rel (ib_rel + 1) env in
  let adjust = unshift_local ib_rel 1 in
  (env_packed, adjust packer, adjust packed)

(*
 * Pack the unpacked term to eliminate using the new hypothesis
 *)
let pack_unpacked env packer ib_typ ib_rel unpacked =
  let sub_typ = all_eq_substs (mkRel (4 - ib_rel), mkRel 1) in
  let sub_index = all_eq_substs (mkRel (ib_rel + 3), mkRel 2) in
  let adjust trm = shift_local ib_rel 1 (shift trm) in
  let typ_body = sub_index (sub_typ (adjust unpacked)) in
  let packer_indexed = apply_packer env (shift packer) (mkRel 1) in
  let index_body = mkLambda (Anonymous, packer_indexed, typ_body) in
  mkLambda (Anonymous, shift ib_typ, index_body)

(*
 * Pack the hypothesis of an ornamental forgetful function
 *)
let pack_hypothesis env evd idx b unpacked =
  let (off, ib_typ) = (fst idx, shift (snd idx)) in
  let (b_typ, _) = b in
  let (id, _, unpacked_typ) = CRD.to_tuple @@ lookup_rel 1 env in
  let packer = make_packer env evd b_typ (unfold_args unpacked_typ) idx false in
  let env_push = pack_hypothesis_type env ib_typ packer (id, unpacked_typ) in
  let ib_rel = new_rels (pop_rel_context 1 env) off in
  let unpacked = pack_unpacked env_push packer ib_typ ib_rel unpacked in
  let adjusted = adjust_to_elim env_push ib_rel packer unpacked in
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
let pack_orn f_indexer is_fwd =
  if is_fwd then pack_conclusion f_indexer else pack_hypothesis

(* Search for the promotion or forgetful function *)
let find_promote_or_forget env_pms evd idx indexer_n o n is_fwd =
  let directional x y = if is_fwd then x else y in
  let (o_typ, arity_o, elim, elim_o_typ) = o in
  let (n_typ, arity_n, _, elim_n_typ) = n in
  let npm = nb_rel env_pms in
  let (off, idx_t) = idx in
  let f_indexer = make_constant indexer_n in
  let f_indexer_opt = directional (Some f_indexer) None in
  let (_, p_o, _) = destProd elim_o_typ in
  let env_p_o = zoom_env zoom_product_type env_pms p_o in
  let nargs = new_rels env_p_o npm in
  let (typ, arity) = (n_typ, directional arity_o arity_n) in
  let o = (o_typ, elim_o_typ) in
  let n = (n_typ, elim_n_typ) in
  let elim_a_typ_exp = stretch off env_pms f_indexer npm o n is_fwd in
  let o = (o_typ, directional elim_a_typ_exp elim_o_typ) in
  let n = (n_typ, directional elim_n_typ elim_a_typ_exp) in
  let p = promote_forget_motive off env_p_o typ arity npm f_indexer_opt in
  let adj = directional identity shift in
  let unpacked =
    apply_eliminator
      {
        elim = elim;
        pms = shift_all_by nargs (mk_n_rels npm);
        p = shift_by nargs p;
        cs =
          List.map
            adj
            (promote_forget_cases env_pms off is_fwd (adj (shift p)) nargs o n);
        final_args = mk_n_rels nargs;
      }
  in
  let o = (o_typ, arity_o) in
  let n = (n_typ, arity_n) in
  let idx = (npm + off, idx_t) in
  let b = directional n o in
  let packed = pack_orn f_indexer is_fwd env_p_o evd idx b unpacked in
  reconstruct_lambda (fst packed) (snd packed)

(* Find promote and forget, using a directional flag for abstraction *)
let find_promote_forget env_pms evd idx indexer_n a b =
  twice (find_promote_or_forget env_pms evd idx indexer_n) a b

(* --- Algebraic ornaments --- *)
              
(*
 * Search two inductive types for an algebraic ornament between them
 *)
let search_algebraic env evd npm indexer_n a b =
  let (a_typ, arity_a) = a in
  let (b_typ, arity_b) = b in
  let lookup_elim typ = type_eliminator env (fst (destInd typ)) in
  let elims = map_tuple lookup_elim (a_typ, b_typ) in
  let zoom_elim_typ el = zoom_n_prod env npm (infer_type env evd el) in
  let ((env_pms, el_a_typ), (_, el_b_typ)) = map_tuple zoom_elim_typ elims in
  let a = (a_typ, el_a_typ) in
  let b = (b_typ, el_b_typ) in
  let idx = offset_and_ib env_pms a b in (* idx = (off, I_B) *)
  let indexer = find_indexer env_pms idx (fst elims) a b in
  let a = (a_typ, arity_a, fst elims, el_a_typ) in
  let b = (b_typ, arity_b, snd elims, el_b_typ) in
  let (promote, forget) = find_promote_forget env_pms evd idx indexer_n a b in
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
         let (a, b) = map_if reverse (arity_n <= arity_o) (o, n) in
         search_algebraic env evd npm indexer_id a b
       else
         failwith "this kind of change is not yet supported"
  | _ ->
     failwith "this kind of change is not yet supported"

             
(* --- Coherence proof --- *) 

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
              
(* --- Equivalence proofs --- *)

(*
 * The proofs of both section and retraction apply lemmas
 * that show that equalities are preserved in inductive cases.
 * These lemmas are folds over substitutions of recursive arguments, 
 * with refl as identity.
 *
 * To construct these proofs, we first construct the lemmas, then 
 * specialize them to the appropriate arguments.
 *)
              
(*
 * Form the environment with the appropriate hypotheses for the equality lemmas.
 * Take as arguments the original environment, an evar_map, the recursive
 * arguments for the particular case, and a lift config.
 *)
let eq_lemmas_env env evd recs l =
  List.fold_left
    (fun e r ->
      let r1 = shift_by (new_rels2 e env) r in
      let r_t = reduce_type e evd r1 in
      let push_ib =
        map_backward
          (fun e ->
            push_local (Anonymous, reduce_type e evd (get_arg l.off r_t)) e)
          l
      in
      (* push index in backwards direction *)
      let e_ib = push_ib e in 
      let adj_back = map_backward (reindex_app (reindex l.off (mkRel 1))) l in
      let r_t = adj_back (shift_by (new_rels2 e_ib e) r_t) in
      (* push new rec arg *)
      let e_r = push_local (Anonymous, r_t) e_ib in
      let pack_back = map_backward (pack e_r evd l.off) l in
      let r1 = pack_back (shift_by (new_rels2 e_r e) r1) in
      let r2 = pack_back (mkRel 1) in
      let r_t = reduce_type e_r evd r1 in
      let r_eq = apply_eq {at_type = r_t; trm1 = r1; trm2 = r2} in
      (* push equality *)
      push_local (Anonymous, r_eq) e_r)
    env
    recs
  
(*
 * Determine the equality lemmas for each case of an inductive type
 * Take as arguments an environment, an evar_map, the inductive type,
 * and a lift config.
 *)
let eq_lemmas env evd typ l =
  let ((i, i_index), u) = destInd typ in
  Array.mapi
    (fun c_index _ ->
      let c = mkConstructU (((i, i_index), c_index + 1), u) in
      let (env_c_b, c_body) = zoom_lambda_term env (expand_eta env evd c) in
      let c_body = reduce_term env_c_b c_body in
      let c_args = unfold_args c_body in
      let recs = List.filter (on_type (is_or_applies typ) env_c_b evd) c_args in
      let env_lemma = eq_lemmas_env env_c_b evd recs l in
      let pack_back = map_backward (pack env_lemma evd l.off) l in
      let c_body = pack_back (shift_by (new_rels2 env_lemma env_c_b) c_body) in
      let c_body_type = reduce_type env_lemma evd c_body in
      (* reflexivity proof: the identity case *)
      let refl = apply_eq_refl { typ = c_body_type; trm = c_body } in
      (* fold to recursively substitute each recursive argument *)
      let (body, _, _) =
        List.fold_right
          (fun _ (b, h, c_app) ->
            let h_r = destRel h in
            let (_, _, h_t) = CRD.to_tuple @@ lookup_rel h_r env_lemma in
            let app = dest_eq (shift_by h_r h_t) in
            let at_type = app.at_type in
            let r1 = app.trm1 in
            let r2 = app.trm2 in
            let c_body_b = shift c_body in
            let c_app_b = shift c_app in
            let (abs_c_app, c_app_trans) =
              if l.is_fwd then
                let abs_c_app = all_eq_substs (shift r1, mkRel 1) c_app_b in
                let c_app_trans = all_eq_substs (r1, r2) c_app in
                (abs_c_app, c_app_trans)
              else
                let (r1_ex, r2_ex) = map_tuple dest_existT (r1, r2) in
                let r1_u = r1_ex.unpacked in
                let r2_u = r2_ex.unpacked in
                let r1_ib = r1_ex.index in
                let r2_ib = r2_ex.index in
                let b_sig_typ = dest_sigT (shift at_type) in
                let ib = project_index b_sig_typ (mkRel 1) in
                let u = project_value b_sig_typ (mkRel 1) in
                let abs_c_app_u = all_eq_substs (shift r1_u, u) c_app_b in
                let abs_c_app = all_eq_substs (shift r1_ib, ib) abs_c_app_u in
                let c_app_trans_u = all_eq_substs (r1_u, r2_u) c_app in
                let c_app_trans = all_eq_substs (r1_ib, r2_ib) c_app_trans_u in
                (abs_c_app, c_app_trans)
            in
            let typ_b = shift c_body_type in
            let p_b = { at_type = typ_b; trm1 = c_body_b; trm2 = abs_c_app } in
            let p = mkLambda (Anonymous, at_type, apply_eq p_b) in
            let eq_proof_app = {at_type; p; trm1 = r1; trm2 = r2; h; b} in
            let eq_proof = apply_eq_ind eq_proof_app in
            (eq_proof, shift_by (directional l 2 3) h, c_app_trans))
          recs
          (refl, mkRel 1, c_body)
      in reconstruct_lambda env_lemma body)
    ((lookup_mind i env).mind_packets.(i_index)).mind_consnames

(* TODO move out shifting? why there *)
(* TODO refactor packing w/ pack in specialization, or w/ lift pack *)
(* TODO refactor, clean, etc *)
(* TODO remove at_type or pass different arg for this *)
let retraction_motive env evd at_type_packed promote forget npm l =
  let b = mkRel 1 in
  let env_u = env in (* TODO remove later; part of a refactor *)
  let b_typ = reduce_type env_u evd b in
  let typ_args = remove_index l.off (unfold_args b_typ) in (* TODO refactor this stuff, common w lift config *)
  let b_ex = pack env_u evd l.off b in
  let b_ex' = mkAppl (promote, snoc (mkAppl (forget, snoc b_ex typ_args)) typ_args) in
  let at_type = reduce_type env_u evd b_ex in (* TODO more redundancy *)
  let p_b = apply_eq { at_type; trm1 = b_ex; trm2 = b_ex' } in
  shift_by (new_rels env npm - 1) (reconstruct_lambda_n env_u p_b npm)

(* TODO test w third new index to doublevector *)
(* TODO move out shifting? why there *)
(* TODO refactor, clean, etc *)
(* TODO is a just always mkRel 1? *)
let section_motive env evd at_type promote forget npm =
  let a = mkRel 1 in
  let typ_args = unfold_args at_type in
  let a' = mkAppl (forget, snoc (mkAppl (promote, snoc a typ_args)) typ_args) in
  let p_b = apply_eq { at_type; trm1 = a; trm2 = a' } in
  shift_by (new_rels env npm) (reconstruct_lambda_n env p_b npm)

(* TODO refactor, clean, etc *)
let retraction_case env evd pms p eq_lemma c =
  let rec case e pms p_rel p args lemma_args c =
    match kind c with
      | App (_, _) ->
         (* conclusion: apply eq lemma and beta-reduce *)
         let all_args = List.append (List.rev args) (List.rev lemma_args) in
         reduce_term e (mkAppl (eq_lemma, List.append pms all_args))
      | Prod (n, t, b) ->
         let case_b = case (push_local (n, t) e) (shift_all pms) (shift p_rel) (shift p) in
         if applies p_rel t then
           (* IH *)
           let t' = reduce_term e (mkAppl (p, unfold_args t)) in
           let app = dest_eq t' in
           let b' = app.trm2 in
           let b_sig_t' = dest_sigT (reduce_type e evd b') in
           let ib' = project_index b_sig_t' b' in
           let bv' = project_value b_sig_t' b' in
           let lemma_args_b = mkRel 1 :: shift_all (bv' :: ib' :: lemma_args) in
           mkLambda (n, t', case_b (shift_all args) lemma_args_b b)
         else
           (* Product *)
           let args_b = mkRel 1 :: shift_all args in
           mkLambda (n, t, case_b args_b (shift_all lemma_args) b)
      | _ ->
         failwith "unexpected case"
    in case env pms (mkRel 1) p [] [] c
           
(* TODO refactor, clean, etc *)
let section_case env pms p eq_lemma c =
  let rec case e pms p_rel p args lemma_args c =
    match kind c with
      | App (_, _) ->
         (* conclusion: apply eq lemma and beta-reduce *)
         let all_args = List.append (List.rev args) (List.rev lemma_args) in
         reduce_term e (mkAppl (eq_lemma, List.append pms all_args))
      | Prod (n, t, b) ->
         let case_b = case (push_local (n, t) e) (shift_all pms) (shift p_rel) (shift p) in
         if applies p_rel t then
           (* IH *)
           let t' = reduce_term e (mkAppl (p, unfold_args t)) in
           let app = dest_eq t' in
           let a' = app.trm2 in
           let lemma_args_b = mkRel 1 :: shift_all (a' :: lemma_args) in
           mkLambda (n, t', case_b (shift_all args) lemma_args_b b)
         else
           (* Product *)
           let args_b = mkRel 1 :: shift_all args in
           mkLambda (n, t, case_b args_b (shift_all lemma_args) b)
      | _ ->
         failwith "unexpected case"
    in case env pms (mkRel 1) p [] [] c

 

(* TODO refactor below, comment, fill in *)
(* TODO clean up too *)
let prove_section promote_n forget_n env evd l =
  let env_sec = zoom_env zoom_lambda_term env l.orn.promote in
  let a = mkRel 1 in
  let at_type = reduce_type env_sec evd a in
  let a_typ = first_fun at_type in
  let ((i, i_index), u) = destInd a_typ in
  let mutind_body = lookup_mind i env in
  let elim = type_eliminator env_sec (i, i_index) in
  let npm = mutind_body.mind_nparams in
  let nargs = new_rels env_sec npm in
  let (env_pms, elim_typ) = zoom_n_prod env npm (infer_type env evd elim) in
  let (n, p_t, b) = destProd elim_typ in
  let env_motive = zoom_env zoom_product_type env_pms p_t in
  let p = section_motive env_motive evd at_type (make_constant promote_n) (make_constant forget_n) npm in
  let env_p = push_local (n, p_t) env_pms in
  let pms = shift_all (mk_n_rels npm) in (* TODO why shift *)
  let lemmas = eq_lemmas env evd a_typ l in
  let cs = List.mapi (fun j c -> section_case env_p pms (unshift_by (nargs - 1) p) lemmas.(j) c) (take_except nargs (factor_product b)) in
  let app =
       apply_eliminator
         {
           elim;
           pms = shift_all_by (nargs - 1) pms; (* TODO why *)
           p;
           cs = shift_all_by (nargs - 1) cs;
           final_args = mk_n_rels nargs;
         }
  in
  let eq_typ = dest_eq (reduce_type env_sec evd app) in
  let t1 = eq_typ.trm1 in
  let t2 = eq_typ.trm2 in
  reconstruct_lambda env_sec (mkAppl (eq_sym, [at_type; t1; t2; app]))

(* TODO refactor common w/ section, or call lift *)
(* TODO refactor below, comment, fill in *)
(* TODO clean up too *)
let prove_retraction promote_n forget_n env evd l =
  (* TODO should be env_retract *)
  let env_sec = zoom_env zoom_lambda_term env l.orn.forget in
  let b = mkRel 1 in
  let at_type_packed = reduce_type env_sec evd b in
  let at_type = snd (zoom_lambda_term env_sec (last_arg at_type_packed)) in
  let b_typ = first_fun at_type in
  let ((i, i_index), u) = destInd b_typ in
  let mutind_body = lookup_mind i env in
  let elim = type_eliminator env_sec (i, i_index) in
  let npm = mutind_body.mind_nparams in
  let nargs = new_rels env_sec npm in
  let (env_pms, elim_typ) = zoom_n_prod env npm (infer_type env evd elim) in
  let (n, p_t, b) = destProd elim_typ in
  let env_motive = zoom_env zoom_product_type env_pms p_t in
  let p = retraction_motive env_motive evd at_type_packed (make_constant promote_n) (make_constant forget_n) npm l in
  let env_p = push_local (n, p_t) env_pms in
  let pms = shift_all (mk_n_rels npm) in (* TODO why shift *)
  let lemmas = eq_lemmas env evd b_typ l in
  let cs = List.mapi (fun j c -> retraction_case env_p evd pms (unshift_by (nargs - 1) p) lemmas.(j) c) (take_except (nargs + 1) (factor_product b)) in
  let args = mk_n_rels nargs in
  let b_sig = last args in
  let b_sig_typ = on_type dest_sigT env_sec evd b_sig in
  let i_b = project_index b_sig_typ b_sig in
  let b = project_value b_sig_typ b_sig in
  let final_args = insert_index (l.off - npm) i_b (reindex (nargs - 1) b args) in
  let app =
       apply_eliminator
         {
           elim;
           pms = shift_all_by (nargs - 1) pms; (* TODO why *)
           p;
           cs = shift_all_by (nargs - 1) cs;
           final_args;
         }
  in (* TODO use eta_sigT where relevant *)
  let eq_typ = dest_eq (reduce_type env_sec evd app) in
  let t1 = eq_typ.trm1 in
  let t2 = eq_typ.trm2 in
  let at_type = reduce_type env_sec evd t1 in (* TODO why can't just reuse *)
  let sym_app = mkAppl (eq_sym, [at_type; t1; t2; app]) in
  let to_elim = dest_sigT at_type in
  let t1_ex = dest_existT t1 in
  let trm2 = last_arg (t1_ex.unpacked) in
  let trm1 = all_eq_substs (t1, trm2) t2 in
  (* TODO why all the shifting here *)
  let packed_type = shift (reconstruct_lambda_n env_sec (apply_eq {at_type; trm1; trm2}) (nb_rel env_sec - 1)) in
  let ib_typ = (dest_sigT at_type).index_type in
  let b_typ = mkAppl ((dest_sigT (shift at_type)).packer, [mkRel 1]) in
  let sym_app_b = all_eq_substs (shift_by 2 i_b, mkRel 2) (all_eq_substs (shift_by 2 b, mkRel 1) (shift_by 2 sym_app)) in
  let unpacked = mkLambda (Anonymous, ib_typ, (mkLambda (Anonymous, b_typ, sym_app_b))) in (* TODO build by env instead *)
  let arg = mkRel 1 in
  let elim_app = elim_sigT { to_elim; packed_type; unpacked; arg } in
  reconstruct_lambda env_sec elim_app
