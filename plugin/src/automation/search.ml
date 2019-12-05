(*
 * Searching for ornamental promotions between inductive types.
 * Some of the useful dependencies can be found in the differencing component.
 *)

open Names
open Constr
open Environ
open Utilities
open Debruijn
open Indexing
open Hofs
open Substitution
open Factoring
open Zooming
open Abstraction
open Lifting
open Declarations
open Util
open Differencing
open Inference
open Indutils
open Typehofs
open Funutils
open Apputils
open Envutils
open Contextutils
open Sigmautils
open Reducers
open Constutils
open Stateutils
open Apputils
open Caching
open Desugarprod

(* --- Error messages for the user --- *)
       
let unsupported_change_error =
  Pp.str
    "change not yet supported; request on GitHub issues if interested"

let new_parameter_error =
  Pp.str
    "new parameters not yet supported; request on GitHub issues if interested"

let new_constructor_error =
  Pp.str
    "new constructors not yet supported; request on GitHub issues if interested"
    
(* --- Finding the new index --- *)

(* 
 * The offset function (wrapped with IB for convenience)
 *)

(* Find the new index offset and type *)
let offset_and_ib env_pms a b sigma =
  let (a_t, b_t) = map_tuple fst (map_tuple destInd (fst a, fst b)) in
  let idx_op = new_index_type_simple env_pms sigma a_t b_t in
  if Option.has_some idx_op then
    Option.get idx_op
  else
    let (elim_t_a, elim_t_b) = map_tuple snd (a, b) in
    new_index_type env_pms sigma elim_t_a elim_t_b

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
  bind
    (not_state
       (fun (b_t, t_b) sigma ->
         same_mod_indexing env sigma p (a_t, t_a) (b_t, t_b))
       (b_t, t_b))
    (fun optimize_types ->
      let optimize_arity = (arity b_a = arity b_b) in
      if optimize_types then
        ret true
      else if optimize_arity then
        ret false
      else
        (* call is_new *)
        ret (computes_ih_index off (shift p) (mkRel 1) b_b))

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
let index_case env sigma off p a b : types state =
  let rec diff_case p p_a_b subs e a b =
    let (a_t, c_a) = a in
    let (b_t, c_b) = b in
    match map_tuple kind (c_a, c_b) with
    | (App (_, _), App (_, _)) ->
       (* INDEX-CONCLUSION *)
       ret (List.fold_right all_eq_substs subs (get_arg off c_b))
    | (Prod (n_a, t_a, b_a), Prod (n_b, t_b, b_b)) ->
       let diff_b = diff_case (shift p) (shift p_a_b) in
       branch_state
         (optimized_is_new e off p_a_b a)
         (fun _ -> 
           (* INDEX-HYPOTHESIS *)
           let a = map_tuple shift a in
           let b = (shift b_t, b_b) in
           bind
             (diff_b (shift_subs subs) (push_local (n_b, t_b) e) a b)
             (fun b -> ret (unshift b)))
         (fun _ ->
           let e_b = push_local (n_a, t_a) e in
           let a = (shift a_t, b_a) in
           let b = (shift b_t, b_b) in
           if apply p_a_b t_a t_b then
             (* INDEX-IH *)
             let sub_index = (shift (get_arg off t_b), mkRel 1) in
             let subs_b = sub_index :: shift_subs subs in
             bind
               (diff_b subs_b e_b a b)
               (fun b -> ret (mkLambda (n_a, mkAppl (p, unfold_args t_a), b)))
           else
             (* INDEX-PROD *)
             bind
               (diff_b (shift_subs subs) e_b a b)
               (fun b -> ret (mkLambda (n_a, t_a, b))))
         b
    | _ ->
       CErrors.user_err unsupported_change_error
  in diff_case p (mkRel 1) [] env a b sigma

(* Get the cases for the indexer *)
let indexer_cases env off p nargs a b =
  let (a_t, elim_t_a) = a in
  let (b_t, elim_t_b) = b in
  match map_tuple kind (elim_t_a, elim_t_b) with
  | (Prod (n_a, p_a_t, b_a), Prod (_, _, b_b)) ->
     let env_p_a = push_local (n_a, p_a_t) env in
     map2_state
       (fun c_a c_b sigma ->
         Util.on_snd
           (shift_by (nargs - 1))
           (index_case env_p_a sigma off p (a_t, c_a) (b_t, c_b)))
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
let find_indexer env_pms idx elim_a a b =
  let (a_t, elim_t_a) = a in
  let npm = nb_rel env_pms in
  let (off, _) = idx in
  match kind elim_t_a with
  | Prod (_, p_a_t, _) ->
     let env_a = zoom_env zoom_product_type env_pms p_a_t in
     let nargs = new_rels env_a npm in
     let p = index_motive idx npm env_a in
     bind
       (indexer_cases env_pms off (shift p) nargs a b)
       (fun cs ->
         let app =
           apply_eliminator
             {
               elim = elim_a;
               pms = shift_all_by nargs (mk_n_rels npm);
               p = shift_by nargs p;
               cs;
               final_args = mk_n_rels nargs;
             }
         in ret (reconstruct_lambda env_a app))
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
let promote_forget_case env sigma off is_fwd p o n : types state =
  let directional a b = if is_fwd then a else b in
  let rec sub p p_a_b subs e o n =
    let (ind_o, c_o) = o in
    let (ind_n, c_n) = n in
    match map_tuple kind (c_o, c_n) with
    | (App (f_o, args_o), App (f_n, args_n)) ->
       (* PROMOTE-CONCLUSION / FORGET-CONCLUSION *)
       ret (List.fold_right all_eq_substs subs (last_arg c_n))
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let sub_b = sub (shift p) (shift p_a_b) in
       branch_state
         (fun (o, n) ->
           optimized_is_new e off p_a_b (directional o n) (directional n o))
         (fun (o, n) ->
           (* PROMOTE-HYPOTHESIS and FORGET-HYPOTHESIS *)
           let o = (shift ind_o, directional (shift c_o) b_o) in
           let n = (shift ind_n, directional b_n (shift c_n)) in
           bind
             (sub_b (shift_subs subs) (push_local (n_n, t_n) e) o n)
             (fun b ->
               ret ((directional unshift (fun b -> mkLambda (n_o, t_o, b))) b)))
         (fun (o, n) ->
           let e_b = push_local (n_o, t_o) e in
           let o = (shift ind_o, b_o) in
           let n = (shift ind_n, b_n) in
           if apply p_a_b t_o t_n then
             (* PROMOTE-IH / FORGET-IH *)
             let ib_sub = map_tuple shift (map_tuple (get_arg off) (t_n, t_o)) in
             let ih_sub = (shift (last_arg t_n), mkRel 1) in
             let subs_b = List.append [ib_sub; ih_sub] (shift_subs subs) in
             bind
               (sub_b subs_b e_b o n)
               (fun b -> ret (mkLambda (n_o, mkAppl (p, unfold_args t_o), b)))
           else
             (* PROMOTE-PROD / FORGET-PROD *)
             bind
               (sub_b (shift_subs subs) e_b o n)
               (fun b -> ret (mkLambda (n_o, t_o, b))))
         (o, n)
    | _ ->
       CErrors.user_err unsupported_change_error
  in sub p (mkRel 1) [] env o n sigma

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
let promote_forget_cases env off is_fwd orn_p nargs o n =
  let directional a b = if is_fwd then a else b in
  let (o_t, elim_o_t) = o in
  let (n_t, elim_n_t) = n in
  let (n_o, p_o_t, b_o) = destProd elim_o_t in
  let (_, p_n_t, b_n) = destProd elim_n_t in
  let adjust p = shift (stretch_motive off env (o_t, p) (n_t, p_n_t)) in
  let p = map_if adjust is_fwd (unshift orn_p) in
  map2_state
    (fun c_o c_n sigma ->
      Util.on_snd
        (shift_by (directional (nargs - 1) (nargs - 2)))
        (promote_forget_case env sigma off is_fwd p (o_t, c_o) (n_t, c_n)))
    (take_except nargs (factor_product b_o))
    (take_except (directional (nargs + 1) (nargs - 1)) (factor_product b_n))

(*
 * Make a packer function for existT/sigT
 *)
let make_packer env b_typ args (off, ib_typ) is_fwd sigma : types state =
  let sub_index = if is_fwd then insert_index else reindex in
  let packed_args = sub_index off (mkRel 1) (shift_all args) in
  let env_abs = push_local (Anonymous, ib_typ) env in
  abstract_arg env_abs sigma off (mkAppl (b_typ, packed_args))

(*
 * Pack the conclusion of an ornamental promotion
 *)
let pack_conclusion f_indexer env idx b unpacked =
  let (b_typ, arity) = b in
  let off = arity - 1 in
  let index_type = shift_by off (snd idx) in
  bind
    (make_packer env b_typ (mk_n_rels off) idx true)
    (fun packer ->
      let index = mkAppl (f_indexer, mk_n_rels arity) in
      ret (env, pack_existT {index_type; packer; index; unpacked}))

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
let apply_packer env sigma packer arg =
  reduce_stateless reduce_term env sigma (mkAppl (packer, [arg]))

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
let pack_unpacked env sigma packer ib_typ ib_rel unpacked =
  let sub_typ = all_eq_substs (mkRel (4 - ib_rel), mkRel 1) in
  let sub_index = all_eq_substs (mkRel (ib_rel + 3), mkRel 2) in
  let adjust trm = shift_local ib_rel 1 (shift trm) in
  let typ_body = sub_index (sub_typ (adjust unpacked)) in
  let packer_indexed = apply_packer env sigma (shift packer) (mkRel 1) in
  let index_body = mkLambda (Anonymous, packer_indexed, typ_body) in
  mkLambda (Anonymous, shift ib_typ, index_body)

(*
 * Pack the hypothesis of an ornamental forgetful function
 *)
let pack_hypothesis env idx b unpacked sigma =
  let (off, ib_typ) = (fst idx, shift (snd idx)) in
  let (b_typ, _) = b in
  let (id, _, unpacked_typ) = CRD.to_tuple @@ lookup_rel 1 env in
  let (sigma, packer) = make_packer env b_typ (unfold_args unpacked_typ) idx false sigma in
  let env_push = pack_hypothesis_type env ib_typ packer (id, unpacked_typ) in
  let ib_rel = new_rels (pop_rel_context 1 env) off in
  let unpacked = pack_unpacked env_push sigma packer ib_typ ib_rel unpacked in
  let adjusted = adjust_to_elim env_push ib_rel packer unpacked in
  let (env_packed, packer, unpacked) = adjusted in
  let arg = mkRel 1 in
  let arg_typ = on_red_type_default (ignore_env dest_sigT) env_packed sigma arg in
  let (index, value) = projections arg_typ arg in
  sigma, (env_packed, reduce_stateless reduce_term env_packed sigma (mkAppl (unpacked, [index; value])))

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
let find_promote_or_forget env_pms idx indexer_n o n is_fwd =
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
  bind
    (promote_forget_cases env_pms off is_fwd (adj (shift p)) nargs o n)
    (fun cs ->
      let unpacked =
        apply_eliminator
          {
            elim = elim;
            pms = shift_all_by nargs (mk_n_rels npm);
            p = shift_by nargs p;
            cs = List.map adj cs;
            final_args = mk_n_rels nargs;
          }
      in
      let o = (o_typ, arity_o) in
      let n = (n_typ, arity_n) in
      let idx = (npm + off, idx_t) in
      let b = directional n o in
      bind
        (pack_orn f_indexer is_fwd env_p_o idx b unpacked)
        (fun (env_packed, packed) ->
          ret (reconstruct_lambda env_packed packed)))

(* Find promote and forget, using a directional flag for abstraction *)
let find_promote_forget env_pms idx indexer_n a b =
  bind
    (find_promote_or_forget env_pms idx indexer_n a b true)
    (fun f ->
      bind
        (find_promote_or_forget env_pms idx indexer_n b a false)
        (fun g ->
          ret (f, g)))

(* --- Algebraic ornaments --- *)
              
(*
 * Search two inductive types for an algebraic ornament between them
 *)
let search_algebraic env sigma npm indexer_n a b =
  let (a_typ, arity_a) = a in
  let (b_typ, arity_b) = b in
  let lookup_elim typ = type_eliminator env (fst (destInd typ)) in
  let (el_a, el_b) = map_tuple lookup_elim (a_typ, b_typ) in
  let sigma, (env_pms, el_a_typ) = on_type (fun env sigma t -> sigma, zoom_n_prod env npm t) env sigma el_a in
  let sigma, (_, el_b_typ) = on_type (fun env sigma t -> sigma, zoom_n_prod env npm t) env sigma el_b in
  let a = (a_typ, el_a_typ) in
  let b = (b_typ, el_b_typ) in
  let sigma, idx = offset_and_ib env_pms a b sigma in (* idx = (off, I_B) *)
  let sigma, indexer = find_indexer env_pms idx el_a a b sigma in
  let indexer = Some indexer in
  let a = (a_typ, arity_a, el_a, el_a_typ) in
  let b = (b_typ, arity_b, el_b, el_b_typ) in
  let sigma, (promote, forget) = find_promote_forget env_pms idx indexer_n a b sigma in
  sigma, { indexer; promote; forget; kind = Algebraic }

(* --- Records and products --- *)

(*
 * TODO comment, clean
 * TODO break into two files above top-level search function:
 * algebraic and curry
 * TODO better error messages for failure cases, e.g. when don't match order or when number of
 * fields doesn't match or only one field
 *)

(*
 * TODO appropriate error message for indices, which shouldn't exist
 * TODO check/fix w/ params that are used
 * TODO get proof generation working
 * TODO then lifting
 *)
let search_curry_record env_pms sigma a_ind b =
  let npm = nb_rel env_pms in
  let pms = mk_n_rels npm in
  let a = mkAppl (mkInd a_ind, pms) in
  let b = mkAppl (b, pms) in
  let sigma, promote =
    let elim = type_eliminator env_pms a_ind in
    let sigma, (_, elim_typ) = on_type (fun env sigma t -> sigma, zoom_n_prod env npm t) (Global.env ()) sigma elim in
    let (p_n, _, elim_body) = destProd elim_typ in
    let p = mkLambda (Anonymous, a, shift b) in
    let env_p = push_local (p_n, p) env_pms in
    let env_arg = push_local (Anonymous, a) env_pms in
    let (_, c_typ, _) = destProd elim_body in
    let env_c, _ = zoom_product_type env_p c_typ in
    let rec make_c n sigma =
      let trm1 = mkRel n in
      if n = 1 then
        sigma, trm1
      else
        let sigma, trm2 = make_c (n - 1) sigma in
        let sigma, typ1 = infer_type env_c sigma trm1 in
        let sigma, typ2 = infer_type env_c sigma trm2 in
        sigma, apply_pair { typ1; typ2; trm1; trm2 }
    in
    let sigma, c = make_c (new_rels2 env_c env_p) sigma in
    let cs = [reconstruct_lambda_n env_c c (nb_rel env_p)] in
    let app =
      apply_eliminator
        {
          elim = elim;
          pms = shift_all pms;
          p = shift p;
          cs = cs;
          final_args = mk_n_rels 1;
        }
    in sigma, reconstruct_lambda env_arg app
  in
  let sigma, forget =
    let env_arg = push_local (Anonymous, b) env_pms in
    let c = mkAppl (mkConstruct (a_ind, 1), shift_all pms) in
    let rec make_args n arg sigma =
      let sigma, arg_typ = reduce_type env_arg sigma arg in
      let sigma, arg_typ =
        if equal (first_fun arg_typ) prod then
          sigma, arg_typ
        else
          let f = unwrap_definition env_arg (first_fun arg_typ) in
          let pms = unfold_args arg_typ in
          reduce_term env_arg sigma (mkAppl (f, pms))
      in
      let prod_app = dest_prod arg_typ in
      if n = 2 then
        sigma, [prod_fst_elim prod_app arg; prod_snd_elim prod_app arg]
      else
        let sigma, args = make_args (n - 1) (prod_snd_elim prod_app arg) sigma in
        sigma, List.append [prod_fst_elim prod_app arg] args
    in
    let sigma, c_typ = reduce_type env_arg sigma c in
    let sigma, args = make_args (arity c_typ) (mkRel 1) sigma in
    let app = mkAppl (c, args) in
    sigma, reconstruct_lambda env_arg app
  in
  let indexer = None in
  sigma, { promote; forget; indexer; kind = CurryRecord }

(* --- Top-level search --- *)

(*
 * Search two inductive types for an ornament between them.
 * This is more general to handle eventual extension with other 
 * kinds of ornaments.
 *)
let search_orn_inductive env sigma indexer_id_opt trm_o trm_n =
  match map_tuple kind (trm_o, trm_n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if not (npm_o = npm_n) then
       (* new parameter *)
       CErrors.user_err new_parameter_error
     else
       let (bs_o, bs_n) = map_tuple (fun m -> m.mind_packets) (m_o, m_n) in
       let (b_o, b_n) = map_tuple (fun bs -> Array.get bs 0) (bs_o, bs_n) in
       let (cs_o, cs_n) = map_tuple (fun m -> m.mind_consnames) (b_o, b_n) in
       if not (Array.length cs_o = Array.length cs_n) then
         CErrors.user_err new_constructor_error
       else
         let npm = npm_o in
         let (typ_o, typ_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
         let (arity_o, arity_n) = map_tuple arity (typ_o, typ_n) in
         if Option.has_some indexer_id_opt && not (arity_o = arity_n) then
           (* new index *)
           let o = (trm_o, arity_o) in
           let n = (trm_n, arity_n) in
           let (a, b) = map_if reverse (arity_n <= arity_o) (o, n) in
           search_algebraic env sigma npm (Option.get indexer_id_opt) a b
         else
           CErrors.user_err unsupported_change_error             
  | _ ->
     failwith "Called search_orn_inductive on non-inductive types!"

(*
 * Search two types for an ornament between them, where one type
 * is an inductive type and the other is something else (like an application
 * of an inductive type). This is more general to handle eventual extensions
 * with other kinds of ornaments.
 *)
let search_orn_one_noninductive env sigma trm_o trm_n =
  let ind, non_ind = if isInd trm_o then (trm_o, trm_n) else (trm_n, trm_o) in
  let ((i, _), _) = destInd ind in
  let m = lookup_mind i env in
  check_inductive_supported m;
  let non_ind_inner = unwrap_definition env non_ind in
  let sigma, non_ind_inner = reduce_term env sigma non_ind_inner in
  let env, non_ind_inner = zoom_lambda_term env non_ind_inner in
  match kind non_ind_inner with
  | App _ ->
     let f = unwrap_definition env (first_fun non_ind_inner) in
     if equal f prod then
       let npm = m.mind_nparams in
       let bs = m.mind_packets in
       let ncs = Array.length (Array.get bs 0).mind_consnames in
       if npm = nb_rel env && ncs = 1 then
         (* Curry a record into an application of prod *)
         search_curry_record env sigma (fst (destInd ind)) non_ind
       else
         CErrors.user_err unsupported_change_error
     else
       CErrors.user_err unsupported_change_error
  | _ ->
     CErrors.user_err unsupported_change_error
              
(*
 * Search two types for an ornament between them.
 * This is more general to handle eventual extension with other 
 * kinds of ornaments.
 *)
let search_orn env sigma indexer_id_opt trm_o trm_n =
  if isInd trm_o && isInd trm_n && Option.has_some indexer_id_opt then
    (* Ornament between two inductive types *)
    search_orn_inductive env sigma indexer_id_opt trm_o trm_n
  else if isInd trm_o || isInd trm_n then
    (* Ornament between an inductive type and something else *)
    search_orn_one_noninductive env sigma trm_o trm_n
  else
    CErrors.user_err unsupported_change_error
