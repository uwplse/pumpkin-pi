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
open Desugarprod
open Ornerrors
open Convertibility
open Promotion
open Equtils
open Libnames
open Nametab
open Specialization
       
(* --- Common code --- *)
       
(*
 * Find promote and forget, using a directional flag for abstraction
 *)
let find_promote_forget find_promote_or_forget promote_o forget_o sigma =
  let sigma, promote =
    if Option.has_some promote_o then
      sigma, Option.get promote_o
    else
      find_promote_or_forget true sigma
  in
  let sigma, forget =
    if Option.has_some forget_o then
      sigma, Option.get forget_o
    else
      find_promote_or_forget false sigma
  in sigma, (promote, forget)

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
        ret (computes_ih_index env off (shift env p) (mkRel 1) b_b))

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
       ret (List.fold_right (all_eq_substs env) subs (get_arg off c_b))
    | (Prod (n_a, t_a, b_a), Prod (n_b, t_b, b_b)) ->
       let diff_b = diff_case (shift env p) (shift env p_a_b) in
       branch_state
         (optimized_is_new e off p_a_b a)
         (fun _ -> 
           (* INDEX-HYPOTHESIS *)
           let a = map_tuple (shift env) a in
           let b = (shift env b_t, b_b) in
           bind
             (diff_b (shift_subs env subs) (push_local (n_b.binder_name, t_b) e) a b)
             (fun b -> ret (unshift env b)))
         (fun _ ->
           let e_b = push_local (n_a.binder_name, t_a) e in
           let a = (shift env a_t, b_a) in
           let b = (shift env b_t, b_b) in
           if apply p_a_b t_a t_b then
             (* INDEX-IH *)
             let sub_index = (shift env (get_arg off t_b), mkRel 1) in
             let subs_b = sub_index :: shift_subs env subs in
             bind
               (diff_b subs_b e_b a b)
               (fun b -> ret (mkLambda (n_a, mkAppl (p, unfold_args t_a), b)))
           else
             (* INDEX-PROD *)
             bind
               (diff_b (shift_subs env subs) e_b a b)
               (fun b -> ret (mkLambda (n_a, t_a, b))))
         b
    | _ ->
       user_err
         "index_case"
         err_unsupported_change
         [try_supported]
         [cool_feature; mistake]
  in diff_case p (mkRel 1) [] env a b sigma

(* Get the cases for the indexer *)
let indexer_cases env off p nargs a b =
  let (a_t, elim_t_a) = a in
  let (b_t, elim_t_b) = b in
  match map_tuple kind (elim_t_a, elim_t_b) with
  | (Prod (n_a, p_a_t, b_a), Prod (_, _, b_b)) ->
     let env_p_a = push_local (n_a.binder_name, p_a_t) env in
     map2_state
       (fun c_a c_b sigma ->
         Util.on_snd
           (shift_by env (nargs - 1))
           (index_case env_p_a sigma off p (a_t, c_a) (b_t, c_b)))
       (take_except nargs (factor_product env b_a))
       (take_except (nargs + 1) (factor_product env b_b))
  | _ ->
     raise NotEliminators

(* Find the motive for the indexer (INDEX-MOTIVE) *)
let index_motive env idx npm env_a =
  let (off, ib_t) = idx in
  let ib_t = shift_by env (npm + off) ib_t in
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
     let p = index_motive env_pms idx npm env_a in
     bind
       (indexer_cases env_pms off (shift env_pms p) nargs a b)
       (fun cs ->
         let app =
           apply_eliminator
             {
               elim = elim_a;
               pms = shift_all_by env_pms nargs (mk_n_rels npm);
               p = shift_by env_pms nargs p;
               cs;
               final_args = mk_n_rels nargs;
             }
         in ret (reconstruct_lambda env_a app))
  | _ ->
     raise NotEliminators

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
     let n_b = (shift env n_typ, b_n) in
     if off = 0 then
       mkProd (n_n, t_n, shift env p_o_typ)
     else
       let env_b = push_local (n_o.binder_name, t_o) env in
       let o_b = (shift env o_typ, b_o) in
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
    map_term_if env
      (fun (p, _) t -> applies p t)
      (fun (p, pms) t ->
        let non_pms = unfold_args t in
        let index = mkAppl (indexer, List.append pms non_pms) in
        mkAppl (p, insert_index off index non_pms))
      (fun (p, pms) -> (shift env p, shift_all env pms))
      (mkRel 1, shift_all env (mk_n_rels npm))
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
        (n.binder_name, unshift_local env (i - j - 1) 1 t))
      (List.rev (List.tl (List.rev popped)))
  in List.fold_right push_local push env_pop

(* --- Algebraic ornaments --- *)

(*
 * Find the motive that the ornamental promotion or forgetful function proves
 * for an indexing function (PROMOTE-MOTIVE and FORGET-MOTIVE)
 *)
let promote_forget_motive off env t arity npm indexer_opt =
  let args = shift_all env (mk_n_rels arity) in
  let concl =
    match indexer_opt with
    | Some indexer ->
       (* PROMOTE-MOTIVE *)
       let indexer = Option.get indexer_opt in
       let index = mkAppl (indexer, snoc (mkRel 1) args) in
       mkAppl (t, insert_index (npm + off) index args)
    | None ->
       (* FORGET-MOTIVE *)
       mkAppl (t, adjust_no_index env (npm + off) (shift_all env args))
  in reconstruct_lambda_n env concl npm

(*
 * Substitute indexes and IHs in a case of promote or forget 
 *)
let promote_forget_case_algebraic env sigma off is_fwd p o n : types state =
  let directional a b = if is_fwd then a else b in
  let rec sub p p_a_b subs e o n =
    let (ind_o, c_o) = o in
    let (ind_n, c_n) = n in
    match map_tuple kind (c_o, c_n) with
    | (App (f_o, args_o), App (f_n, args_n)) ->
       (* PROMOTE-CONCLUSION / FORGET-CONCLUSION *)
       ret (List.fold_right (all_eq_substs env) subs (last_arg c_n))
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let sub_b = sub (shift env p) (shift env p_a_b) in
       branch_state
         (fun (o, n) ->
           optimized_is_new e off p_a_b (directional o n) (directional n o))
         (fun (o, n) ->
           (* PROMOTE-HYPOTHESIS and FORGET-HYPOTHESIS *)
           let o = (shift env ind_o, directional (shift env c_o) b_o) in
           let n = (shift env ind_n, directional b_n (shift env c_n)) in
           bind
             (sub_b (shift_subs env subs) (push_local (n_n.binder_name, t_n) e) o n)
             (fun b ->
               ret ((directional (unshift env) (fun b -> mkLambda (n_o, t_o, b))) b)))
         (fun (o, n) ->
           let e_b = push_local (n_o.binder_name, t_o) e in
           let o = (shift env ind_o, b_o) in
           let n = (shift env ind_n, b_n) in
           if apply p_a_b t_o t_n then
             (* PROMOTE-IH / FORGET-IH *)
             let ib_sub = map_tuple (shift env) (map_tuple (get_arg off) (t_n, t_o)) in
             let ih_sub = (shift env (last_arg t_n), mkRel 1) in
             let subs_b = List.append [ib_sub; ih_sub] (shift_subs env subs) in
             bind
               (sub_b subs_b e_b o n)
               (fun b -> ret (mkLambda (n_o, mkAppl (p, unfold_args t_o), b)))
           else
             (* PROMOTE-PROD / FORGET-PROD *)
             bind
               (sub_b (shift_subs env subs) e_b o n)
               (fun b -> ret (mkLambda (n_o, t_o, b))))
         (o, n)
    | _ ->
       user_err
         "promote_forget_case_algebraic"
         err_unsupported_change
         [try_supported]
         [cool_feature; mistake]
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
let promote_forget_cases_algebraic env off is_fwd orn_p nargs o n =
  let directional a b = if is_fwd then a else b in
  let (o_t, elim_o_t) = o in
  let (n_t, elim_n_t) = n in
  let (n_o, p_o_t, b_o) = destProd elim_o_t in
  let (_, p_n_t, b_n) = destProd elim_n_t in
  let adjust p = shift env (stretch_motive off env (o_t, p) (n_t, p_n_t)) in
  let p = map_if adjust is_fwd (unshift env orn_p) in
  map2_state
    (fun c_o c_n sigma ->
      Util.on_snd
        (shift_by env (directional (nargs - 1) (nargs - 2)))
        (promote_forget_case_algebraic env sigma off is_fwd p (o_t, c_o) (n_t, c_n)))
    (take_except nargs (factor_product env b_o))
    (take_except (directional (nargs + 1) (nargs - 1)) (factor_product env b_n))

(*
 * Make a packer function for existT/sigT
 *)
let make_packer env b_typ args (off, ib_typ) is_fwd sigma : types state =
  let sub_index = if is_fwd then insert_index else reindex in
  let packed_args = sub_index off (mkRel 1) (shift_all env args) in
  let env_abs = push_local (Anonymous, ib_typ) env in
  abstract_arg env_abs sigma off (mkAppl (b_typ, packed_args))

(*
 * Pack the conclusion of an ornamental promotion
 *)
let pack_conclusion f_indexer env idx b unpacked =
  let (b_typ, arity) = b in
  let off = arity - 1 in
  let index_type = shift_by env off (snd idx) in
  bind
    (make_packer env b_typ (mk_n_rels off) idx true)
    (fun packer ->
      let index = mkAppl (f_indexer, mk_n_rels arity) in
      ret (env, pack_existT {index_type; packer; index; unpacked}))

(*
 * Pack the hypothesis type into a sigT, and update the environment
 *)
let pack_hypothesis_type env ib_typ packer (id, unpacked_typ) : env =
  let packer = unshift env packer in
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
  let adjust = unshift_local env ib_rel 1 in
  (env_packed, adjust packer, adjust packed)

(*
 * Pack the unpacked term to eliminate using the new hypothesis
 *)
let pack_unpacked env sigma packer ib_typ ib_rel unpacked =
  let sub_typ = all_eq_substs env (mkRel (4 - ib_rel), mkRel 1) in
  let sub_index = all_eq_substs env (mkRel (ib_rel + 3), mkRel 2) in
  let adjust trm = shift_local env ib_rel 1 (shift env trm) in
  let typ_body = sub_index (sub_typ (adjust unpacked)) in
  let packer_indexed = apply_packer env sigma (shift env packer) (mkRel 1) in
  let index_body = mkLambda (get_rel_ctx_name Anonymous, packer_indexed, typ_body) in
  mkLambda (get_rel_ctx_name Anonymous, shift env ib_typ, index_body)

(*
 * Pack the hypothesis of an ornamental forgetful function
 *)
let pack_hypothesis env idx b unpacked sigma =
  let (off, ib_typ) = (fst idx, shift env (snd idx)) in
  let (b_typ, _) = b in
  let (id, _, unpacked_typ) = CRD.to_tuple @@ lookup_rel 1 env in
  let (sigma, packer) = make_packer env b_typ (unfold_args unpacked_typ) idx false sigma in
  let env_push = pack_hypothesis_type env ib_typ packer (id.binder_name, unpacked_typ) in
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
let find_promote_or_forget_algebraic env_pms idx indexer_n a b is_fwd sigma =
  let directional x y = if is_fwd then x else y in
  let (o, n) = directional (a, b) (b, a) in
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
  let adj = directional identity (shift env_pms) in
  let sigma, cs = promote_forget_cases_algebraic env_pms off is_fwd (adj (shift env_pms p)) nargs o n sigma in
  let unpacked =
    apply_eliminator
      {
        elim;
        pms = shift_all_by env_pms nargs (mk_n_rels npm);
        p = shift_by env_pms nargs p;
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
      ret (reconstruct_lambda env_packed packed))
    sigma

(*
 * Find promote and forget, using a directional flag for abstraction
 *)
let find_promote_forget_algebraic env_pms idx indexer_n promote_o forget_o a b =
  find_promote_forget
    (find_promote_or_forget_algebraic env_pms idx indexer_n a b)
    promote_o
    forget_o
              
(*
 * Search two inductive types for an algebraic ornament between them
 *)
let search_algebraic env sigma npm indexer_n promote_o forget_o a b =
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
  let a = (a_typ, arity_a, el_a, el_a_typ) in
  let b = (b_typ, arity_b, el_b, el_b_typ) in
  let sigma, (promote, forget) = find_promote_forget_algebraic env_pms idx indexer_n promote_o forget_o a b sigma in
  sigma, { promote; forget; kind = Algebraic (indexer, fst idx + npm) }

(* --- Swapping constructors --- *)

(*
 * This looks a lot like algebraic, except that there is no new index
 * (and so no indexer and no packing/unpacking), but on the other hand we
 * must swap the constructor order.
 *
 * There are sometimes many possible equivalences that correspond to this, so
 * we start by enumerating the first n of those possible equivalences.
 * We don't enumerate all because the total number of possible equivalences
 * is, for each group of n_i constructors of the same type t_i, the product of
 * all of the (n_i!).
 *)

(*
 * Find all permutations of l that result from swapping either zero or one
 * elements in the list. This is used to figure out which equivalences are
 * possible and enumerate them in a reasonable order
 *)
let rec zero_one_swaps l =
  match l with
  | [] ->
     []
  | h :: [] ->
     [[h]]
  | h :: tl ->
     let h_perms =
       List.mapi
         (fun i _ ->
           let tl1, tl2 = split_at (i + 1) tl in
           let h2 = last tl1 in
           List.append (h2 :: all_but_last tl1) (h :: tl2))
         tl
     in List.append (List.map (fun l -> h :: l) (zero_one_swaps tl)) h_perms

(*
 * Also for reasonable enumeration order, we provide a way to filter out
 * duplicate lists of swaps:
 *)                    
let same cs cs' =
  List.for_all2 (fun c c' -> equal (mkConstructU c) (mkConstructU c')) cs cs'

(*
 * And a way of determining when we've visited a swap map before:
 *)
let visited seen swaps =
  List.for_all
    (fun swaps' -> not (same swaps' swaps))
    seen
  
                
(*
 * Now we can get the n most likely swap maps. Most of the mess here is
 * to enumerate those initial maps in a reasonable order. That means
 * that this algorithm is not the most efficient for small lists,
 * but we get a reasonable top 50 for large lists.
 *
 * The enumeration order here starts with zero swaps, then one swap,
 * then two swaps, and so on, for each group of ambiguous constructors.
 *)
let rec get_likely_swap_maps n swaps =
  (* Because of the strange enumeration order, we use fuel to terminate *)
  let rec cs_swap_maps fuel seen cs_a cs_bs =
    let swaps = List.map (List.combine cs_a) cs_bs in
    if List.length swaps > n || fuel = 0 then
      take n swaps
    else
      let cs_bs = List.filter (visited seen) (flat_map zero_one_swaps cs_bs) in
      let cs_bs = unique same cs_bs in
      let seen = List.append seen cs_bs in
      take n (List.append swaps (cs_swap_maps (fuel - 1) seen cs_a cs_bs))
  in
  (* Now we do this for each group of ambiguous constructors *)
  match swaps with
  | (_, ((cs_a, cs_b), _)) :: tl ->
     let swap_maps = get_likely_swap_maps n tl in
     let swaps = cs_swap_maps (List.length cs_b - 1) [cs_b] cs_a [cs_b] in
     if List.length swap_maps = 0 then
       take n swaps
     else
       let swap_maps =
         flat_map
           (fun swap_map -> List.map (List.append swap_map) swaps)
           swap_maps
       in take n swap_maps
  | _ ->
     []

(*
 * OK, now when there are many possible maps, we prompot the user
 * for more information and show them the top 50 that we found.
 *
 * Eventually, this would be better using Lemmas.add_lemma or something
 * similar. For now, we just require the user to tell us which one
 * using `Save ornament`.
 *)
let prompt_swap_ambiguous env swap_maps ambiguous sigma =
  let num_solutions =
    List.fold_left
      (fun n (_, ((ms_o, _), _)) ->
        if n = "1" then
          Printf.sprintf "%d!" (List.length ms_o)
        else
          let len = List.length ms_o in
          if len = 1 then
            n
          else
            Printf.sprintf "%s * %d!" n len)
      "1"
      ambiguous
  in
  user_err
    "prompt_swap_ambiguous"
    (err_ambiguous_swap env num_solutions swap_maps sigma)
    []
    []

(*
 * OK, now that we've found that, we can find the actual equivalence.
 *
 * Find the motive for promote or forget for swapping constructors
 *)
let find_motive_swap env_motive typ nargs pms =
  let typ_args = List.append (shift_all_by env_motive nargs pms) (shift_all env_motive (mk_n_rels (nargs - 1))) in
  let p_b = mkAppl (typ, typ_args) in
  reconstruct_lambda_n env_motive p_b (List.length pms)

(*
 * Find the cases for promote or forget for swapping constructors
 *)
let find_cases_swap env p elim_p_typ swap_map o nargs sigma =
  let env_p = push_local (Anonymous, p) env in
  let ncons = List.length swap_map in
  List.mapi
    (fun i c ->
      let env_c_b, c_b = zoom_product_type env_p (shift_by env_p (nargs - 1) c) in
      let (ind, u) = destInd o in
      let constr_from = ((ind, (i + 1)), u) in
      let constr_to = List.assoc constr_from swap_map in
      let hyps =
        List.mapi
          (fun j rel ->
            match rel with
            | CRD.(LocalAssum (n, t)) ->
               j + 1, shift_by env_p (j + 1) t
            | CRD.(LocalDef (n, e, t)) ->
               j + 1, shift_by env_p (j + 1) t)
          (lookup_all_rels env_c_b)
      in
      let p_rel = first_fun c_b in
      let constr_app = last_arg c_b in
      let args = unfold_args constr_app in
      let sigma, args_sub =
        map_state
          (fun arg sigma ->
            try
              let ih_i, _ =
                List.find
                  (fun (j, h_t) ->
                    isApp h_t && applies p_rel h_t && equal (last_arg h_t) arg)
                  hyps
              in sigma, mkRel ih_i
            with _ ->
              sigma, arg)
          args
          sigma
      in
      let constr_ih = mkAppl (mkConstructU constr_to, args_sub) in
      let c_p = reconstruct_lambda_n env_c_b constr_ih (nb_rel env_p) in
      all_eq_substs env_p (mkRel nargs, shift_by env_p nargs p) c_p)
    (take ncons (factor_product env_p elim_p_typ))
        
(*
 * Find promote or forget for swapping constructors
 *)
let find_promote_or_forget_swap env npm swap_map a b is_fwd sigma =
  let directional x y = if is_fwd then x else y in
  let (o, n) = directional (a, b) (b, a) in
  let swap_map = if is_fwd then swap_map else List.map reverse swap_map in
  let elim = type_eliminator env (fst (destInd o)) in
  let sigma, (env_pms, elim_typ) = on_type (fun env sigma t -> sigma, zoom_n_prod env npm t) env sigma elim in
  let pms = mk_n_rels npm in
  let (_, p_typ, elim_p_typ) = destProd elim_typ in
  let env_p_b = zoom_env zoom_product_type env_pms p_typ in
  let nargs = new_rels2 env_p_b env_pms in
  let p = find_motive_swap env_p_b n nargs pms in
  let cs = find_cases_swap env_pms p elim_p_typ swap_map o nargs sigma in
  let app =
    apply_eliminator
      {
        elim;
        pms = shift_all_by env_p_b nargs pms;
        p = shift_by env_p_b nargs p;
        cs;
        final_args = mk_n_rels nargs;
      }
  in sigma, reconstruct_lambda env_p_b app

(*
 * Find promote and forget for swapping constructors
 *)
let find_promote_forget_swap env npm swaps promote_o forget_o a b sigma =
  let sigma, (promote, forget) =
    find_promote_forget
      (find_promote_or_forget_swap env npm swaps a b)
      promote_o
      forget_o
      sigma
  in
  let swaps_ints = List.map (fun (((_, i), _), ((_, j), _)) -> i, j) swaps in
  sigma, { promote ; forget ; kind = SwapConstruct swaps_ints }
           
(*
 * Search for the components of the equivalence for swapping constructors
 *)
let search_swap_constructor env npm grouped swap_i_o promote_o forget_o a b sigma =
  let sigma, swap_map =
    if Option.has_some promote_o || Option.has_some forget_o then
      swap_map_of_promote_or_forget env a b promote_o forget_o sigma
    else
      let swaps =
        List.map
          (fun (repr, (ms, typ_a)) ->
            let (ms_a, ms_b) = List.partition (fun ((i, _), _) -> equal (mkInd i) a) ms in
            let typ_b = all_eq_substs env (a, b) typ_a in
            (repr, ((List.rev ms_a, List.rev ms_b), (typ_a, typ_b))))
          grouped
      in
      let ambiguous = List.filter (fun (_, ((ms_a, _), _)) -> List.length ms_a > 1) swaps in
      if List.length ambiguous > 0 then
        (* Ambiguous; need more information *)
        let swap_maps = get_likely_swap_maps 50 swaps in
        if Option.has_some swap_i_o then
          (* The user gave us this information already *)
          let swap_i = Option.get swap_i_o in
          sigma, List.nth swap_maps swap_i
        else
          (* We ask the user to give us that information *)
          sigma, prompt_swap_ambiguous env swap_maps ambiguous sigma
      else
        (* Unambiguous *)
        map_state
          (fun (_ , ((ms_a, ms_b), _)) -> ret (List.hd ms_a, List.hd ms_b))
          swaps
          sigma
  in find_promote_forget_swap env npm swap_map promote_o forget_o a b sigma
           
(* --- Records and products --- *)

(*
 * Search for promote/forget for curry record.
 * For promote, eliminate the record and recursively construct a product.
 * For forget, recursively eliminate the product and construct a record.
 *)            
let find_promote_or_forget_curry_record env_pms a b is_fwd sigma =
  let directional x y = if is_fwd then x else y in
  let npm = nb_rel env_pms in
  let pms = mk_n_rels npm in
  let a_pms = mkAppl (a, pms) in
  let b_pms = mkAppl (b, pms) in
  let env_arg = push_local (Anonymous, directional a_pms b_pms) env_pms in
  let pms = shift_all env_arg pms in
  let a_pms, b_pms = map_tuple (shift env_arg) (a_pms, b_pms) in
  let c_a = mkAppl (mkConstruct (fst (destInd a), 1), pms) in
  let sigma, c_a_typ = reduce_type env_arg sigma c_a in
  let num_hyps = arity c_a_typ in
  let arg = mkRel 1 in
  let sigma, body =
    if is_fwd then
      let elim = type_eliminator env_pms (fst (destInd a)) in
      let p = mkLambda (get_rel_ctx_name Anonymous, a_pms, shift env_arg b_pms) in
      let sigma, cs =
        let env_c = zoom_env zoom_product_type env_arg c_a_typ in
        let rec make_c n sigma =
          let trm1 = mkRel n in
          if n = 1 then
            sigma, trm1
          else
            let sigma, trm2 = make_c (n - 1) sigma in
            let sigma, typ1 = infer_type env_c sigma trm1 in
            let sigma, typ2 = infer_type env_c sigma trm2 in
            sigma, apply_pair Produtils.{ typ1; typ2; trm1; trm2 }
        in
        let sigma, c = make_c num_hyps sigma in
        sigma, [reconstruct_lambda_n env_c c (nb_rel env_arg)]
      in
      let final_args = [arg] in
      sigma, apply_eliminator { elim; pms; p; cs; final_args }
    else
      let rec make_args n arg sigma =
        let sigma, arg_typ =
          let sigma, arg_typ = reduce_type env_arg sigma arg in
          if equal (first_fun arg_typ) prod then
            sigma, arg_typ
          else
            let f = unwrap_definition env_arg (first_fun arg_typ) in
            let pms = unfold_args arg_typ in
            reduce_term env_arg sigma (mkAppl (f, pms))
        in
        let prod_app = dest_prod arg_typ in
        let fst_elim, snd_elim = prod_projections_elim prod_app arg in
        if n = 2 then
          sigma, [fst_elim; snd_elim]
        else
          let sigma, args = make_args (n - 1) snd_elim sigma in
          sigma, fst_elim :: args
      in
      let sigma, args = make_args num_hyps arg sigma in
      sigma, mkAppl (c_a, args)
  in sigma, reconstruct_lambda env_arg body

(*
 * Find both promote and forget for curry_record
 *)
let find_promote_forget_curry_record env_pms promote_o forget_o a b =
  find_promote_forget
    (find_promote_or_forget_curry_record env_pms a b)
    promote_o
    forget_o

(*
 * Search for the components of the equivalence for curry_record
 *)
let search_curry_record env_pms sigma promote_o forget_o a b =
  let sigma, (promote, forget) = find_promote_forget_curry_record env_pms promote_o forget_o a b sigma in
  sigma, { promote; forget; kind = CurryRecord }

(* --- Unpack sigma --- *)

(*
 * This searches for the equivalence between two types
 * { s : sigT B & projT1 s = i_b } and B i_b, for particular I_B : Type
 * and B : I_B -> Type.
 *
 * The search algorithm here is very simple: It just instantiates
 * generic equivalences already defined in Ornamental.Equivalences to
 * particular types. The reason this is so easy relative to the others
 * is that it needs not introspect on the structure of any inductive
 * types. Thus, it is possible to prove this generally within the theory,
 * then instantiate it.
 *)

(*
 * Constant for generic promote
 *)
let unpack_generic () =
  let n = qualid_of_string "Ornamental.Equivalences.unpack_generic" in
  mkConst (locate_constant n)

(*
 * Constant for generic forget
 *)
let unpack_generic_inv () =
  let n = qualid_of_string "Ornamental.Equivalences.unpack_generic_inv" in
  mkConst (locate_constant n)

(*
 * Search for promote or forget (instantiate the above generic constants)
 *)
let find_promote_or_forget_unpack env_args b_sig_eq is_fwd sigma =
  let directional x y = if is_fwd then x else y in
  let f = (directional unpack_generic unpack_generic_inv) () in
  let sigma, args = unpack_typ_args env_args b_sig_eq sigma in
  sigma, reconstruct_lambda env_args (mkAppl (f, args))

(*
 * Search for promote and forget
 *)
let find_promote_forget_unpack env_args promote_o forget_o b_sig_eq =
  find_promote_forget
    (find_promote_or_forget_unpack env_args b_sig_eq)
    promote_o
    forget_o

(*
 * Search for the equivalence
 *)
let search_unpack env_args promote_o forget_o b_sig_eq sigma =
  let sigma, (promote, forget) = find_promote_forget_unpack env_args promote_o forget_o b_sig_eq sigma in
  sigma, { promote; forget; kind = UnpackSigma }
           
(* --- Top-level search --- *)

(*
 * Search two inductive types for an ornament between them.
 * This is more general to handle eventual extension with other 
 * kinds of ornaments.
 *)
let search_orn_inductive env sigma indexer_id_opt swap_i_o typ_o typ_n promote_o forget_o =
  match map_tuple kind (typ_o, typ_n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if not (npm_o = npm_n) then
       (* new parameter *)
       user_err
         "search_orn_inductive"
         err_new_parameter
         [try_supported]
         [cool_feature; mistake]
     else
       let (bs_o, bs_n) = map_tuple (fun m -> m.mind_packets) (m_o, m_n) in
       let (b_o, b_n) = map_tuple (fun bs -> Array.get bs 0) (bs_o, bs_n) in
       let (cs_o, cs_n) = map_tuple (fun m -> m.mind_consnames) (b_o, b_n) in
       if not (Array.length cs_o = Array.length cs_n) then
         user_err
           "search_orn_inductive"
           err_new_constructor
           [try_supported]
           [cool_feature; mistake]
       else
         let npm = npm_o in
         let ncons = Array.length cs_o in
         let (sort_o, sort_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
         let (arity_o, arity_n) = map_tuple arity (sort_o, sort_n) in
         if Option.has_some indexer_id_opt && not (arity_o = arity_n) then
           (* new index *)
           let o = (typ_o, arity_o) in
           let n = (typ_n, arity_n) in
           let (a, b) = map_if reverse (arity_n <= arity_o) (o, n) in
           search_algebraic env sigma npm (Option.get indexer_id_opt) promote_o forget_o a b
         else
           (* change in constructor *)
           let group_cs_by_types cs grouped sigma =
             fold_left_state
               (fun grouped c sigma ->
                 let c_dest = destConstruct c in
                 let sigma, c_typ = infer_type env sigma c in
                 let c_typ = all_eq_substs env (typ_o, typ_n) c_typ in
                 try
                   let sigma, (repr, (matches, typ)) =
                     find_state
                       (fun (_, (_, typ)) sigma ->
                         convertible env sigma c_typ typ)
                       grouped
                       sigma
                   in
                   let grouped = List.remove_assoc repr grouped in
                   sigma, (repr, (c_dest :: matches, typ)) :: grouped
                 with _ ->
                   sigma, ((c_dest, ([c_dest], c_typ)) :: grouped))
               grouped
               cs
               sigma
           in
           let cs_o = List.init ncons (fun i -> mkConstruct ((i_o,ii_o),i+1)) in
           let cs_n = List.init ncons (fun i -> mkConstruct ((i_n,ii_n),i+1)) in
           let sigma, grouped_o = group_cs_by_types cs_o [] sigma in
           let sigma, grouped_n = group_cs_by_types cs_n grouped_o sigma in
           let is_swapped =
             List.for_all
               (fun (repr, (matches_o, _)) ->
                 let (matches_n, _) = List.assoc repr grouped_n in
                 List.length matches_n = 2 * List.length matches_o)
               grouped_o
           in
           if is_swapped then
             (* swapped constructors (including constructor renaming) *)
             search_swap_constructor env npm grouped_n swap_i_o promote_o forget_o typ_o typ_n sigma
           else
             user_err
               "search_orn_inductive"
               err_unsupported_change
               [try_supported]
               [cool_feature; problematic; mistake]           
  | _ ->
     raise NotInductive

(*
 * Search two types for an ornament between them, where one type
 * is an inductive type and the other is something else (like an application
 * of an inductive type). This is more general to handle eventual extensions
 * with other kinds of ornaments.
 *)
let search_orn_one_noninductive env sigma typ_o typ_n promote_o forget_o =
  let ind, non_ind = if isInd typ_o then (typ_o, typ_n) else (typ_n, typ_o) in
  let ((i, _), _) = destInd ind in
  let m = lookup_mind i env in
  check_inductive_supported m;
  let non_ind_inner = unwrap_definition env non_ind in
  let sigma, non_ind_inner = reduce_term env sigma non_ind_inner in
  let env, non_ind_inner = zoom_lambda_term env non_ind_inner in
  let err_unsupported () =
    user_err
      "search_orn_one_noninductive"
      err_unsupported_change
      [try_supported]
      [cool_feature; mistake]
  in
  match kind non_ind_inner with
  | App _ ->
     let f = unwrap_definition env (first_fun non_ind_inner) in
     if equal f prod then
       let npm = m.mind_nparams in
       let bs = m.mind_packets in
       let ncs = Array.length (Array.get bs 0).mind_consnames in
       if npm = nb_rel env && ncs = 1 then
         (* Curry a record into an application of prod *)
         search_curry_record env sigma promote_o forget_o ind non_ind
       else
         err_unsupported ()
     else if equal f sigT then
       let sigma, is_unpack =
         try
           let sigma, expected =
             let eq_sig = dest_sigT non_ind_inner in
             let b_sig = dest_sigT eq_sig.index_type in
             let sigma, b_sig_expected =
               let sigma, packer =
                 let env_i_b, packer_b = zoom_lambda_term env b_sig.packer in
                 let sigma, packer_b = reduce_nf env_i_b sigma packer_b in
                 let packer_ind = mkAppl (ind, unfold_args packer_b) in
                 sigma, reconstruct_lambda_n env_i_b packer_ind (nb_rel env)
               in sigma, pack_sigT { index_type = b_sig.index_type; packer }
             in
             let sigma, packer =
               let env_sig_b, b_eq = zoom_lambda_term env eq_sig.packer in
               let sigma, b_eq = reduce_nf env_sig_b sigma b_eq in
               let sigma, eq =
                 let trm1 =
                   let typ = dest_sigT (shift env_sig_b b_sig_expected) in
                   project_index typ (mkRel 1)
                 in
                 let trm2 = (dest_eq b_eq).trm2 in
                 sigma, apply_eq { at_type = b_sig.index_type; trm1; trm2 }
               in sigma, reconstruct_lambda_n env_sig_b eq (nb_rel env)
             in sigma, pack_sigT { index_type = b_sig_expected; packer }
           in convertible env sigma non_ind_inner expected
         with _ ->
           sigma, false
       in
       if is_unpack then
         (* Unpack { s : sigT B & projT1 s = i_b} to (B i_b) *)
         search_unpack env promote_o forget_o non_ind_inner sigma
       else
         err_unsupported ()
     else
       err_unsupported ()
  | _ ->
     err_unsupported ()

(*
 * Common code for search and inversion
 *)
let search_common env sigma indexer_id_opt swap_i_o typ_o typ_n promote_o forget_o =
  if isInd typ_o && isInd typ_n then
    (* Ornament between two inductive types *)
    search_orn_inductive env sigma indexer_id_opt swap_i_o typ_o typ_n promote_o forget_o
  else if isInd typ_o || isInd typ_n then
    (* Ornament between an inductive type and something else *)
    search_orn_one_noninductive env sigma typ_o typ_n promote_o forget_o
  else
    user_err
      "search_common"
      err_unsupported_change
      [try_supported]
      [cool_feature; mistake]
       
(*
 * Search for an ornament between two types.
 *
 * Eventually, we should move the optional arguments to some configuration.
 *)
let search_orn env sigma indexer_id_opt swap_i_o typ_o typ_n =
  search_common env sigma indexer_id_opt swap_i_o typ_o typ_n None None

(*
 * Try to invert a single component of an ornament between two types.
 *
 * Eventually, we should move the optoinal arguments to some configuration,
 * and we should move this to the inversion component at least partially.
 *)
let invert_orn env sigma indexer_id_opt swap_i_o typ_o typ_n promote_o forget_o =
  if Option.has_some promote_o && Option.has_some forget_o then
    failwith "Only one of promote and forget should be present in invert_orn"
  else if not (Option.has_some promote_o) && not (Option.has_some forget_o) then
    failwith "Exactly one of promote and forget should be present in invert_orn"
  else
    search_common env sigma indexer_id_opt swap_i_o typ_o typ_n promote_o forget_o
