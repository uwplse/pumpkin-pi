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
open Factoring
open Abstraction
open Hypotheses
open Names

(* --- Some utilities for meta-reduction --- *)

(*
 * Adjust an environment to remove the unpacked references
 *)
let pack_env assum_ind env =
  pop_rel_context (assum_ind + 1) env

(*
 * Reconstruct a lambda in an unpacked environment
 *)
let reconstruct_packed assum_ind env trm =
  reconstruct_lambda_n_skip env trm (offset env 2) (assum_ind - 1)

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
  zoom_apply_lambda
    (fun env _ -> ornament_args env evd from_ind l trm)
    env
    (sub_in_hypos l env from_ind to_ind hypos)

(* Apply the promotion/forgetful function to the conclusion, if applicable *)
let ornament_concls concl_typ env evd (l : lifting) (from_ind, _) trm =
  map_if
    (zoom_apply_lambda
       (fun _ trm_zoom ->
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
         in mkAppl (lift_to l, snoc trm_zoom args))
       env)
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
  let typ = reduce_type env evd trm in
  let concl_typ = in_body zoom_product_type reduce_nf env typ in
  app_orn (ornament_concls concl_typ) (app_orn ornament_hypos trm)
          
(* --- Meta-reduction --- *)

(*
 * TODO from here on out needs clean-up
 * TODO separate out into steps instead of doing everything at once
 * TODO maybe even separate application this way too
 *)

(*
 * Pack arguments inside of a sigT type
 *)
let pack_inner env evd l unpacked =
  let index_i = Option.get l.orn.index_i in
  let typ = reduce_type env evd unpacked in
  let index = get_arg index_i typ in
  let typ_args = unfold_args typ in
  let index_type = infer_type env evd index in
  let packer = abstract_arg env evd index_i typ in
  let ex = pack_existT {index_type; packer; index; unpacked} in
  mkAppl (lift_back l, snoc ex (remove_index index_i typ_args))

(*
 * Get the arguments for composing two applications of an induction
 * principle that are structurally the same when one is an ornament.
 *)
let compose_p_args evd npms post_assums inner comp =
  let l = comp.l in
  let (env, p) = comp.f in
  let index_i = Option.get l.orn.index_i in
  in_lambda_body
    (fun env_b p_b ->
      let orn_app =
        if not inner then
          let off = offset2 env_b env in
          let nargs = arity (unwrap_definition env (lift_back l)) in
          let shift_pms = shift_local off (off + List.length post_assums) in
          map_backward
            (fun t ->
              let index_type = get_arg index_i t in
              let index = mkRel 1 in
              let abs_i = reindex_body (reindex_app (reindex index_i index)) in
              let packer = abs_i (mkLambda (Anonymous, index_type, shift t)) in
              project_value { index_type; packer } t)
            l
            (shift_pms (mkAppl (lift_back l, mk_n_rels nargs)))
        else
          pack_inner env_b evd l (mkRel 1)
      in
      let reindex_if_sig = map_if (remove_index index_i) (applies sigT p_b) in
      let inner_args = reindex_if_sig (unfold_args (zoom_if_sig_app p_b)) in
      snoc orn_app (snd (take_split npms inner_args)))
    env
    p

(*
 * Get the function for composing two applications of an induction
 * principle that are structurally the same when one is an ornament.
 *)
let compose_p_fun evd (comp : composition) =
  let l = comp.l in
  let index_i = Option.get l.orn.index_i in
  let (env_g, p_g) = comp.g in
  let (env_f, p_f) = comp.f in
  let env_p_f = zoom_env zoom_lambda_term env_f p_f in
  let p_g_in_p_f = shift_to_env (env_g, env_p_f) p_g in
  map_forward
    (map_if
       (zoom_apply_lambda_n
          (nb_rel env_g)
          (fun _ trm ->
            (* pack the conclusion *)
            let index_type = infer_type env_p_f evd (mkRel 2) in
            let abs_i = reindex_body (reindex_app (reindex index_i (mkRel 1))) in
            let packer = abs_i (mkLambda (Anonymous, index_type, shift trm)) in
            pack_sigT { index_type ; packer })
          env_g)
       (comp.is_g && not l.is_indexer))
    l
    p_g_in_p_f
    
(*
 * Compose two properties for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * This works by finding (p, p_args) and returning their application.
 * This will be an adjusted version of an existing p
 * with new arguments that are promoted/forgotten/indexed appropriately.
 *)
let compose_p evd npms post_assums inner (comp : composition) =
  let (env_f, p_f) = comp.f in
  zoom_apply_lambda_n
    (nb_rel env_f)
    (fun env _ ->
      let p_args = compose_p_args evd npms post_assums inner comp in
      let p = compose_p_fun evd comp in
      reduce_term env (mkAppl (p, p_args)))
    env_f
    p_f

(*
 * Compose the IH for a constructor.
 * This simply uses the new property p.
 *)
let compose_ih evd npms ip p comp =
  let (env_f, c_f) = comp.f in
  let ip_g_typ = reduce_type env_f evd ip in
  let from_typ = first_fun (fst (ind_of_promotion_type ip_g_typ)) in
  map_term_env_if
    (fun _ _ trm -> is_or_applies from_typ trm)
    (fun en p trm ->
      let (_, _, orn_final_typ) = CRD.to_tuple @@ lookup_rel 1 en in
      let typ_args = unfold_args (shift orn_final_typ) in
      let non_pms = snd (take_split npms typ_args) in
      reduce_term en (mkAppl (p, snoc (mkRel 1) non_pms)))
    shift
    env_f
    p
    c_f

(*
 * Meta-reduction of an applied ornament in the forward direction in the
 * non-indexer case, when the ornament application produces an existT term.
 *)
let reduce_existT_app l evd orn env arg trm =
  let orn_app = mkAppl (orn, snoc arg (on_type unfold_args env evd arg)) in
  let unfolded = chain_reduce reduce_term delta env trm in
  let orn_app_red = reduce_nf env orn_app in
  let orn_app_ind = reduce_to_ind env orn_app in
  let abstract = abstract_arg env evd (Option.get l.orn.index_i) in
  let unfolded_ex = dest_existT unfolded in
  let orn_app_ind_ex = dest_existT orn_app_ind in
  let orn_app_red_ex = dest_existT orn_app_red in
  let packer = on_type abstract env evd orn_app_ind_ex.unpacked in
  let index_type = unfolded_ex.index_type in
  let arg_sigT = { index_type ; packer } in
  let arg_indexer = project_index arg_sigT arg in
  let arg_value = project_value arg_sigT arg in
  let fold_index = all_eq_substs (orn_app_red_ex.index, arg_indexer) in
  let fold_value = all_eq_substs (orn_app_red_ex.unpacked, arg_value) in
  let unfolded_index_red = reduce_nf env unfolded_ex.index in
  let unfolded_unpacked_red = reduce_nf env unfolded_ex.unpacked in
  let index = fold_index unfolded_index_red in
  let unpacked = fold_index (fold_value unfolded_unpacked_red) in
  if eq_constr unfolded_unpacked_red unpacked then
    (* nothing to rewrite; ensure termination *)
    trm
  else
    (* pack the rewritten term *)
    pack_existT { unfolded_ex with index; unpacked }

(*
 * Meta-reduction of an applied ornament in the indexer case.
 *)
let reduce_indexer_app l evd orn env arg trm =
  let orn_app = mkAppl (orn, snoc arg (on_type unfold_args env evd arg)) in
  let unfolded = chain_reduce reduce_term delta env trm in
  let orn_app_red = reduce_nf env orn_app in
  let app_red = reduce_nf env unfolded in
  let app = all_eq_substs (orn_app_red, orn_app) app_red in
  if eq_constr app_red app then
    (* nothing to rewrite; ensure termination *)
    trm
  else
    (* return the rewritten term *)
    app

(*
 * Meta-reduction of an applied ornament in the backwards non-indexer case,
 * when the application of the induction principle eliminates a sigT.
 *)
let reduce_sigT_elim_app l evd orn env arg trm =
  let deindex = remove_index (Option.get l.orn.index_i) in
  let arg_typ = unshift (on_type zoom_sig_app env evd arg) in
  let orn_app = mkAppl (orn, snoc arg (deindex (unfold_args arg_typ))) in
  let unfolded = chain_reduce reduce_term delta env trm in
  let orn_app_ind = reduce_to_ind env orn_app in
  let app_red = reduce_nf env unfolded in
  let elim = dest_sigT_elim orn_app_ind in
  let arg_indexer = project_index elim.to_elim arg in
  let arg_value = project_value elim.to_elim arg in
  let unpacked_app = mkAppl (elim.unpacked, [arg_indexer; arg_value]) in
  let unpacked_app_red = reduce_nf env unpacked_app in
  let app = all_eq_substs (unpacked_app_red, arg) app_red in
  if eq_constr app_red app then
    (* nothing to rewrite; ensure termination *)
    trm
  else
    (* return the rewritten term *)
    app

(* 
 * Get the meta-reduction function for a lifted term.
 *)
let meta_reduce l =
  if l.is_fwd && not l.is_indexer then
    (* rewrite in the unpacked body of an existT *)
    reduce_existT_app l
  else if l.is_indexer then
    (* rewrite in the application of an indexer *)
    reduce_indexer_app l
  else
    (* rewrite inside of an eliminator of a sigT *)
    reduce_sigT_elim_app l

(*
 * Meta-reduction of an applied ornament to simplify and then rewrite
 * in terms of the ornament and indexer applied to the specific argument.
 *)
let reduce_ornament_f_arg l env evd orn trm arg =
  map_term_env_if
    (fun _ _ trm -> applies orn trm)
    (meta_reduce l evd orn)
    shift
    env
    arg
    trm
  
            
(*
 * Meta-reduction of an applied ornament to simplify and then rewrite
 * in terms of the ornament and indexer applied to arguments from the list.
 *)
let reduce_ornament_f l env evd orn trm args =
  List.fold_left (reduce_ornament_f_arg l env evd orn) trm args

(*
 * Get the (index arg index, IH) pairs for a constructor
 * 
 * Need to test: What happens if the index isn't the first argument in
 * the new constructor? Unsure if the recursion condition is correct here.
 *)
let indexes to_typ index_i num_args trm =
  let rec constr_indexes t i =
    match kind_of_term t with
    | Prod (n, t, b) ->
       let num_args_left = num_args - (i + 1) in
       let index_ih_opt = index_ih index_i to_typ (mkRel 1) b num_args_left in
       map_if
         (fun tl -> (i, Option.get index_ih_opt) :: tl)
         (Option.has_some index_ih_opt)
         (constr_indexes b (i + 1))
    | _ ->
       []
  in constr_indexes (lambda_to_prod trm) 0

(* 
 * Reduces the body of a constructor of an indexer
 *)
let reduce_indexer_constr_body l env evd trm =
  let from = last_arg trm in
  if is_or_applies (lift_back l) from then
    (* eliminate the promotion/forgetful function *)
    let arg = last_arg from in
    project_index (on_type dest_sigT env evd arg) arg
  else
    (* leave as-is *)
    trm

(*
 * Reduces the body of a constructor of a promoted function
 *)
let reduce_promoted_constr_body l env evd trm =
  let from = last_arg trm in
  if is_or_applies (lift_back l) from then
    (* eliminate the promotion function *)
    last_arg from
  else
    (* leave as-is *)
    trm

(* 
 * Reduces the body of a constructor of a forgetful function
 *)
let reduce_forgotten_constr_body l env evd trm =
  let from = last_arg trm in
  if is_or_applies existT from then
    let ex = dest_existT from in
    if is_or_applies projT2 ex.unpacked then
      (* eliminate existT of the projection of a promotion *)
      last_arg (last_arg ex.unpacked)
    else if is_or_applies (lift_to l) ex.unpacked then
      (* eliminate existT of the forgetful function *)
      last_arg ex.unpacked
    else
      (* leave as-is *)
      trm
  else if is_or_applies (lift_back l) from then
    (* eliminate the promotion function *)
    last_arg from
  else
    (* leave as-is *)
    trm

(*
 * Get the pre-meta-reduction function for a constructor body.
 *)
let pre_reduce l =
  if l.is_indexer then
    reduce_indexer_constr_body l
  else if l.is_fwd then
    reduce_promoted_constr_body l
  else
    reduce_forgotten_constr_body l

(*
 * Filter the arguments to only the ones that have the type we are
 * promoting/forgetting from.
 *
 * For simplicity, we assume that the function doesn't have any other
 * applications of that type that don't use the new index, otherwise
 * we would need to track the type arguments everywhere, which is tedious
 *)
let filter_orn l env evd (from_typ, to_typ) args =
  let is_orn env trm =
    if l.is_fwd then
      is_or_applies from_typ trm
    else
      if is_or_applies sigT trm then
        let trm_app = dest_sigT trm in
        eq_constr to_typ (first_fun (dummy_index env trm_app.packer))
      else
        false
  in List.filter (on_type (is_orn env) env evd) args

(*
 * When we ornament in both directions and we're currently reducing g o f
 * where g is the promotion/forgetful function and f is already reduced,
 * we need to unpack applications of the function to the inductive
 * hypotheses. This function does that.
 *)
let unpack_ihs f ihs trm =
  map_unit_if
    (fun t ->
      isApp t && applies f t && List.exists (eq_constr (last_arg t)) ihs)
    last_arg
    trm
                 
(*
 * This reduces the body of an ornamented constructor to a reasonable term,
 * when we ornament in both directions
 *)
let reduce_constr_body env evd l (from_typ, to_typ) index_args body =
  let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
  let all_args = mk_n_rels (nb_rel env) in
  let orn_args = filter_orn l env evd (from_typ, to_typ) all_args in
  let ihs = List.map (fun (_, (ih, _)) -> ih) index_args in
  let red_body =
    map_if
      (reduce_nf env)
      (List.length index_args = 0 && not l.is_indexer)
      (map_unit_if
         (applies f)
         (fun trm ->
           reduce_ornament_f l env evd f (pre_reduce l env evd trm) orn_args)
         body)
  in unpack_ihs f ihs red_body

(* 
 * When forgetting, we do not have indices to pass to the constructor,
 * so for each of those arguments, we must project the index from the
 * result of promoting the corresponding IH. This function does that projection.
 *)
let project_index_from_ih l env evd ih =
  let orn = mkAppl (lift_back l, snoc ih (on_type unfold_args env evd ih)) in
  project_index (on_type dest_sigT env evd orn) orn
                
(* 
 * When forgetting, for every IH, to pass that IH to the constructor, 
 * we must project out the value from the result of promoting the IH. 
 * This function does that promotion.
 *)
let project_value_from_ih l env evd ih =
  let orn = mkAppl (lift_back l, snoc ih (on_type unfold_args env evd ih)) in
  project_value (on_type dest_sigT env evd orn) orn

(*
 * This does the index and value projections of the IHs when forgetting.
 *)
let project_ihs l env evd (from_typ, to_typ) c_g =
  let index_i = Option.get l.orn.index_i in
  let index_args = indexes to_typ index_i (arity c_g) c_g in
  List.mapi
    (fun i arg ->
      if List.mem_assoc i index_args then
        let ih = fst (List.assoc i index_args) in
        project_index_from_ih l env evd ih
      else if on_type (is_or_applies from_typ) env evd arg then
        project_value_from_ih l env evd arg
      else
        arg)
    (get_all_hypos c_g)

(*
 * In the promotion direction, we need to do the opposite, and pack each IH.
 *)
let pack_ihs l env evd (from_typ, to_typ) c_g =
  List.map
    (fun arg ->
      if on_type (is_or_applies to_typ) env evd arg then
        pack_inner env evd l arg
      else
        arg)
    (get_all_hypos c_g)

(*
 * Given a term with the type we are promoting to/forgetting from, 
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
let non_index_typ_args l env evd trm =
  if l.is_fwd then
    on_type unfold_args env evd trm
  else
    let app = on_type dest_sigT env evd trm in
    let deindex = remove_index (Option.get l.orn.index_i) in
    deindex (unfold_args (dummy_index env app.packer))
  
(*
 * Compose two constructors for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * For now, this does not handle nested induction.
 *)
let compose_c evd npms_g ip_g p post_assums (comp : composition) =
  let l = comp.l in
  let (env_g, c_g) = comp.g in
  let (env_f, c_f_old) = comp.f in
  let (orn_f, orn_g) = (l.orn.forget, l.orn.promote) in
  let promotion_type env trm = fst (on_type ind_of_promotion_type env evd trm) in
  let to_typ = zoom_sig (promotion_type env_f orn_f) in
  let from_typ = first_fun (promotion_type env_g orn_g) in
  let c_f = compose_ih evd npms_g ip_g p comp in
  zoom_apply_lambda_n
    (nb_rel env_f)
    (fun env trm ->
      if not comp.is_g then
        (* it's still unclear to me why local_max is what it is *)
        let local_max = directional l 0 (List.length post_assums) in
        let f = shift_local local_max (offset2 env env_g) c_g in
        let lift_args = map_directional pack_ihs project_ihs l in
        let args = lift_args l env evd (from_typ, to_typ) c_g in
        reduce_term env (mkAppl (f, args))
      else
        let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
        let index_i = Option.get l.orn.index_i in
        let c_indexed = directional l c_f c_g in
        let index_args = indexes to_typ index_i (arity c_g) c_indexed in
        in_lambda_body
          (fun env_old _ ->
            let args = snoc trm (non_index_typ_args l env_old evd trm) in
            let app = mkAppl (f, args) in
            reduce_constr_body env_old evd l (from_typ, to_typ) index_args app)
          env_f
          c_f_old)
    env_f
    c_f

(* Map compose_c *)
let compose_cs evd npms ip p post_assums comp gs fs =
  let comp_cs =
    List.map2
      (fun c_g c_f -> { comp with g = (fst gs, c_g); f = (fst fs, c_f)})
      (snd gs)
      (snd fs)
  in List.map (compose_c evd npms ip p post_assums) comp_cs

(*
 * Build the lifted indexer, if applicable
 *)
let build_lifted_indexer evd idx_n assum_ind comp =
  let l = comp.l in
  let (env, f) = comp.f in
  if l.is_fwd && comp.is_g && not l.is_indexer then
    let indexer = Option.get l.orn.indexer in
    let (env_b, b) = zoom_lambda_term env f in
    let index_args = snoc b (on_type unfold_args env_b evd b) in
    let indexer_app = mkAppl (indexer, index_args) in
    let unpacked = reconstruct_packed assum_ind env_b indexer_app in
    let env_packed = pack_env assum_ind env_b in
    let index_type = infer_type env_b evd (mkRel (assum_ind + 1)) in
    let packer = infer_type env_packed evd (mkRel assum_ind) in
    let packed_type = mkLambda (Anonymous, packer, shift index_type) in
    let arg = mkRel assum_ind in
    let to_elim = { index_type; packer } in
    let indexer_body = elim_sigT { to_elim; packed_type; unpacked; arg } in
    let indexer = reconstruct_lambda env_packed indexer_body in
    let l = { l with lifted_indexer = Some (make_constant idx_n) } in
    ({ comp with l }, Some indexer)
  else
    (comp, None)
      
(*
 * Compose two applications of an induction principle that are
 * structurally the same when one is an ornament.
 *)
let rec compose_inductive evd idx_n post_assums assum_ind inner comp =
  let (env_g, g) = comp.g in
  let (env_f, f) = comp.f in
  let f_app = deconstruct_eliminator env_f evd f in
  let g_app = deconstruct_eliminator env_g evd g in
  let npms = List.length g_app.pms in
  let (comp, indexer) = build_lifted_indexer evd idx_n assum_ind comp in
  let c_p = { comp with g = (env_g, g_app.p); f = (env_f, f_app.p) } in
  let p = compose_p evd npms post_assums inner c_p in
  let (cs, indexer) =
    if applies sigT_rect f then
      (* recurse inside the sigT_rect *)
      let compose_rec = compose_inductive evd idx_n post_assums assum_ind true in
      let c = List.hd f_app.cs in
      let (env_c, c_body) = zoom_lambda_term env_f c in
      let c_inner = { comp with f = (env_c, c_body)} in
      let (c_comp, indexer) = compose_rec c_inner in
      ([reconstruct_lambda_n env_c c_comp (nb_rel env_f)], indexer)
    else
      (* compose the constructors *)
      let gs =
        map_if
          (fun (env, cs) ->
            in_lambda_body
              (fun env trm -> (env, (deconstruct_eliminator env evd trm).cs))
              env
              (List.hd cs))
          (applies sigT_rect g)
          (env_g, g_app.cs)
      in
      let fs = (env_f, f_app.cs) in
      (compose_cs evd npms g_app.elim p post_assums comp gs fs, indexer)
  in (apply_eliminator {f_app with p; cs}, indexer)

(*
 * Factor the inside of an application of a sigT_elim to an existT,
 * or the opposite way around, or the application of a sigT_elim to
 * an indexer. In other words, meta-reduce complex sigT_elim terms when
 * the result is obvious.
 *)
let factor_elim_existT evd assum_ind f g g_no_red =
  let (env_f, f) = f in
  let (env_g, g) = g in
  if applies sigT_rect g && applies existT f then
    (* sigT .... o existT .... *)
    let g_inner = (dest_sigT_elim g).unpacked in
    let f_app = dest_existT f in
    let inner = mkAppl (g_inner, [f_app.index; f_app.unpacked]) in
    factor_term_dep (mkRel assum_ind) env_f evd inner
  else if applies sigT_rect f && applies existT g then
    (* existT ... o sigT .... *)
    let c_g = reconstruct_lambda env_g (dest_existT g).unpacked in
    let typ_args = List.rev (List.tl (List.rev (unfold_args g_no_red))) in
    let c_f = reduce_term env_g (mkAppl (c_g, typ_args)) in
    in_lambda_body
      (fun env trm ->
        let inner = mkAppl (shift_by 2 c_f, [trm]) in
        factor_term_dep (mkRel assum_ind) env evd inner)
      env_f
      (dest_sigT_elim f).unpacked
  else
    (* existT ... o indexer ... *)
    in_lambda_body
      (fun env trm -> factor_term_dep (mkRel assum_ind) env evd trm)
      env_g
      (dest_sigT_elim g).unpacked

(*
 * When composing factors, determine if we have an application of
 * the forgetful function. Return (f_forgets, g_forgets).
 *)
let forgets l g f =
  let (env_g, g) = g in
  let (env_f, f) = f in
  let forget = l.orn.forget in
  let f_forgets = is_or_applies forget f in
  let g_forgets = is_or_applies forget g in
  (f_forgets, isApp f && g_forgets)

(*
 * When composing factors, determine if we have an application of
 * the promotion function. Return (f_promotes, g_promotes).
 *)
let promotes evd l assum_ind g f =
  let (env_g, g) = g in
  let (env_f, f) = f in
  let promote = l.orn.promote in
  let indexer = Option.get l.orn.indexer in
  let index_i = Option.get l.orn.index_i in
  let promote_unpacked =
    zoom_apply_lambda_n
      (nb_rel env_f)
      (fun _ trm -> (dest_existT trm).unpacked)
      env_f
      (delta env_f promote)
  in
  let typ_args = on_type unfold_args env_f evd f in
  let deindex = List.exists (applies indexer) typ_args in
  let assum = mkRel assum_ind in
  let args = snoc assum (map_if (remove_index index_i) deindex typ_args) in
  let promote_param = reduce_term env_f (mkAppl (promote_unpacked, args)) in
  let g_promotes = is_or_applies promote g || is_or_applies promote_param g in
  let f_promotes = is_or_applies promote f || is_or_applies promote_param f in
  (f_promotes, isApp f && g_promotes)

(*
 * When composing factors, determine if we have an application of
 * the indexer. Return (f_indexes, g_indexes, is_inner).
 *)
let is_indexer l g f =
  let (env_g, g) = g in
  let (env_f, f) = f in
  let indexer = Option.get l.orn.indexer in
  let is_indexer_inner t =
    if is_or_applies sigT_rect t then
      let unpacked = (dest_sigT_elim t).unpacked in
      in_lambda_body (fun _ -> is_or_applies indexer) env_f unpacked
    else
      false
  in
  let f_indexes_inner = is_indexer_inner f in
  let g_indexes_inner = is_indexer_inner g in
  let f_is_indexer = is_or_applies indexer f || f_indexes_inner in
  let g_is_indexer = is_or_applies indexer g || g_indexes_inner in
  (f_is_indexer, g_is_indexer, f_indexes_inner || g_indexes_inner)
    
(*
 * Compose factors of an ornamented, but not yet reduced function
 *)
let rec compose_orn_factors evd (l : lifting) assum_ind idx_n fs =
  let compose_rec l fs = compose_orn_factors evd l assum_ind idx_n fs in
  match fs with
  | Factor ((en, t), children) ->
     if List.length children > 0 then
       let post_assums = mk_n_rels (assum_ind - 1) in
       let ((t_app, indexer), env, composed) = compose_rec l (last children) in
       let g = zoom_lambda_term en t in
       let f = (env, t_app) in
       let (f_promotes, g_promotes) = promotes evd l assum_ind g f in
       let (f_forgets, g_forgets) = forgets l g f in
       let (f_is_indexer, g_is_indexer, is_indexer_inner) = is_indexer l g f in
       let is_promote = f_promotes || g_promotes in
       let is_forget = f_forgets || g_forgets in
       let is_index = f_is_indexer || g_is_indexer in
       if is_promote || is_forget || is_index then
         let is_g = g_promotes || g_forgets || g_is_indexer in
         let l = { l with is_indexer = is_index } in
         let g_ind = (fst g, reduce_to_ind (fst g) (snd g)) in
         let f_ind = (fst f, reduce_to_ind (fst f) (snd f)) in
         let comp = { l ; g = g_ind ; f = f_ind ; is_g } in    
         if applies sigT_rect (snd g_ind) && applies existT (snd f_ind) then
           compose_rec l (factor_elim_existT evd assum_ind f_ind g_ind (snd g))
         else if applies sigT_rect (snd f_ind) && applies existT (snd g_ind) then
           let inner_fs = factor_elim_existT evd assum_ind f_ind g_ind (snd g) in
           let ((t_app, indexer), env, composed) = compose_rec l inner_fs in
           let f_app = dest_sigT_elim (snd f_ind) in
           let unpacked = reconstruct_packed assum_ind env t_app in
           let packed_type =
             zoom_apply_lambda_empty
               (fun _ -> on_type (unshift_by assum_ind) env evd t_app)
               f_app.packed_type
           in
           let t_app_packed = elim_sigT { f_app with packed_type; unpacked } in
           ((t_app_packed, indexer), pack_env assum_ind env, composed)
         else if applies sigT_rect (snd g_ind) && is_indexer_inner then
           let inner_fs = factor_elim_existT evd assum_ind f_ind g_ind (snd g) in
           let ((t_app, indexer), env, composed) = compose_rec l inner_fs in
           let g_app = dest_sigT_elim (snd g_ind) in
           let unpacked = reconstruct_packed 1 env t_app in
           let t_app_packed = elim_sigT { g_app with unpacked } in
           ((t_app_packed, indexer), pack_env 1 env, composed)
         else
           let compose = compose_inductive evd idx_n post_assums assum_ind in
           (compose false comp, env, true)
       else
         let t = shift_by assum_ind t in
         let t_args =
           if not composed then
             t_app :: post_assums
           else
             [t_app]
         in ((reduce_term env (mkAppl (t, t_args)), indexer), env, composed)
     else
       ((t, None), en, false)
  | Unit ->
     failwith "unexpected"
                  
(*
 * This takes a term (f o orn_inv) and reduces it to f' where orn_inv is
 * moved inside of the function.
 *
 * It assumes the term is in an easy-to-factor form (the form apply produces).
 * It also does not yet handle terms like append where the final result
 * is then ornamented. It also does not yet handle proofs like app_nil_r
 * where the type of the final result is no longer definable as-is.
 * It also does not yet handle any situations where f is not just an application
 * of the induction principle for the unornamented type. Basically,
 * this is a very preliminary attempt at solving this problem, which I
 * will build on.
 *)
let internalize env evd (indexer_name : Id.t) (l : lifting) (trm : types) =
  let (assum_ind, factors) = factor_ornamented l.orn env evd trm in
  let ((internalized, indexer), env, _) = compose_orn_factors evd l assum_ind indexer_name factors in
  (reconstruct_lambda env internalized, indexer)
