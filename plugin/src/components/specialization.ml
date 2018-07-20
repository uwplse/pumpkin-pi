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
  on_type (non_index_args l env) env evd trm

(* --- Application of ornaments before meta-reduction --- *)

(*
 * Substitute the ornamented type in the hypotheses.
 *)
let sub_in_hypos l env evd (from_ind, to_ind) hypos =
  let rec sub env trm =
    match kind_of_term trm with
    | Prod (n, t, b) ->
       let t' =
         map_unit_env_if
           (fun env trm ->
             is_or_applies from_ind (zoom_if_sig (reduce_nf env trm)))
           (fun env trm ->
             reduce_term env (mkAppl (to_ind, non_index_args l env trm)))
           env
           (map_unit_env_if
              (fun env trm ->
                try
                  is_or_applies from_ind (on_type zoom_if_sig env evd trm)
                with _ ->
                  false)
              (fun env trm ->
                let t_args = non_index_typ_args l env evd trm in
                mkAppl (lift_back l, snoc trm t_args))
              env
              t)
       in mkProd (n, t', sub (push_local (n, t) env) b)
    | _ ->
       trm
  in sub env hypos

(* Apply the promotion/forgetful function to the arguments *)
let ornament_args env evd from_ind l trm =
  let rec ornament_arg env i typ =
    match kind_of_term typ with
    | Prod (n, t, b) ->
       let ornament_b = ornament_arg (push_local (n, t) env) (unshift_i i) b in
       if is_or_applies from_ind (zoom_if_sig (reduce_nf env t)) then
         let t_args = non_index_args l env (shift_by i t) in
         mkAppl (lift_back l, snoc (mkRel i) t_args) :: ornament_b
       else
         mkRel i :: ornament_b
    | _ ->
       []
  in mkAppl (trm, on_type (fun t -> ornament_arg env (arity t) t) env evd trm)

(* Apply the promotion/forgetful function to the hypotheses *)
let ornament_hypos env evd (l : lifting) (from_ind, to_ind) trm =
  let hypos = reduce_type env evd trm in
  let subbed = sub_in_hypos l env evd (from_ind, to_ind) hypos in
  zoom_apply_lambda
    (fun env _ -> ornament_args env evd from_ind l trm)
    env
    (prod_to_lambda subbed)

(* Apply the promotion/forgetful function to the conclusion, if applicable *)
let ornament_concls concl_typ env evd (l : lifting) (from_ind, _) trm =
  let index_i = Option.get l.orn.index_i in
  map_if
    (zoom_apply_lambda
       (fun env_zoom trm_zoom ->
         mkAppl (lift_to l, snoc trm_zoom (non_index_args l env concl_typ)))
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
  let concl_typ = in_body zoom_product_type reduce_term env typ in
  app_orn (ornament_concls concl_typ) (app_orn ornament_hypos trm)

(* --- Meta-reduction --- *)

(*
 * Forget/promote assumption for induction
 *)
let forget_assum env evd l assum =
  let index_i = Option.get l.orn.index_i in
  let typ = reduce_type env evd assum in
  let typ_args = non_index_args l env typ in
  mkAppl (lift_back l, snoc assum typ_args)

(*
 * Forget/promote assumption for induction everywhere in a term
 *)
let forget_assums env evd l assum trm =
  map_term_env_if
    (fun _ -> eq_constr)
    (fun e _ -> forget_assum e evd l)
    shift
    env
    assum
    trm

(*
 * Pack inside of a sigT type
 *)
let pack env evd l unpacked =
  let index_i = Option.get l.orn.index_i in
  let typ = reduce_type env evd unpacked in
  let index = get_arg index_i typ in
  let typ_args = unfold_args typ in
  let index_type = infer_type env evd index in
  let packer = abstract_arg env evd index_i typ in
  pack_existT {index_type; packer; index; unpacked}
    
(*
 * Pack arguments inside of a sigT type and lift
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
 *
 * LATER: We will need to restest this when our unornamented type itself
 * has an index, to check indexing logic for assum_args.
 *)
let compose_p_args evd npms assum_ind comp =
  let l = comp.l in
  let (env, p) = comp.f in
  let index_i = Option.get l.orn.index_i in
  let deindex = remove_index index_i in
  in_lambda_body
    (fun env_b p_b ->
      let off = offset2 env_b env in
      let assum = shift_by off (mkRel assum_ind) in
      let assums = non_index_typ_args l env_b evd assum in
      let post_assums = mk_n_rels off in
      let orn_args = List.append assums post_assums in
      let reindex_if_sig = map_if (fun l -> if List.length l > 0 then deindex l else l) (applies sigT p_b) in
      let p_b_sig = zoom_if_sig_app p_b in
      let p_b_args = unfold_args p_b_sig in
      let inner_args = reindex_if_sig p_b_args in
      let non_pms = snd (take_split npms inner_args) in
      if l.is_fwd then
        let orn_app = pack_inner env_b evd l (last orn_args) in
        snoc orn_app non_pms
      else
        let orn_app = mkAppl (lift_back l, orn_args) in
        let orn_app_typ = on_type dest_sigT env_b evd orn_app in
        let value = project_value orn_app_typ orn_app in
        if comp.is_g then
          let index = project_index orn_app_typ orn_app in
          snoc value (insert_index index_i index non_pms)
        else
          snoc value non_pms)
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
          (fun env trm ->
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
let compose_p evd npms assum_ind (comp : composition) =
  let (env_f, p_f) = comp.f in
  zoom_apply_lambda_n
    (nb_rel env_f)
    (fun env _ ->
      let p_args = compose_p_args evd npms assum_ind comp in
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
  let index_i = Option.get comp.l.orn.index_i in
  let rec compose en p c =
    match kind_of_term c with
    | Lambda (n, t, b) | Prod (n, t, b) ->
       let t' =
         map_term_env_if
           (fun en _ trm ->
             if comp.l.is_fwd || not comp.is_g then
               is_or_applies from_typ trm
             else
               if is_or_applies sigT trm then
                 let f = first_fun (dummy_index en ((dest_sigT trm).packer)) in
                 is_or_applies from_typ f
               else
                 false)
           (fun en p trm ->
             let (_, _, orn_final_typ) = CRD.to_tuple @@ lookup_rel 1 en in
             let typ_args = unfold_args (shift orn_final_typ) in
             let non_pms = snd (take_split npms typ_args) in
             reduce_term en (mkAppl (p, snoc (mkRel 1) non_pms)))
           shift
           en
           p
           t
       in mkLambda (n, t', compose (push_local (n, t) en) (shift p) b)
    | _ ->
       c
  in compose env_f p c_f


(*
 * Get all recursive constants
 * TODO instead of doing this and refolding, in some cases
 * we should be able to just avoid unfolding these, at least for
 * higher lifted functions
 *)
let rec all_recursive_constants env trm =
  let consts = all_const_subterms (fun _ _ -> true) (fun u -> u) () trm in
  let non_axioms =
    List.map
      Option.get
      (List.filter
         (Option.has_some)
         (List.map
            (fun c ->
              try
                let def = unwrap_definition env c in
                if not (eq_constr def c || isInd def) then
                  Some (c, def)
                else
                  None
              with _ ->
                None)
            consts))
  in
  let non_axiom_consts = List.map fst non_axioms in
  let defs = List.map snd non_axioms in
  let flat_map f l = List.flatten (List.map f l) in
  unique
    eq_constr
    (List.append non_axiom_consts (flat_map (all_recursive_constants env) defs))

(*
 * Fold back constants after applying a function
 * Necessary for current higher lifting implementation
 * Workaround may not always work yet
 *)
let fold_back_constants env f trm =
  List.fold_left
    (fun red lifted ->
      all_conv_substs env (lifted, lifted) red)
    (f trm)
    (all_recursive_constants env trm)

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
  let index = fold_index unfolded_index_red in
  let unfolded_unpacked_red = reduce_nf env unfolded_ex.unpacked in
  let unpacked = fold_index (fold_value unfolded_unpacked_red) in
  if eq_constr index unfolded_index_red && eq_constr unpacked unfolded_unpacked_red then
    (* don't reduce *)
    trm
  else
    pack_existT { unfolded_ex with index; unpacked }

(*
 * Meta-reduction of an applied ornament in the indexer case.
 * TODO here and elsewhere (or in step after):
 * rewrite back other expanded functions (see append with flector;
 * may matter for higher lifting)
 *)
let reduce_indexer_app l evd orn env arg trm =
  let orn_app = mkAppl (orn, snoc arg (on_type unfold_args env evd arg)) in
  let unfolded = chain_reduce reduce_term delta env trm in
  let orn_app_red = reduce_nf env orn_app in
  let app_red = reduce_nf env unfolded in
  let app = all_eq_substs (orn_app_red, orn_app) app_red in
  if eq_constr app_red app then
    (* nothing to rewrite *)
    trm
  else
    (* return the rewritten term *)
    app

(*
 * Meta-reduction of an applied ornament in the backwards non-indexer case,
 * when the application of the induction principle eliminates a sigT.
 *)
let reduce_sigT_elim_app l evd orn env arg trm =
  let index_i = Option.get l.orn.index_i in
  let deindex = remove_index index_i in
  let arg_typ = dummy_index env ((on_type dest_sigT env evd arg).packer) in
  let orn_app = mkAppl (orn, snoc arg (deindex (unfold_args arg_typ))) in
  let app_red =
    reduce_nf
      env
      (map_unit_env_if_lazy (* TODO move this now that we use it twice *)
         (fun _ tr -> eq_constr tr (first_fun arg_typ))
         (fun en -> expand_eta en evd)
         env
         trm)
  in
  let unpacked_app_red = reduce_nf env orn_app in
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
 * in terms of the ornament and indexer applied to the specific arguments
 *
 * !!! TODO should be able to avoid unfolding/refolding if we assume
 * we always have recursive ornaments
 *)
let reduce_ornament_f l env evd orn trm args =
  map_term_env_if
    (fun en _ trm ->
      if applies orn trm then (* TODO unsure if general *)
        let arg = last_arg trm in
        if isApp arg then
          not (Option.has_some (search_lifted en (first_fun arg)))
        else
          true
      else
        false)
    (fun env args trm ->
      fold_back_constants
        env
        (fun trm ->
          List.fold_right
            (fun arg trm ->
              try
                meta_reduce l evd orn env arg trm
              with _ ->
                trm (* TODO investigate why failing *) )
            args
            trm)
        trm)
    shift_all
    env
    args
    trm

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
      eq_constr to_typ (first_fun (dummy_index env (dest_sigT typ).packer))
    else
      false

(*
 * Filter the arguments to only the ones that have the type we are
 * promoting/forgetting from.
 *)
let filter_orn l env evd (from_typ, to_typ) args =
  List.filter (on_type (is_orn l env evd (from_typ, to_typ)) env evd) args

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
 * When we ornament in both directions and we're currently reducing g o f
 * where g is the promotion/forgetful function and f is already reduced,
 * we need to unpack applications of the function to the inductive
 * hypotheses. This function does that.
 *
 * TODO messy after extending, and need to get working for indices
 * (need to pass right function, but if we do that then we lose this
 * fuctionality, so we need both c_g and c_f for indexes)
 *)
let unpack_ihs env evd f ihs trm l =
  let unpacked_body =
    map_term_env_if
      (fun en ihs t ->
        isApp t && Option.has_some (search_lifted en (first_fun t)))
      (fun en ihs t ->
        let f = first_fun t in
        let args =
          List.map
            (fun a ->
              map_term_env_if
                (fun _ ihs t -> List.exists (eq_constr t) ihs)
                (fun en _ t ->
                  forget_assum en evd l t)
                shift_all
                en
                ihs
                a)
            (unfold_args t)
        in mkAppl (f, args))
      shift_all
      env
      ihs
      trm
  in
  if l.is_indexer then
    map_unit_if
      (fun t ->
        isApp t && applies f t && List.exists (eq_constr (last_arg t)) ihs)
      last_arg
      unpacked_body
  else
    unpacked_body

(*
 * This reduces the body of an ornamented constructor to a reasonable term,
 * when we ornament in both directions
 *)
let reduce_constr_body env env_new evd l (from_typ, to_typ) index_args body =
  let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
  let all_args = mk_n_rels (nb_rel env) in
  let orn_args = filter_orn l env evd (from_typ, to_typ) all_args in
  let ihs = List.map (fun (_, (ih, _)) -> ih) index_args in
  let pre = map_unit_if (applies f) (pre_reduce l env evd) body in
  let red_body =
    map_if
      (fold_back_constants env (reduce_nf env))
      (*(List.length index_args = 0 && not l.is_indexer)*)
      false (* TODO superficial deps; avoid unfolding inner things here/unfold only iff constr *)
      (map_unit_if
         (applies f)
         (fun trm ->
           reduce_ornament_f l env evd f trm orn_args)
         pre)
  in unpack_ihs env_new evd f ihs red_body l

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
let pack_ihs c_f_old l env evd (from_typ, to_typ) c_g =
  let index_args = indexes to_typ (Option.get l.orn.index_i) (arity c_f_old) c_f_old in
  let nhs = arity c_f_old - List.length index_args in
  List.map
    (fun arg ->
      if on_type (is_or_applies to_typ) env evd arg then
        pack_inner env evd l arg
      else
        arg)
    (get_n_hypos nhs c_g)

let promotion_type env evd trm =
  fst (on_type ind_of_promotion_type env evd trm)
    
(*
 * Compose two constructors for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * For now, this does not handle nested induction.
 *)
let compose_c evd npms_g ip_g p assum_ind post_assums (comp : composition) =
  let l = comp.l in
  let (env_g, c_g) = comp.g in
  let (env_f, c_f_old) = comp.f in
  let (orn_f, orn_g) = (l.orn.forget, l.orn.promote) in
  let to_typ = zoom_sig (promotion_type env_f evd orn_f) in
  let from_typ = first_fun (promotion_type env_g evd orn_g) in
  let c_f = compose_ih evd npms_g ip_g p comp in
  zoom_apply_lambda_n
    (nb_rel env_f)
    (fun env trm ->
      if not comp.is_g then
        (* it's still unclear to me why local_max is what it is *)
        let local_max = directional l 0 (List.length post_assums) in
        let s_off = shift_local local_max (offset2 env env_g) in
        let f = forget_assums env evd l (s_off (mkRel assum_ind)) (s_off c_g) in
        let lift_args = map_directional (pack_ihs c_f_old) project_ihs l in
        let args = lift_args l env evd (from_typ, to_typ) c_g in
        reduce_term env (mkAppl (f, args))
      else
        let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
        let index_i = Option.get l.orn.index_i in
        let c_indexed = if l.is_indexer then c_f else directional l c_g c_f in
        let index_args = indexes to_typ index_i (arity c_g) c_indexed in
        in_lambda_body
          (fun env_old _ ->
            let args = snoc trm (non_index_typ_args l env_old evd trm) in
            let app = mkAppl (f, args) in
            reduce_constr_body env_old env evd l (from_typ, to_typ) index_args app)
          env_f
          c_f_old)
    env_f
    c_f

(* Map compose_c *)
let compose_cs evd npms ip p assum_ind post_assums comp gs fs =
  let comp_cs =
    List.map2
      (fun c_g c_f -> { comp with g = (fst gs, c_g); f = (fst fs, c_f)})
      (snd gs)
      (snd fs)
  in List.map (compose_c evd npms ip p assum_ind post_assums) comp_cs

(*
 * Build the lifted indexer, if applicable
 *)
let build_lifted_indexer evd assum_ind comp =
  let l = comp.l in
  let (env, f) = comp.f in
  if l.is_fwd && comp.is_g && not l.is_indexer then
    try
      let indexer = Option.get l.orn.indexer in
      let (env_b, b) = zoom_lambda_term env f in
      let index_args = snoc b (on_type unfold_args env_b evd b) in
      let indexer_app = mkAppl (indexer, index_args) in
      let unpacked = reconstruct_lambda env_b indexer_app in
      ({ comp with l }, Some unpacked)
    with _ ->
      Printf.printf "%s\n\n" "WARNING: Failed to define indexer";
      (comp, None)
  else
    (comp, None)

(*
 * Compose two applications of an induction principle that are
 * structurally the same when one is an ornament.
 *)
let rec compose_inductive evd post_assums assum_ind comp =
  let (env_g, g) = comp.g in
  let (env_f, f) = comp.f in
  let f_app = deconstruct_eliminator env_f evd f in
  let g_app = deconstruct_eliminator env_g evd g in
  let npms = List.length g_app.pms in
  let (comp, indexer) = build_lifted_indexer evd assum_ind comp in
  let c_p = { comp with g = (env_g, g_app.p); f = (env_f, f_app.p) } in
  let p = compose_p evd npms assum_ind c_p in
  let gs = (env_g, g_app.cs) in
  let fs = (env_f, f_app.cs) in
  let cs = compose_cs evd npms g_app.elim p assum_ind post_assums comp gs fs in
  let curried_args = mk_n_rels (arity p - List.length f_app.final_args) in
  let final_args = List.append f_app.final_args curried_args in
  (apply_eliminator {f_app with p; cs; final_args}, indexer)

(*
 * When composing factors, determine if we have an application of
 * the forgetful function. Return (f_forgets, g_forgets).
 *)
let forgets l g f =
  if not l.is_indexer then
    let (env_g, g) = g in
    let (env_f, f) = f in
    let forget = l.orn.forget in
    let f_forgets = is_or_applies forget f in
    let g_forgets = is_or_applies forget g in
    (f_forgets, isApp f && g_forgets)
  else
    (false, false)

(*
 * When composing factors, determine if we have an application of
 * the promotion function. Return (f_promotes, g_promotes).
 *)
let promotes evd l assum_ind g f =
  if not l.is_indexer then
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
  else
    (false, false)

(*
 * When composing factors, determine if we have an application of
 * the indexer. Return (f_indexes, g_indexes, is_inner).
 *)
let is_indexer l g f =
  if l.is_indexer then
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
  else
    (false, false, false)

(*
 * Configure the composition
 *)
let configure_compose_inductive evd assum_ind l (f, g) is_g =
  let g_ind = (fst g, reduce_to_ind (fst g) (snd g)) in
  let f_ind = (fst f, reduce_to_ind (fst f) (snd f)) in
  let comp = { l ; g = g_ind ; f = f_ind ; is_g } in
  let existT_f = applies existT (snd f_ind) in
  let existT_g = applies existT (snd g_ind) in
  if existT_f || existT_g then
    let exT_ind = if existT_f then f_ind else g_ind in
    let exT = if existT_f then f else g in
    let orn_body = unwrap_definition (fst f_ind) (lift_to l) in
    let env_orn = zoom_env zoom_lambda_term empty_env orn_body in
    let unpacked = (dest_existT (snd exT_ind)).unpacked in
    let c = reconstruct_lambda env_orn (shift_by (nb_rel env_orn) unpacked) in
    let typ_args = List.rev (List.tl (List.rev (unfold_args (snd exT)))) in
    let c_args = map_if (snoc (mkRel assum_ind)) existT_f typ_args in
    let exT_inner = reduce_term (fst exT_ind) (mkAppl (c, c_args)) in
    let exT_ind = zoom_lambda_term (fst exT_ind) exT_inner in
    if existT_f then { comp with f = exT_ind } else { comp with g = exT_ind }
  else
    comp

(*
 * Compose factors of an ornamented, but not yet reduced function
 *
 * Note: Now that we are in sigmas, we can probably go back to non-dependent
 * factoring. But that is a major effort, so for now we just always get the
 * last factor.
 *)
let rec compose_orn_factors evd (l : lifting) assum_ind fs =
  let compose_rec l fs = compose_orn_factors evd l assum_ind fs in
  match fs with
  | Factor ((en, t), children) ->
     if List.length children > 0 then
       let post_assums = mk_n_rels (assum_ind - 1) in
       let ((t_app, indexer), env, composed) = compose_rec l (last children) in
       let g = zoom_lambda_term en t in
       let f = (env, t_app) in
       let (f_is_indexer, g_is_indexer, is_indexer_inner) = is_indexer l g f in
       let is_index = f_is_indexer || g_is_indexer in
       let (f_promotes, g_promotes) = promotes evd l assum_ind g f in
       let (f_forgets, g_forgets) = forgets l g f in
       let is_promote = f_promotes || g_promotes in
       let is_forget = f_forgets || g_forgets in
       if is_promote || is_forget || is_index then
         let is_g = g_promotes || g_forgets || g_is_indexer in
         let comp = configure_compose_inductive evd assum_ind l (f, g) is_g in
         let comped = compose_inductive evd post_assums assum_ind comp in
         (comped, fst comp.f, true)
       else
         let t = shift_by assum_ind t in
         let num_child = List.length children in
         let t_args =
           if num_child > 1 && l.is_indexer then
             let index = Array.get (Array.of_list children) (num_child - 2) in
             let ((t_app_index, _), _, _) = compose_rec l index in
             List.append [t_app_index; t_app] post_assums
           else if not composed then
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
let internalize env evd (l : lifting) (trm : types) =
  let (assum_ind, fs) = factor_ornamented l.orn env evd trm in
  let ((body, indexer), env_body, _) = compose_orn_factors evd l assum_ind fs in
  let reconstructed = reconstruct_lambda env_body body in
  let rec pack_hypos en tr = (* TODO move, explain *)
    match kind_of_term tr with
    | Lambda (n, t, b) ->
       let t' =
         map_term_env_if
           (fun _ assum tr -> try eq_constr assum tr with _ -> false)
           (fun en assum tr ->
             let typ_app = on_type dest_sigT en evd tr in
             let index_type = typ_app.index_type in
             let packer = typ_app.packer in
             let index = project_index typ_app tr in
             let unpacked = project_value typ_app tr in
             pack_existT {index_type; packer; index; unpacked})
           shift
           en
           (mkRel (assum_ind - arity tr))
           t
       in mkLambda (n, t', pack_hypos (push_local (n, t') en) b)
    | _ ->
       tr
  in (map_forward (pack_hypos env_body) l reconstructed, indexer)

(* --- Lifting induction principle --- *)

(* TODO temporary: before full refactor is done, just forget/promote the
   arguments (later this will be done implicitly in a later step, and as
   such this doesn't fully work right now when you have product arguments) *)
let lift_args_temporary env evd l npms args =
  let arg = map_backward last_arg l (last args) in
  let typ_args = non_index_typ_args l env evd arg in
  let lifted_arg = mkAppl (lift_to l, snoc arg typ_args) in
  let index_i = (Option.get l.orn.index_i) - npms in
  let value_i = List.length args - 1 in
  if l.is_fwd then
    let lifted_arg_sig = on_type dest_sigT env evd lifted_arg in
    let index = project_index lifted_arg_sig lifted_arg in
    let value = project_value lifted_arg_sig lifted_arg in
    insert_index index_i index (reindex value_i value args)
  else
    remove_index index_i (reindex value_i lifted_arg args)

(* Lift the motive *)
(* TODO refactor out common code w/ above *)
let lift_motive env evd l npms parameterized_elim motive =
  let parameterized_elim_type = reduce_type env evd parameterized_elim in
  let (_, to_motive_typ, _) = destProd parameterized_elim_type in
  let env_to_motive = zoom_env zoom_product_type env to_motive_typ in
  let off = offset2 env_to_motive env in
  let motive = shift_by off motive in
  let index_i = (Option.get l.orn.index_i) - npms in
  let args = mk_n_rels off in
  let arg = last args in
  let typ_args = non_index_typ_args l env_to_motive evd arg in
  let value_i = List.length args - 1 in
  if l.is_fwd then
    (* PROMOTE-MOTIVE *)
    let lifted_arg = pack_inner env_to_motive evd l arg in
    let args = remove_index index_i (reindex value_i lifted_arg args) in
    let motive_app = reduce_term env_to_motive (mkAppl (motive, args)) in
    reconstruct_lambda_n env_to_motive motive_app (nb_rel env)
  else
    (* FORGET-MOTIVE *)
    let lifted_arg = mkAppl (lift_back l, snoc arg typ_args) in
    let lifted_arg_sig = on_type dest_sigT env_to_motive evd lifted_arg in
    let index = project_index lifted_arg_sig lifted_arg in
    let value = project_value lifted_arg_sig lifted_arg in
    let args = insert_index index_i index (reindex value_i value args) in 
    let motive_app = reduce_term env_to_motive (mkAppl (motive, args)) in
    reconstruct_lambda_n env_to_motive motive_app (nb_rel env)

(* Lift a case *)
(* TODO clean a bunch *)
(* TODO better base-case detection *)
let lift_case env evd l (from_typ, to_typ) p c_elim c =
  let c_eta = expand_eta env evd c in
  let c_elim_type = reduce_type env evd c_elim in
  let (_, to_c_typ, _) = destProd c_elim_type in
  let rec num_ihs env typ =
    match kind_of_term typ with
    | Prod (n, t, b) ->
       if is_or_applies to_typ (reduce_term env t) then
         let (n_b_t, b_t, b_b) = destProd b in
         1 + num_ihs (push_local (n, t) (push_local (n_b_t, b_t) env)) b_b
       else
         num_ihs (push_local (n, t) env) b
    | _ ->
       0
  in
  let nihs = num_ihs env to_c_typ in
  if nihs = 0 then
    c (* base case *)
  else
    let env_to_c = zoom_env zoom_product_type env to_c_typ in
    let off = offset2 env_to_c env in
    let c_eta = shift_by off c_eta in
    let (env_c_body, c_body) = zoom_lambda_term env_to_c c_eta in
    let (c_f, c_args) = destApp c_body in
    let is_rec a =
      match kind_of_term a with
      | Rel i when i <= nb_rel env_c_body ->
         on_type (is_or_applies from_typ) env_c_body evd a
      | _ ->
         false
    in
    let index_i = Option.get l.orn.index_i in
    if l.is_fwd then
      (* PROMOTE-CASE *)
      let rec lift_args args index =
        match args with
        | h :: tl ->
           if eq_constr h index then
             shift h :: (lift_args (shift_all tl) index)
           else
             let h_typ = reduce_type env_to_c evd h in
             if is_or_applies to_typ h_typ then
               let h_lifted = pack_inner env_to_c evd l h in
               h_lifted :: lift_args tl (get_arg index_i h_typ)
             else
               h :: lift_args tl index
        | _ -> []
      in
      let (c_args, b_args) = take_split (off - nihs) (Array.to_list c_args) in
      let c_args = unshift_all_by (List.length b_args) c_args in
      let c_to_args = List.rev (lift_args (List.rev c_args) (mkRel 0)) in
      let c_to_f = unshift_by (offset2 env_c_body env_to_c) c_f in
      let c_to_body = reduce_term env_to_c (mkAppl (c_to_f, c_to_args)) in
      reconstruct_lambda_n env_to_c c_to_body (nb_rel env)
    else
      (* FORGET-CASE *)
      let rec lift_args args (index, proj_index) =
        match args with
        | h :: tl ->
           if eq_constr h index then
             proj_index :: (lift_args (unshift_all tl) (index, proj_index))
           else
             let h_typ = reduce_type env_c_body evd h in
             if is_or_applies from_typ h_typ then
               let typ_args = non_index_typ_args l env_to_c evd h in
               let h_lifted = mkAppl (lift_back l, snoc h typ_args) in
               let h_lifted_typ = on_type dest_sigT env_to_c evd h_lifted in
               let proj_value = project_value h_lifted_typ h_lifted in
               let proj_index = project_index h_lifted_typ h_lifted in
               proj_value :: lift_args tl (get_arg index_i h_typ, proj_index)
             else
               h :: lift_args tl (index, proj_index)
        | _ -> []
      in
      let (c_args, b_args) = take_split (off + nihs) (Array.to_list c_args) in
      let c_args = unshift_all_by (List.length b_args) c_args in
      let c_to_args = List.rev (lift_args (List.rev c_args) (mkRel 0, mkRel 0)) in
      let c_to_f = unshift_by (offset2 env_c_body env_to_c) c_f in
      let c_to_body = reduce_term env_to_c (mkAppl (c_to_f, c_to_args)) in
      reconstruct_lambda_n env_to_c c_to_body (nb_rel env)
                         
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
 * This lifts the induction principle.
 * The input term should be fully eta-expanded before calling this,
 * and should not contain extra arguments after induction.
 *
 * The old application and meta-reduction steps were just hacks to accomplish
 * this. So they did this work, but also a lot more work.
 * Accordingly, when this is done, we'll remove the old application
 * and meta-reduction steps.
 *)
let lift_induction_principle_core env evd l trm =
  let to_typ = zoom_sig (promotion_type env evd l.orn.forget) in
  let from_typ = first_fun (promotion_type env evd l.orn.promote) in
  let (from_typ, to_typ) = map_backward reverse l (from_typ, to_typ) in
  let trm_app = deconstruct_eliminator env evd trm in
  let npms = List.length trm_app.pms in
  let elim = type_eliminator env (fst (destInd to_typ)) in
  let param_elim = mkAppl (elim, trm_app.pms) in
  let p = lift_motive env evd l npms param_elim trm_app.p in
  let p_elim = mkAppl (param_elim, [p]) in
  let cs = lift_cases env evd l (from_typ, to_typ) p p_elim trm_app.cs in
  let final_args = lift_args_temporary env evd l npms trm_app.final_args in
  apply_eliminator {trm_app with elim; p; cs; final_args}

(* TODO temporary: pre-process to test just lifting induction principle *)
let lift_induction_principle env evd l def =
  let to_typ = zoom_sig (promotion_type env evd l.orn.forget) in
  let from_typ = first_fun (promotion_type env evd l.orn.promote) in
  let (from_typ, to_typ) = map_backward reverse l (from_typ, to_typ) in
  let trm = expand_eta env evd (unwrap_definition env def) in
  let (env, body) = zoom_lambda_term env trm in
  let body = reduce_to_ind env body in
  let body = reduce_term env body in
  let body_app = deconstruct_eliminator env evd body in
  let npms = List.length body_app.pms in
  let value_i = arity (expand_eta env evd from_typ) - npms in
  let final_args = take (value_i + 1) body_app.final_args in
  let body = apply_eliminator { body_app with final_args } in
  let off = List.length body_app.final_args - (value_i + 1) in
  let body = lift_induction_principle_core env evd l body in
  let dummy_args = Array.make off (mkRel 0) in
  let postprocess_lam = reconstruct_lambda_n env body (offset env off) in
  let postprocess_env = pop_rel_context off env in
  let postprocess = reduce_term postprocess_env (mkApp (postprocess_lam, dummy_args)) in
  reconstruct_lambda postprocess_env postprocess

(* --- Lifting constructions --- *)

(* 
 * Using the refolding algorithm, lift the constructor function and arguments
 *)
let lift_construction_core env evd l trm =
  (* LIFT-CONSTR-ARGS & LIFT-CONSTR-FUN *)
  let to_typ = zoom_sig (promotion_type env evd l.orn.forget) in
  let from_typ = first_fun (promotion_type env evd l.orn.promote) in
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
  let orn_app = mkAppl (orn, snoc trm typ_args) in
  if List.length rec_args = 0 then
    (* base case - don't bother refolding *)
    reduce_nf env orn_app
  else
    (* inductive case - refold *)
    List.fold_left
      (fun t a ->
        let a_typ_args = non_index_typ_args l env evd a in
        all_eq_substs (a, mkAppl (orn, snoc a a_typ_args)) t)
      (reduce_ornament_f l env evd orn orn_app rec_args)
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
let lift_existential_construction env evd l trm =
  (* LIFT-CONSTR *)
  let inner_construction = map_backward last_arg l trm in
  let constr = first_fun inner_construction in
  let args = unfold_args inner_construction in
  let (env_c_body, c_body) = zoom_lambda_term env (expand_eta env evd constr) in
  let c_body = reduce_term env_c_body c_body in
  let to_refold = map_backward (pack env_c_body evd l) l c_body in
  let refolded = lift_construction_core env_c_body evd l to_refold in
  let lifted_constr = reconstruct_lambda_n env_c_body refolded (nb_rel env) in
  reduce_term env (mkAppl (lifted_constr, args))

(* TODO temporary: pre-process to test just lifting construction *)
let lift_construction env evd l def =
  let to_typ = zoom_sig (promotion_type env evd l.orn.forget) in
  let from_typ = first_fun (promotion_type env evd l.orn.promote) in
  let (from_typ, to_typ) = map_backward reverse l (from_typ, to_typ) in
  let trm = expand_eta env evd (unwrap_definition env def) in
  let (env, body) = zoom_lambda_term env trm in
  let body = unwrap_definition env body in
  let body = reduce_term env body in
  assert (on_type (is_or_applies from_typ) env evd (map_backward last_arg l body));
  reconstruct_lambda env (lift_existential_construction env evd l body)
  
(* --- Higher lifting --- *)

(*
 * TODO in reduction step: avoid reducing anything that is higher-lifted!
 *)

(*
 * Substitute every term of the type we are promoting/forgetting from
 * with a term with the corresponding promoted/forgotten type
 *
 * LATER: This doesn't yet handle partial applications of constructors;
 * need to handle that at some point.
 * Also, should clean more.
 *
 * TODO will need to eta everywhere, for now just trying to hook in w/
 * new rules
 *)
let substitute_lifted_terms env evd l (from_type, to_type) index_type trm =
  let trm =
    map_unit_env_if_lazy
      (fun _ tr ->
        match kind_of_term tr with
        | Construct (((i, i_index), _), u) ->
           let ind = mkInd (i, i_index) in
           eq_constr ind (directional l from_type to_type)
        | _ ->
           false (* TODO also handle type list/vect *))
      (fun en -> expand_eta en evd)
      env
      trm
  in
  let index_i = Option.get l.orn.index_i in
  let typ_is_orn en t = on_type (is_orn l en evd (from_type, to_type)) en evd t in
  let rec sub_rec en index_type tr =
    let lifted_opt = search_lifted en tr in
    let has_lifted = Option.has_some lifted_opt in
    if has_lifted then
      (* substitute in a lower-lifted term *)
      Option.get lifted_opt
    else if is_orn l en evd (from_type, to_type) tr then
      (* substitute in a lifted type *)
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
    else
      match kind_of_term tr with
      | Cast (c, k, t) ->
         let c' = sub_rec en index_type c in
         let t' = sub_rec en index_type t in
         mkCast (c', k, t')
      | Prod (n, t, b) ->
         let t' = sub_rec en index_type t in
         let en_b = push_local (n, t) en in
         let b' = sub_rec en_b (shift index_type) b in
         mkProd (n, t', b')
      | Lambda (n, t, b) ->
         let t' = sub_rec en index_type t in
         let en_b = push_local (n, t) en in
         let b' = sub_rec en_b (shift index_type) b in
         mkLambda (n, t', b')
      | LetIn (n, trm, typ, e) ->
         let trm' = sub_rec en index_type trm in
         let typ' = sub_rec en index_type typ in
         let en_e = push_let_in (n, e, typ) en in
         let e' = sub_rec en_e (shift index_type) e in
         mkLetIn (n, trm', typ', e')
      | App (fu, args) ->
         let args = Array.to_list args in
         if (not (Option.has_some (search_lifted en fu))) && typ_is_orn en tr then
           if (l.is_fwd || l.is_indexer) && isConstruct (first_fun (reduce_term en tr)) then (* TODO should be able to get rid of reduction here at some point *)
             let tr' = lift_existential_construction en evd l tr in
             let (fu', args') = destApp tr' in
             mkApp (fu', Array.map (sub_rec en index_type) args')
           else if (not l.is_fwd) && eq_constr existT fu then
             let last_arg = last args in
             if isApp last_arg && isConstruct (first_fun (reduce_term en last_arg)) then
               let tr' = lift_existential_construction en evd l tr in
               let (fu', args') = destApp tr' in
               mkApp (fu', Array.map (sub_rec en index_type) args')
             else
               sub_rec en index_type last_arg
           else if eq_constr (lift_back l) fu then
             (* SECTION-RETRACTION *)
             last_arg tr
           else if l.is_fwd || l.is_indexer then
             failwith "not yet implemented" (* pack somehow *)
           else
             failwith "invalid input"
         else if eq_constr projT2 fu && typ_is_orn en (last args) then
           reduce_term en (sub_rec en index_type (last args))
           (* TODO indexer rule, projections in other direction *)
         else if eq_constr (lift_to l) fu then
           (* INTERNALIZE *)
           sub_rec en index_type (last_arg tr) (* TODO eventually will not need to recurse when we remove reduction step *)
         else
           (* APP *)
           let args' = List.map (sub_rec en index_type) args in
           let fu' = sub_rec en index_type fu in
           mkAppl (fu', args')
      | Case (ci, ct, m, bs) ->
         let ct' = sub_rec en index_type ct in
         let m' = sub_rec en index_type m in
         let bs' = Array.map (sub_rec en index_type) bs in
         mkCase (ci, ct', m', bs')
      | Fix ((is, i), (ns, ts, ds)) ->
         let ts' = Array.map (sub_rec en index_type) ts in
         let ds' = Array.map (map_rec_env_fix sub_rec shift en index_type ns ts) ds in
         mkFix ((is, i), (ns, ts', ds'))
      | CoFix (i, (ns, ts, ds)) ->
         let ts' = Array.map (sub_rec en index_type) ts in
         let ds' = Array.map (map_rec_env_fix sub_rec shift en index_type ns ts) ds in
         mkCoFix (i, (ns, ts', ds'))
      | Proj (pr, c) ->
         let c' = sub_rec en index_type c in
         mkProj (pr, c')
      | Construct _  when typ_is_orn en tr ->
         lift_existential_construction en evd l tr
      | _ ->
         tr
  in sub_rec env index_type trm

let type_is_orn l env evd (from_type, to_type) trm =
  on_type (is_orn l env evd (from_type, to_type)) env evd trm
             
let is_packed_constr l env evd (from_type, to_type) trm =
  let right_type = type_is_orn l env evd (from_type, to_type) in
  match kind_of_term trm with
  | Construct _  when right_type trm ->
     true
  | App (f, args) ->
     if l.is_fwd then
       isConstruct f && right_type trm
     else
       if eq_constr existT f && right_type trm then
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
    match kind_of_term trm with
    | App (f, args) ->
       eq_constr existT f && right_type trm
    | _ ->
       false

let is_proj l env evd (from_type, to_type) trm =
  let right_type = type_is_orn l env evd (from_type, to_type) in
  match kind_of_term trm with
  | App (f, args) ->
     if l.is_fwd then
       eq_constr (Option.get l.orn.indexer) f && right_type (last_arg trm)
     else
       (eq_constr projT1 f || eq_constr projT2 f) && right_type (last_arg trm)
  | _ ->
     false

let is_eliminator l env evd (from_type, to_type) trm =
  let right_type = type_is_orn l env evd (from_type, to_type) in
  match kind_of_term trm with
  | App (f, args) when isConst f ->
     let maybe_ind = inductive_of_elim env (destConst f) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       eq_constr (mkInd (ind, 0)) (directional l from_type to_type)
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
      let tr' = lift_existential_construction en evd l tr in
      match kind_of_term tr with
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
      else if eq_constr projT1 (first_fun tr) then
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
      let tr_elim_curr = apply_eliminator { tr_elim with final_args } in
      let tr' = lift_induction_principle_core en evd l tr_elim_curr in
      let tr'' = lift en index_type tr' in
      let post_args' = List.map (lift en index_type) post_args in
      mkAppl (tr'', post_args')
    else
      match kind_of_term tr with
      | App (f, args) ->
         if eq_constr (lift_back l) f then
           (* SECTION-RETRACTION *)
           last_arg tr
         else if eq_constr (lift_to l) f then
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
         if eq_constr ind (directional l from_type to_type) then
           (* lazy eta expansion *)
           lift en index_type (expand_eta en evd tr)
         else
           tr
      | Const _ ->
         (* CONST *)
         if eq_constr tr projT1 || eq_constr tr projT2 || is_elim en tr then
           tr
         else
           (try
              let def = lookup_definition en tr in
              let lifted = lift en index_type def in
              if eq_constr def lifted then
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
  let indexing_proof = None in (* TODO implement *)
  let trm = unwrap_definition env def in
  let promotion_type en t = fst (on_type ind_of_promotion_type en evd t) in
  let forget_typ = promotion_type env l.orn.forget in
  let promote_typ = promotion_type env l.orn.promote in
  let typs = (first_fun promote_typ, zoom_sig forget_typ) in
  let index_type = (dest_sigT forget_typ).index_type in
  let lifted = lift_core env evd l typs index_type trm in
  (lifted, None)

(*
 * Implementation of higher lifting, which substitutes in the lifted
 * functions, the ornamented and reduced terms, and the ornamented types
 *)
let do_higher_lift env evd (l : lifting) trm =
  let promotion_type en t = fst (on_type ind_of_promotion_type en evd t) in
  let forget_typ = promotion_type env l.orn.forget in
  let promote_typ = promotion_type env l.orn.promote in
  let typs = (first_fun promote_typ, zoom_sig forget_typ) in
  let index_type = (dest_sigT forget_typ).index_type in
  substitute_lifted_terms env evd l typs index_type trm

(*
 * Given a reduced lifting of a proof term that refers to other
 * terms that have already been lifted, lift the proof to
 * use the lifted versions of those terms
 *)
let higher_lift env evd (l : lifting) def =
  let indexing_proof = None in (* TODO implement *)
  let trm = unwrap_definition env def in
  let higher_lifted = do_higher_lift env evd l trm in
  (higher_lifted, indexing_proof)
