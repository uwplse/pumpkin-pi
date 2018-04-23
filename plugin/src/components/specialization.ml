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
  let index_typ = infer_type env evd index in
  let packer = abstract_arg env evd index_i typ in
  let ex = pack_existT index_typ packer index unpacked in
  mkAppl (lift_back l, snoc ex (remove_index index_i typ_args))

(*
 * Get the arguments for composing two applications of an induction
 * principle that are structurally the same when one is an ornament.
 *)
let compose_p_args evd npms post_assums inner comp =
  let l = comp.l in
  let (env, p) = comp.f in
  let index_i = Option.get l.orn.index_i in
  let (env_b, p_b) = zoom_lambda_term env p in
  let orn_app =
    if not inner then
      let off = offset2 env_b env in
      let nargs = arity (unwrap_definition env (lift_back l)) in
      let shift_pms = shift_local off (off + List.length post_assums) in
      shift_pms (mkAppl (lift_back l, mk_n_rels nargs))
    else
      pack_inner env_b evd l (mkRel 1)
  in
  let reindex_if_sig = map_if (remove_index index_i) (applies sigT p_b) in
  let inner_args = reindex_if_sig (unfold_args (zoom_if_sig_app p_b)) in
  snoc orn_app (snd (take_split npms inner_args))

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
  map_directional
    (fun p_g ->
      map_default
        (fun _ ->(* TODO may not yet handle HOFs *)
          let (env_p_g, p_g_b) = zoom_lambda_term env_g p_g in
          let index_typ = infer_type env_p_f evd (mkRel 2) in
          let abs_i = reindex_body (reindex_app (reindex index_i (mkRel 1))) in
          let packer = abs_i (mkLambda (Anonymous, index_typ, shift p_g_b)) in
          let p_g_packed = pack_sigT index_typ packer in
          reconstruct_lambda_n env_p_g p_g_packed (nb_rel env_g))
        p_g
        l.lifted_indexer) (* when does this condition fire? *)
    (map_unit_env_if
       (fun _ -> is_or_applies existT)
       (fun env trm ->
         (* TODO really should be applying orn_inv, then simplifying *)
         (* it will look like inside of compose_c *)
         (* so try other proofs and see where this breaks *)
         let la = last_arg trm in
         if contains_term la (mkRel 1) then
           la
         else
           trm)
       env_p_f)
    (* TODO will fail with cosntant existT like nilV, try *)
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
  let env_p_f = zoom_env zoom_lambda_term env_f p_f in
  let p_args = compose_p_args evd npms post_assums inner comp in
  let p = compose_p_fun evd comp in
  let app = reduce_term env_p_f (mkAppl (p, p_args)) in
  reconstruct_lambda_n env_p_f app (nb_rel env_f)

(*
 * Compose the IH for a constructor.
 * This simply uses the new property p.
 *)
let compose_ih env_g evd npms_g ip_g c_f p =
  let ip_g_typ = reduce_type env_g evd ip_g in
  let from_typ = first_fun (fst (ind_of_promotion_type ip_g_typ)) in
  map_term_env_if
    (fun _ _ trm -> is_or_applies from_typ trm)
    (fun en p trm ->
      let orn_final = [mkRel 1] in
      let (_, _, orn_final_typ) = CRD.to_tuple @@ lookup_rel 1 en in
      let typ_args = shift_all (unfold_args orn_final_typ) in
      let (_, non_pms) = take_split npms_g typ_args in
      reduce_term en (mkAppl (mkAppl (p, non_pms), orn_final)))
    shift
    env_g
    p
    c_f

(*
 * TODO move
 * Only reduce until you have an application of an induction principle,
 * or reducing doesn't change the term
 * Then, do nothing
 *)
let rec reduce_to_ind env trm =
  match kind_of_term trm with
  | App (_, _) when is_elim env (first_fun trm) ->
     trm
  | _ ->
     let reduced = chain_reduce reduce_term delta env trm in
     map_if (reduce_to_ind env) (not (eq_constr reduced trm)) reduced
            
(*
 * TODO move
 * Delta-unfold, simplify, delta-unfold internally, simplify, and so on
 * until nothing changes
 *
 * for reducing ornaments
 * assumes promotion for now
 * also assumes assumption at index 1,
 * need to support IHs at other indices. (TODO)
 *)
let reduce_ornament_f l env evd index_i orn trm orn_args =
  let orn_arg_typs = List.map (on_type zoom_if_sig_lambda env evd) orn_args in
  let orn_arg_typs = List.map (map_backward (fun t -> unshift (snd (zoom_lambda_term empty_env t))) l) orn_arg_typs in
  (* TODO inefficient now *)
  List.fold_left2
    (fun trm orn_arg orn_arg_typ ->
       map_term_env_if
         (fun _ orn_arg_typ trm -> applies orn trm)
         (fun env orn_arg_typ trm ->
           try
             let (app, app_sub_body, app_sub) =
               let unfolded = chain_reduce reduce_term delta env trm in
               let typ_args = map_backward (remove_index index_i) l (unfold_args orn_arg_typ) in
               let orn_app = mkAppl (orn, snoc orn_arg typ_args) in
               let orn_app_ind = reduce_to_ind env orn_app in
               let orn_app_red = reduce_nf env orn_app in
               if l.is_fwd && not l.is_indexer then
                 let indexer = reduce_nf env (get_arg 2 unfolded) in
                 let app = reduce_nf env (get_arg 3 unfolded) in
                 let orn_app_app = get_arg 3 orn_app_ind in
                 let orn_app_app_arg = last_arg orn_app_app in
                 let packed_type_old = reduce_type env evd orn_app_app in
                 let index_type = reduce_type env evd (get_arg index_i packed_type_old) in
                 let packed_type = abstract_arg env evd index_i packed_type_old in
                 let orn_app_indexer = project_index index_type packed_type orn_app_app_arg in
                 let orn_app_app_arg = project_value index_type packed_type orn_app_app_arg in
                 let orn_app_red_app = get_arg 3 orn_app_red in
                 let orn_app_indexer_red = get_arg 2 orn_app_red in
                 let ind_sub = all_eq_substs (orn_app_indexer_red, orn_app_indexer) indexer in
                 let app_sub = all_eq_substs (orn_app_red_app, orn_app_app_arg) app in
                 let app_ind_sub = all_eq_substs (orn_app_indexer_red, orn_app_indexer) app_sub in
                 (app, app_ind_sub, mkAppl (existT, reindex 3 app_ind_sub (reindex 2 ind_sub (unfold_args unfolded))))
               else if not l.is_indexer then
                 let app = reduce_nf env unfolded in
                 let index_type = get_arg 0 (infer_type env evd orn_arg) in
                 let packed_body = reindex_app (reindex index_i (mkRel 1)) (shift orn_arg_typ) in
                 let packed_type = mkLambda (Anonymous, index_type, packed_body) in
                 let app_projT1 = project_index index_type packed_type orn_arg in
                 let app_projT2 = project_value index_type packed_type orn_arg in
                 let orn_app_app = mkAppl (get_arg 3 orn_app_ind, [app_projT1; app_projT2]) in
                 let orn_app_app_red = reduce_nf env orn_app_app in
                 let app_sub = all_eq_substs (orn_app_app_red, orn_arg) app in
                 (* TODO is that sound? think more about other cases *)
                 (app, app_sub, app_sub)
               else
                 let app = reduce_nf env unfolded in
                 let app_sub = all_eq_substs (orn_app_red, orn_app) app in
                 (app, app_sub, app_sub)
             in if eq_constr app_sub_body app then trm else app_sub
           with _ ->
             trm)
         shift
         env
         orn_arg_typ
         trm)
    trm
    orn_args
    orn_arg_typs

(*
 * Get the (index arg index, IH) pairs for a constructor
 *)
let rec indexes env to_typ index_i f_hs g_hs trm i =
  let num_args = List.length g_hs in
  if List.length f_hs != num_args then
    match (g_hs, kind_of_term trm) with
    | (h :: tl, Prod (n, t, b)) ->
       let num_args_left = num_args - (i + 1) in
       let index_ih_opt = index_ih index_i to_typ (mkRel 1) b num_args_left in
       map_if
         (fun tl -> (i, Option.get index_ih_opt) :: tl)
         (Option.has_some index_ih_opt)
         (indexes (push_local (n, t) env) to_typ index_i f_hs tl b (i + 1))
    | _ ->
       []
  else
    []

(* 
 * Reduces the body of a constructor of an indexer
 *)
let reduce_indexer_constr_body env evd l trm =
  let from = last_arg trm in
  if is_or_applies (lift_back l) from then
    (* eliminate the promotion/forgetful function *)
    let la = last_arg from in
    let la_typ = reduce_type env evd la in
    let idx_type = get_arg 0 la_typ in
    let packed_type = get_arg 1 la_typ in
    project_index idx_type packed_type la
  else
    (* leave as-is *)
    trm

(*
 * Reduces the body of a constructor of a promoted function
 *)
let reduce_promoted_constr_body env evd l trm =
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
let reduce_forgotten_constr_body env evd l trm =
  let from = last_arg trm in
  if is_or_applies existT from then
    let proj = last_arg from in
    if is_or_applies projT2 proj then
      (* eliminate existT of the projection *)
      let unpacked = last_arg proj in
      last_arg unpacked
    else if is_or_applies (lift_to l) proj then
      (* eliminate existT of the forgetful function *)
      last_arg proj
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
 * This reduces the body of an ornamented constructor to a reasonable term
 * TODO handle in a separate step
 *)
let reduce_constr_body env evd l is_orn index_i index_args body =
  let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
  let orn_args = mk_n_rels (nb_rel env) in
  let orn_args = List.filter (on_type (is_orn env) env evd) orn_args in
  map_if
    (reduce_nf env)
    (List.length index_args = 0 && not l.is_indexer)
    (map_unit_if
       (applies f)
       (fun trm ->
         let reduce_body trm =
           if l.is_indexer then
             reduce_indexer_constr_body env evd l trm
           else if l.is_fwd then
             reduce_promoted_constr_body env evd l trm
           else
             reduce_forgotten_constr_body env evd l trm
         in reduce_ornament_f l env evd index_i f (reduce_body trm) orn_args)
       body)

      
  
(*
 * Compose two constructors for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * For now, this does not handle nested induction.
 *
 * TODO clean, refactor orn/deorn, take fewer arguments, etc.
 * TODO can massively simplify with packed type, but will take work
 * to figure out exactly what can go
 *)
let compose_c evd npms_g ip_g p post_assums (comp : composition) =
  let l = comp.l in
  let index_i = Option.get l.orn.index_i in
  let (env_g, c_g) = comp.g in
  let (env_f, c_f) = comp.f in
  let (orn_f, orn_g) = (lift_back l, lift_to l) in
  let orn_f_typ = reduce_type env_f evd orn_f in
  let orn_g_typ = reduce_type env_g evd orn_g in
  let ind_f_typ = fst (ind_of_promotion_type orn_f_typ) in
  let ind_g_typ = fst (ind_of_promotion_type orn_g_typ) in
  let to_typ = map_directional zoom_sig first_fun l ind_f_typ in
  let from_typ = map_directional first_fun zoom_sig l ind_g_typ in
  let (to_typ, from_typ) = map_backward reverse l (to_typ, from_typ) in
  let is_deorn = is_or_applies (if l.is_fwd then to_typ else from_typ) in
  let c_f_used = get_used_or_p_hypos is_deorn c_f in
  let c_g_used = get_all_hypos c_g in
  let env_f_body_old = zoom_env zoom_lambda_term env_f c_f in
  let c_f = compose_ih env_g evd npms_g ip_g c_f p in
  let (env_f_body, f_body) = zoom_lambda_term env_f c_f in
  let (env_g_body, g_body) = zoom_lambda_term env_g c_g in
  let off_f = offset2 env_f_body env_f in
  let is_g = comp.is_g in
  let f_body =
    if not is_g then
      let num_assums = List.length post_assums in
      (* TODO f_f logic unclear *)
      let f_f = shift_local (if l.is_fwd then 0 else num_assums) (offset2 env_f env_g) c_g in
      let f = shift_by off_f f_f in
      let c_used = c_g_used in
      let index_args = indexes env_g to_typ index_i c_f_used c_g_used (lambda_to_prod c_g) 0 in
      let args =
        List.mapi
          (fun i arg ->
            if (not l.is_fwd) && (List.mem_assoc i index_args) then
              let index_type = infer_type env_g_body evd arg in
              let (ih, _) = List.assoc i index_args in
              let ih_typ = reduce_type env_f_body evd ih in
              let typ_args = unfold_args (reduce_term env_f_body ih_typ) in
              let orn = mkAppl (lift_back l, snoc ih typ_args) in
              let orn_typ = reduce_type env_f_body evd orn in
              let packed_type = get_arg 1 orn_typ in
              project_index index_type packed_type orn
            else
              map_unit_env_if
                (fun env trm -> on_type is_deorn env evd trm)
                (fun env trm ->
                  let typ = reduce_type env evd trm in
                  if l.is_fwd then
                    pack_inner env evd l trm
                  else
                    let typ_args = unfold_args typ in
                    let orn = mkAppl (orn_f, snoc trm typ_args) in
                    let orn_typ = reduce_type env evd orn in
                    let packed_type = get_arg 1 orn_typ in
                    (* line below sensitive to how we define ornaments *)
                    let (_, index_type, _) = destLambda packed_type in
                    project_value index_type packed_type orn)
              env_f_body
              arg)
          c_used
      in reduce_term env_f_body (mkAppl (f, args))
    else
      let c_f_all = get_used_or_p_hypos always_true c_f in
      let index_args = indexes env_g to_typ index_i c_f_all c_g_used (lambda_to_prod (if l.is_fwd then c_f else c_g)) 0 in
      let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
      let is_orn env trm =
        let typ = if l.is_fwd then from_typ else shift_by (offset env_f_body 1) ind_g_typ in
        is_or_applies typ trm || convertible env typ trm
      in
      (* Does this generalize, too? *)
      let f_body =
       map_unit_env_if
         (fun env trm ->
           on_type (is_orn env) env evd trm)
         (fun env trm ->
           let ihs = List.map (fun (_, (ih, _)) -> ih) index_args in
           let typ_args =
             if l.is_fwd then
               on_type unfold_args env evd trm
             else
               let typ = reduce_type env evd trm in
               let packer = get_arg 1 typ in
               if isLambda packer then (* TODO hack with vector A *)
                 let packer_body = unshift (snd (zoom_lambda_term env packer)) in
                 remove_index index_i (unfold_args packer_body)
               else
                 unfold_args packer
           in
           let app_pre_red = mkAppl (f, snoc trm typ_args) in
           (* TODO reinspect condition below, may be bad sometimes *)
           let app = reduce_constr_body env evd l is_orn index_i index_args app_pre_red in
           map_unit_if
             (fun trm ->
               isApp trm &&
               applies f trm &&
               List.exists (eq_constr (last_arg trm)) ihs)
             last_arg
             app)
         env_f_body_old
         f_body
      in map_backward (map_unit_if (applies existT) (get_arg 3)) l f_body
  in reconstruct_lambda_n env_f_body f_body (nb_rel env_f)

(* Map compose_c *)
let compose_cs evd npms ip p post_assums comp gs fs =
  let comp_cs =
    List.map2
      (fun c_g c_f -> { comp with g = (fst gs, c_g); f = (fst fs, c_f)})
      (snd gs)
      (snd fs)
  in List.map (compose_c evd npms ip p post_assums) comp_cs

(*
 * Compose two applications of an induction principle that are
 * structurally the same when one is an ornament.
 *
 * TODO clean
 *)
let rec compose_inductive evd idx_n post_assums assum_ind inner (comp : composition) =
  let l = comp.l in
  let (env_g, g) = comp.g in
  let (env_f, f) = comp.f in
  let f_app = deconstruct_eliminator env_f evd f in
  let g_app = deconstruct_eliminator env_g evd g in
  let npms = List.length g_app.pms in
  let (comp, indexer) =
    if l.is_fwd && comp.is_g && not l.is_indexer then
      (* Build the lifted indexer *)
      let indexer = Option.get l.orn.indexer in
      let (env_f_body, f_body) = zoom_lambda_term env_f f in
      let f_typ_args = on_type unfold_args env_f_body evd f_body in
      let index_args = snoc f_body f_typ_args in
      let indexer_unpacked_body = mkAppl (indexer, index_args) in
      let indexer_unpacked = reconstruct_lambda_n_skip env_f_body indexer_unpacked_body (offset env_f_body 2) (assum_ind - 1) in
      let env_packed = pop_rel_context (assum_ind + 2 - 1) env_f_body in
      let index_type = infer_type env_f_body evd (mkRel (2 + assum_ind - 1)) in
      let packer = infer_type env_packed evd (mkRel (1 + assum_ind - 1)) in
      let packed_type_b = shift index_type in
      let packed_type = mkLambda (Anonymous, packer, packed_type_b) in
      let indexer_body = elim_sigT index_type packer packed_type indexer_unpacked (mkRel (1 + List.length post_assums)) in
      let indexer = reconstruct_lambda env_packed indexer_body in
      let lifted_indexer = Some (make_constant idx_n) in
      let l = { l with lifted_indexer } in
      ({ comp with l }, Some indexer)
    else
      (comp, None)
  in
  let c_p = { comp with g = (env_g, g_app.p); f = (env_f, f_app.p) } in
  let p = compose_p evd npms post_assums inner c_p in
  let (cs, indexer) =
    if applies sigT_rect f then
      (* TODO factoring should handle *)
      (* bubble inside the sigT_rect (is this the best way?) *)
      let c = List.hd f_app.cs in
      let (env_c, c_body) = zoom_lambda_term env_f c in
      let c_cs = { comp with f = (env_c, c_body)} in
      let (c_comp, indexer) = compose_inductive evd idx_n post_assums assum_ind true c_cs in
      ([reconstruct_lambda_n env_c c_comp (nb_rel env_f)], indexer)
    else
      let gs =
        map_if
          (fun (env, cs) ->
            let (env_c, c) = zoom_lambda_term env (List.hd cs) in
            let c_app = deconstruct_eliminator env_c evd c in
            (env_c, c_app.cs))
          (applies sigT_rect g)
          (env_g, g_app.cs)
      in
      let fs = (env_f, f_app.cs) in
      (compose_cs evd npms g_app.elim p post_assums comp gs fs, indexer)
  in (apply_eliminator {f_app with p; cs}, indexer)

(*
 * Compose factors of an ornamented, but not yet reduced function
 *)
let rec compose_orn_factors evd (l : lifting) no_reduce assum_ind idx_n fs =
  let promote = l.orn.promote in
  let forget = l.orn.forget in
  let orn_indexer = Option.get l.orn.indexer in
  match fs with
  | Factor ((en, t), children) ->
     if List.length children > 0 then
       let post_assums = mk_n_rels (assum_ind - 1) in
       let child = List.hd (List.rev children) in
       let ((t_app, indexer), env, composed) = compose_orn_factors evd l no_reduce assum_ind idx_n child in
       let (e_body, t_body) = zoom_lambda_term en t in
       let body_uses f = is_or_applies f t_body in
       let uses f = (is_or_applies f t_app || body_uses f) && isApp t_app in
       let (env_promote, promote_exp) = zoom_lambda_term env (delta env promote) in
       let promote_inner = get_arg 3 promote_exp in
       let promote_inner_recons = reconstruct_lambda_n env_promote promote_inner (nb_rel env) in
       let t_app_typ = reduce_type env evd t_app in
       let t_app_args = unfold_args t_app_typ in
       let deindex = List.exists (applies orn_indexer) t_app_args in
       let promote_args = map_if (remove_index (Option.get l.orn.index_i)) deindex t_app_args in
       let promote_param = reduce_term env (mkAppl (promote_inner_recons, snoc (mkRel assum_ind) promote_args)) in
       let promotes = uses promote || uses promote_param in
       let forgets = uses forget in
       let is_indexer_inner =
         let body_is = is_or_applies sigT_rect t_body in
         let app_is = is_or_applies sigT_rect t_app in
         if app_is || body_is then
           let inner = get_arg 3 (if body_is then t_body else t_app) in
           let (_, inner_zoom) = zoom_lambda_term env inner in
           is_or_applies orn_indexer inner_zoom
         else
           false
       in
       let is_indexer = uses orn_indexer || is_indexer_inner in
       if promotes || forgets || is_indexer then
         let orn_f = if promotes then promote else if forgets then forget else orn_indexer in
         let is_g = applies orn_f t_body || is_or_applies promote_param t_body in
         let l = { l with is_indexer } in
         let g = (e_body, reduce_to_ind e_body t_body) in
         let f = (env, reduce_to_ind env t_app) in
         let comp = { l ; g ; f ; is_g } in
         if applies sigT_rect (snd g) && applies existT (snd f) then
           (* eliminate the existT [TODO move] *)
           let g_inner = get_arg 3 (snd g) in
           let cs_f = List.tl (List.tl (unfold_args (snd f))) in
           let inner = mkAppl (g_inner, cs_f) in
           let inner_factors = factor_term_dep (mkRel assum_ind) (fst f) evd inner in
           compose_orn_factors evd l true assum_ind idx_n inner_factors
         else if applies sigT_rect (snd f) && applies existT (snd g) then
           (* eliminate the existT [TODO move] *)
           let f_inner = get_arg 3 (snd f) in
           let (env_f_inner, f_inner_body) = zoom_lambda_term (fst f) f_inner in
           let c_g = last_arg (snd g) in
           let c_g_f = reconstruct_lambda (fst g) c_g in
           let c_f = reduce_term (fst g) (mkAppl (c_g_f, List.rev (List.tl (List.rev (unfold_args t_body))))) in
           let inner = mkAppl (shift_by 2 c_f, [f_inner_body]) in
           let inner_factors = factor_term_dep (mkRel assum_ind) env_f_inner evd inner in
           let ((t_app_inner, indexer_inner), env_inner, composed_inner) = compose_orn_factors evd l true assum_ind idx_n inner_factors in
           let app_lam = reconstruct_lambda_n_skip env_inner t_app_inner (offset env_inner 2) (assum_ind - 1) in
           let env_inner' = pop_rel_context (assum_ind + 2 - 1) env_inner in
           let f_p_old = get_arg 2 (snd f) in
           let (env_f_p, _) = zoom_lambda_term empty_env f_p_old in
           let f_p_body = unshift (reduce_type env_inner evd t_app_inner) in
           let f_p_new = reconstruct_lambda env_f_p (unshift_by (assum_ind - 1) f_p_body) in
           let f_args = unfold_args (snd f) in
           let args = reindex 3 app_lam (reindex 2 f_p_new f_args) in
           let app = mkAppl (sigT_rect, args) in
           ((app, indexer_inner), env_inner', composed_inner)
         else if applies sigT_rect (snd g) && is_indexer_inner then
           let inner = get_arg 3 (snd g) in
           let (env_inner, inner_body) = zoom_lambda_term (fst g) inner in
           let inner_factors = factor_term_dep (mkRel assum_ind) env_inner evd inner_body in
           let ((t_app_inner, indexer_inner), env_inner, composed_inner) = compose_orn_factors evd l true assum_ind idx_n inner_factors in
           let indexer_lam = reconstruct_lambda_n env_inner t_app_inner (offset env_inner 2) in
           let args = reindex 3 indexer_lam (unfold_args (snd g)) in
           let indexer = mkAppl (sigT_rect, args) in
           ((indexer, indexer_inner), pop_rel_context 2 env_inner, composed_inner)
         else
           let (app, indexer) = compose_inductive evd idx_n post_assums assum_ind false comp in
           ((app, indexer), env, true)
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
  let ((internalized, indexer), env, _) = compose_orn_factors evd l false assum_ind indexer_name factors in
  (reconstruct_lambda env internalized, indexer)
