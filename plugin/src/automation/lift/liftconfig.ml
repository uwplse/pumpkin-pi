open Lifting
open Constr
open Environ
open Stateutils
open Caching
open Apputils
open Promotion
open Sigmautils
open Indexing
open Zooming
open Reducers
open Funutils
open Envutils
open Specialization
open Debruijn
open Typehofs
open Ornerrors
open Hypotheses
open Declarations
open Utilities
open Desugarprod
open Names
open Equtils
open Convertibility
open Unificationutils
open Indutils
open Defutils
open Nameutils

(*
 * Lifting configuration: Includes the lifting, types, and cached rules
 * for optimizations, as well as interfaces to ask questions about
 * the configuration and some initialization code.
 *
 * This is where lifting constructors and projections live, since those
 * are configured ahead of time. Eventually, the bulk of lifting eliminators
 * may live here as well.
 *)

(* --- Datatype --- *)
       
(*
 * Lifting configuration, along with the types A and B,
 * rules for constructors and projections that are configurable by equivalence,
 * simplification rules, rules for lifting the identity function,
 * a cache for constants encountered as the algorithm traverses,
 * and a cache for the constructor rules that refolding determines.
 *)
type lift_config =
  {
    l : lifting;
    typs : types * types;
    elim_types : types * types;
    dep_elims : types * types;
    dep_constrs : types array * types array;
    constr_rules : types array * types array;
    proj_rules :
      ((constr * constr) list * (types * types) list) *
      ((constr * constr) list * (types * types) list);
    optimize_proj_id_rules :
      ((constr * (constr -> constr)) list) *
      ((constr * (constr -> constr)) list);
    id_etas : (constr * constr);
    cache : temporary_cache;
    opaques : temporary_cache
  }

(* --- Modifying the configuration --- *)

let reverse c =
  {
    c with
    l = flip_dir c.l;
    elim_types = reverse c.elim_types;
    dep_elims = reverse c.dep_elims;
    dep_constrs = reverse c.dep_constrs;
    proj_rules = reverse c.proj_rules;
    constr_rules = reverse c.constr_rules;
    optimize_proj_id_rules = reverse c.optimize_proj_id_rules;
    id_etas = reverse c.id_etas;
  }

let zoom c =
  match c.l.orn.kind with
  | Algebraic (indexer, off) ->
     let typs = map_tuple shift c.typs in
     { c with typs }
  | _ ->
     c

(* --- Convenient shorthand --- *)

let convertible env t1 t2 sigma =
  if equal t1 t2 then
    sigma, true
  else
    convertible env sigma t1 t2

let rev_tuple = Utilities.reverse

(* --- Recover the lifting --- *)

let get_lifting c = c.l
    
(* --- Caching --- *)

(*
 * Check opaqueness using either local or global cache
 *)
let is_opaque c trm =
  if is_locally_cached c.opaques trm then
    true
  else
    lookup_opaque (lift_to c.l, lift_back c.l, trm)
    
(*
 * Configurable caching of constants
 *
 * Note: The smart global cache works fine if we assume we always lift every
 * occurrence of the type. But once we allow for more configurable lifting,
 * for example with type-guided search, we will need a smarter smart cache
 * to still get this optimization.
 *)
let smart_cache c trm lifted =
  let l = c.l in
  if equal trm lifted then
    (* Save the fact that it does not change at all *)
    if Options.is_smart_cache () && not (is_opaque c trm) then
      save_lifting (lift_to l, lift_back l, trm) trm
    else
      cache_local c.cache trm trm
  else
    (* Save the lifted term locally *)
    cache_local c.cache trm lifted

(*
 * Check if something is in the local cache
*)
let is_cached c trm = is_locally_cached c.cache trm

(*
 * Lookup something from the local cache
 *)
let lookup_cache c trm = lookup_local_cache c.cache trm

(* --- Types A and B --- *)

(*
 * Initialize the types A and B
 *)
let initialize_types l env sigma =
  let sigma, promote_typ = reduce_type env sigma l.orn.promote in
  let (a_i_t, b_i_t) = promotion_type_to_types promote_typ in
  match l.orn.kind with
  | Algebraic _ ->
     let a_t = first_fun a_i_t in
     let env_pms = pop_rel_context 1 (zoom_env zoom_product_type env promote_typ) in
     let b_t = reconstruct_lambda env_pms (unshift b_i_t) in
     sigma, (a_t, b_t)
  | CurryRecord ->
     let a_t = first_fun a_i_t in
     let sigma, b_t = expand_eta env sigma (first_fun b_i_t) in
     sigma, (a_t, b_t)
  | SwapConstruct _ ->
     let a_t = first_fun a_i_t in
     let b_t = first_fun b_i_t in
     sigma, (a_t, b_t)
  | UnpackSigma ->
     let env_promote = zoom_env zoom_product_type env promote_typ in
     let env_typs = pop_rel_context 1 env_promote in
     let a_t = reconstruct_lambda env_typs a_i_t in
     let b_t = reconstruct_lambda env_typs (unshift b_i_t) in
     sigma, (a_t, b_t)

let get_types c = c.typs

(*
 * Optimization for is_from: things to try rather than trying unification,
 * if our type is in a format that is very easy to reason about without
 * unification.
 *)
let rec optimize_is_from c env typ sigma =
  let (a_typ, b_typ) = c.typs in
  let goal_typ = if c.l.is_fwd then a_typ else b_typ in
  if c.l.is_fwd then
    match c.l.orn.kind with
    | UnpackSigma ->
       (try
          let eq_sig_typ = dest_sigT typ in
          let sig_typ = dest_sigT eq_sig_typ.index_type in
          let rev_typ = sig_typ.packer in
          let sigma, rev_typ = expand_eta env sigma rev_typ in
          let sigma, typ_args_o = optimize_is_from (reverse c) env rev_typ sigma in
          if Option.has_some typ_args_o then
            let packer = eq_sig_typ.packer in
            let index = unshift (last_arg (zoom_term zoom_lambda_term env packer)) in
            let goal_typ = mkAppl (goal_typ, snoc index (Option.get typ_args_o)) in
            let sigma, goal_typ = reduce_term env sigma goal_typ in
            let goal_packer = (dest_sigT goal_typ).packer in
            if equal packer goal_packer then
              sigma, typ_args_o
            else
              sigma, None
          else
            sigma, None
        with _ ->
          sigma, None)
    | _ ->
       if is_or_applies goal_typ typ then
         sigma, Some (unfold_args typ)
       else
         sigma, None
  else
    match c.l.orn.kind with
    | SwapConstruct _ ->
       if is_or_applies goal_typ typ then
         sigma, Some (unfold_args typ)
       else
         sigma, None
    | UnpackSigma ->
       let goal_ind = first_fun (zoom_term zoom_lambda_term env goal_typ) in
       let sigma, typ = reduce_term env sigma typ in
       if is_or_applies goal_ind typ then
         sigma, Some (unfold_args typ)
       else
         sigma, None
    | _ ->
       sigma, None

(*
 * Determine whether a type is the type we are ornamenting from
 * That is, A when we are promoting, and B when we are forgetting
 * Return the arguments to the type if so
 *)
let is_from c env typ sigma =
  let sigma, args_o = optimize_is_from c env typ sigma in
  if Option.has_some args_o then
    sigma, args_o
  else
    let (a_typ, b_typ) = c.typs in
    let goal_typ = if c.l.is_fwd then a_typ else b_typ in
    e_is_from env goal_typ typ sigma

(*
 * Just get all of the unfolded arguments, skipping the check
 *)
let from_args c env trm sigma =
  Util.on_snd Option.get (is_from c env trm sigma)
                    
(* 
 * Determine whether a term has the type we are ornamenting from
 * Return the arguments to the type if so
 *)
let type_is_from c env trm sigma =
  try
    on_red_type
      reduce_term
      (fun env sigma typ -> is_from c env typ sigma)
      env
      sigma
      trm
  with _ ->
    sigma, None

(* 
 * Just return the arguments to from, assuming term has the right type,
 * skipping the check
 *)
let type_from_args c env trm sigma =
  on_red_type
    reduce_term
    (fun env sigma typ -> from_args c env typ sigma)
    env
    sigma
    trm

(* --- Identity and coherence (for definitional equality) --- *)

(* 
 * Initialize the rules for lifting projections
 * This is COHERENCE, but cached
 *)
let initialize_proj_rules c env sigma =
  let l = get_lifting c in
  let init c sigma =
    let l = { l with is_fwd = true } in
    let sigma, lift_typ = reduce_type env sigma (lift_to l) in
    let sigma, lift_typ_inv = reduce_type env sigma (lift_back l) in
    let env_a, b_typ = zoom_product_type env lift_typ in
    let env_b, a_typ = zoom_product_type env lift_typ_inv in
    let t = mkRel 1 in
    match l.orn.kind with
    | Algebraic (indexer, _) ->
       (* indexer <-> projT1, id(_typ) <- (rew ... in projT2(_typ) *)
       let sigma, b_sig = Util.on_snd dest_sigT (reduce_type env_b sigma t) in
       let projT1 = reconstruct_lambda env_b (project_index b_sig t) in
       let projT2 = reconstruct_lambda env_b (project_value b_sig t) in
       let rew_projT2 =
         let index_type = b_sig.index_type in
         let env_index = push_local (Anonymous, index_type) env_b in
         let env_eq =
           let eq_typ =
             let at_type = shift index_type in
             let trm1 = shift (project_index b_sig t) in
             let trm2 = mkRel 1 in
             apply_eq { at_type; trm1; trm2 }
           in push_local (Anonymous, eq_typ) env_index
         in
         let rew =
           let index_type = shift_by 2 index_type in
           let proj_index = shift_by 2 (project_index b_sig t) in
           let packer = shift_by 2 b_sig.packer in
           let b = shift_by 2 (project_value b_sig t) in
           let index = mkRel 2 in
           let eq = mkRel 1 in
           mkAppl (eq_rect, [index_type; proj_index; packer; b; index; eq])
         in reconstruct_lambda env_eq rew
       in
       let indexer =
         let args = mk_n_rels (nb_rel env_a) in
         reconstruct_lambda env_a (mkAppl (indexer, args))
       in
       let id = reconstruct_lambda env_a t in
       let rew_id =
         let index_type = b_sig.index_type in
         let env_index = push_local (Anonymous, index_type) env_a in
         let env_eq =
           let eq_typ =
             let at_type = shift index_type in
             let trm1 = mkAppl (indexer, shift_all (mk_n_rels (nb_rel env_a))) in
             let trm2 = mkRel 1 in
             apply_eq { at_type; trm1; trm2 }
           in push_local (Anonymous, eq_typ) env_index
         in reconstruct_lambda env_eq (shift_by 2 t)
       in
       let projT2_typ = reconstruct_lambda (pop_rel_context 1 env_b) (unshift b_sig.packer) in
       let env_id_typ = zoom_env zoom_lambda_term env projT2_typ in
       let id_typ = reconstruct_lambda env_id_typ a_typ in
       let a_rules = [(indexer, projT1)], [] in
       let b_rules = [(projT1, indexer); (projT2, id); (rew_projT2, rew_id)], [(projT2_typ, id_typ)] in
       sigma, (a_rules, b_rules)
    | UnpackSigma ->
       let sigma, a_typ = reduce_type env_a sigma t in
       let a_sig_sig = dest_sigT a_typ in
       let a_inner_typ = a_sig_sig.index_type in
       let a_sig = dest_sigT a_inner_typ in
       let sigma, (index_type, index) =
         let sigma, args = unpack_typ_args env_a a_typ sigma in
         sigma, (List.hd args, last args)
       in
       let p1 =
         let packer = a_sig.packer in
         let indexer = pack_existT { index_type; packer; index; unpacked = t } in
         reconstruct_lambda env_b indexer
       in
       let proj_bods = projections a_sig_sig t in
       let fwd_rules =
         (* projT1 -> pack, projT2 -> eq_refl *)
         let projT1, projT2 = map_tuple (reconstruct_lambda env_a) proj_bods in
         let p2 =
           let eq = apply_eq_refl { typ = index_type; trm = index } in
           reconstruct_lambda env_b eq
         in [(projT1, p1); (projT2, p2)], []
       in
       let sigma, bwd_rules =
         (* pack ... eq_refl -> pack ... (rew ... in projT2) *)
         (* in addition, opaque types so they match *)
         let p1_typ = reconstruct_lambda (pop_rel_context 2 env_b) (unshift_by 2 a_inner_typ) in
         let p2_typ = reconstruct_lambda (pop_rel_context 1 env_b) (unshift a_sig_sig.packer) in
         let sigma, projT1 =
           let packer = a_sig.packer in
           let index = mkRel 2 in
           let unpacked =
             let proj_index = project_index a_sig (fst proj_bods) in
             let b = project_value a_sig (fst proj_bods) in
             let eq = snd proj_bods in
             mkAppl (eq_rect, [index_type; proj_index; packer; b; index; eq])
           in
           let proj_bod = pack_existT { index_type; packer; index; unpacked } in
           sigma, reconstruct_lambda env_b proj_bod
         in sigma, ([(p1, projT1)], [(p1_typ, p1_typ); (p2_typ, p2_typ)])
       in sigma, (fwd_rules, bwd_rules)
    | CurryRecord ->
       (* accessors <-> projections *)
       let accessors =
         let (a_typ, _) = get_types c in
         let ((i, i_index), u) = destInd a_typ in
         let accessor_opts = Recordops.lookup_projections (i, i_index) in
         let args = mk_n_rels (nb_rel env_a) in
         try
           List.map (fun a_o -> reconstruct_lambda env_a (mkAppl ((mkConst (Option.get a_o)), args))) accessor_opts
         with _ ->
           []
       in
       let sigma, projections =
         let sigma, p_bodies = prod_projections_rec env_b t sigma in
         map_state (fun p -> ret (reconstruct_lambda env_b p)) p_bodies sigma
       in
       if List.length accessors = List.length projections then
         let sigma, fwd_rules =
           map2_state (fun p1 p2 -> ret (p1, p2)) accessors projections sigma
         in
         let bwd_rules = List.map rev_tuple fwd_rules in
         sigma, ((fwd_rules, []), (bwd_rules, []))
       else
         let _ =
           Feedback.msg_warning
             (Pp.str "Can't find record accessors; skipping an optimization")
         in sigma, (([], []), ([], []))
    | SwapConstruct _ ->
       (* no projections *)
       sigma, (([], []), ([], []))
  in
  let sigma, proj_rules = Util.on_snd (map_backward rev_tuple l) (init c sigma) in
  sigma, { c with proj_rules }

(*
 * Define what it means to lift the identity function, since we must
 * preserve definitional equalities.
 *)
let initialize_id_etas c cached env sigma =
  let l = get_lifting c in
  let sigma, ids =
    if Option.has_some cached then
      (* Use the cached id rules *)
      let (_, _, ids) = Option.get cached in
      sigma, ids
    else
      (* Determine the id rules and cache them for later *)
      let (a_typ, b_typ) = get_types c in
      let sigma, fwd_typ = reduce_type env sigma (lift_to l) in
      let sigma, bwd_typ = reduce_type env sigma (lift_back l) in
      let sigma, id_a =
        let env_id = zoom_env zoom_product_type env (if l.is_fwd then fwd_typ else bwd_typ) in
        let a = mkRel 1 in
        match l.orn.kind with
        | UnpackSigma ->
           (* eta for nested sigT *)
           let typ_args = shift_all (mk_n_rels (nb_rel env_id - 1)) in
           let sigma, typ = reduce_term env_id sigma (mkAppl (a_typ, typ_args)) in
           let s_eq_typ = dest_sigT typ in
           let index_type = s_eq_typ.index_type in
           let packer = s_eq_typ.packer in
           let s, unpacked = projections s_eq_typ a in
           let sigma, index =
             let sigma, typ = reduce_type env_id sigma s in
             let s_typ = dest_sigT typ in
             let index_type = s_typ.index_type in
             let packer = s_typ.packer in
             let index, unpacked = projections s_typ s in
             sigma, pack_existT { index_type; packer; index; unpacked}
           in
           let e = pack_existT {index_type; packer; index; unpacked} in
           sigma, reconstruct_lambda env_id e
        | Algebraic _ | CurryRecord | SwapConstruct _ ->
           (* identity *)
           sigma, reconstruct_lambda env_id a
      in
      let sigma, id_b =
        let env_id = zoom_env zoom_product_type env (if l.is_fwd then bwd_typ else fwd_typ) in
        let b = mkRel 1 in
        match l.orn.kind with
        | Algebraic _ ->
           (* eta for sigT *)
           let typ_args = shift_all (mk_n_rels (nb_rel env_id - 1)) in
           let sigma, typ = reduce_term env_id sigma (mkAppl (b_typ, typ_args)) in
           let s_typ = dest_sigT typ in
           let index_type = s_typ.index_type in
           let packer = s_typ.packer in
           let index, unpacked = projections s_typ b in
           let e = pack_existT {index_type; packer; index; unpacked} in
           sigma, reconstruct_lambda env_id e
        | CurryRecord ->
           (* eta for nested prod *)
           let typ_args = shift_all (mk_n_rels (nb_rel env_id - 1)) in
           let sigma, typ = reduce_term env_id sigma (mkAppl (b_typ, typ_args)) in
           let f = first_fun typ in
           let args = unfold_args typ in
           let sigma, typ_red = specialize_delta_f env_id f args sigma in
           sigma, reconstruct_lambda env_id (eta_prod_rec b typ_red)
        | UnpackSigma ->
           (* rewrite in pack (identity at eq_refl) *)
           let sigma, (env_eq, (eq, eq_typ), (b, b_typ)) =
             let push_anon t = push_local (Anonymous, t) in
             let env_sig = zoom_env zoom_lambda_term env a_typ in
             let sigma, (i_b_typ, b_typ, i_b) =
               let sig_eq = mkAppl (a_typ, mk_n_rels (nb_rel env_sig)) in
               let sigma, sig_eq = reduce_term env_sig sigma sig_eq in
               let sigma, typ_args = unpack_typ_args env_sig sig_eq sigma in
               sigma, (List.hd typ_args, List.hd (List.tl typ_args), last typ_args)
             in
             let env_i_b = push_anon i_b_typ env_sig in
             let env_b = push_anon (mkAppl (shift b_typ, [mkRel 1])) env_i_b in
             let eq_typ =
               let at_type = shift_by 2 i_b_typ in
               apply_eq { at_type; trm1 = mkRel 2; trm2 = shift_by 2 i_b }
             in
             let env_eq = push_anon eq_typ env_b in
             sigma, (env_eq, (mkRel 1, shift eq_typ), (mkRel 2, shift_by 3 b_typ))
           in
           let eq_typ_app = dest_eq eq_typ in
           let rewrite =
             let at_type = eq_typ_app.at_type in
             let trm1 = eq_typ_app.trm1 in
             let trm2 = eq_typ_app.trm2 in
             mkAppl (eq_rect, [at_type; trm1; b_typ; b; trm2; eq])
           in sigma, reconstruct_lambda_n env_eq rewrite (nb_rel env)
        | SwapConstruct _ ->
           (* identity *)
           sigma, reconstruct_lambda env_id b
      in
      let ids =
        let id_a_n, id_b_n =
          let promote = Constant.canonical (fst (destConst l.orn.promote)) in
          let (_, _, lab) = KerName.repr promote in
          let base_n = Label.to_id lab in
          (with_suffix base_n "id_eta_a", with_suffix base_n "id_eta_b")
        in
        let id_a, id_b = ((id_a_n, id_a), (id_b_n, id_b)) in
        try
          let id_a = define_term (fst id_a) sigma (snd id_a) true in
          let id_b = define_term (fst id_b) sigma (snd id_b) true in
          map_tuple Universes.constr_of_global (id_a, id_b)
        with _ ->
          snd id_a, snd id_b
      in
      save_id_eta (l.orn.promote, l.orn.forget) ids;
      sigma, ids
  in
  let ids = if l.is_fwd then ids else rev_tuple ids in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let id_etas = map_tuple (unwrap_definition env) ids in
  sigma, { c with id_etas }

(*
 * Get the map of projections for the type
 *)
let get_proj_map c = fst c.proj_rules

(* Unification can be slow, so sometimes we can do better ourselves *)
let optimize_is_proj c env trm proj_is sigma =
  let l = get_lifting c in
  match l.orn.kind with
  | UnpackSigma ->
     if l.is_fwd then
       let args = unfold_args trm in
       let isProjT1 = is_or_applies projT1 trm in
       let isProjT2 = is_or_applies projT2 trm in
       if List.length args = 3 && (isProjT1 || isProjT2) then
         let packed = last args in
         let sigma, typ_args_o = type_is_from c env packed sigma in
         if Option.has_some typ_args_o then
           let typ_args = Option.get typ_args_o in
           if isProjT1 then
             sigma, Some (0, snoc packed typ_args, trm)
           else
             sigma, Some (1, snoc packed typ_args, trm)
         else
           sigma, None
       else
         sigma, None
     else
       if is_or_applies existT trm then
         try
           let ex = dest_existT trm in
           let packer = ex.packer in
           let index = ex.index in
           let unpacked = ex.unpacked in
           let sigma, typ_args_o = is_from c env packer sigma in
           if Option.has_some typ_args_o then
             let typ_args = Option.get typ_args_o in
             sigma, Some (0, snoc unpacked (snoc index typ_args), trm)
           else
             sigma, None
         with _ ->
           sigma, None
       else
         sigma, None
  | _ ->
     sigma, None
                         
(* Check if a term applies a given projection *)
let check_is_proj c env trm proj_is sigma =
  let sigma, is_proj = optimize_is_proj c env trm proj_is sigma in
  if Option.has_some is_proj then
    sigma, is_proj
  else
    match kind trm with
    | App _ | Const _ -> (* this check is an optimization *)
       let f = first_fun trm in
       let rec check_is_proj_i i proj_is =
         match proj_is with
         | proj_i :: tl ->
            let proj_i_f = first_fun (zoom_term zoom_lambda_term env proj_i) in
            branch_state
              (convertible env proj_i_f) (* this check is an optimization *)
              (fun _ sigma ->
                try
                  let sigma, trm_eta = expand_eta env sigma trm in
                  let env_b, b = zoom_lambda_term env trm_eta in
                  let args = unfold_args b in
                  if List.length args = 0 then
                    check_is_proj_i (i + 1) tl sigma
                  else
                    (* attempt unification *)
                    let sigma, eargs = mk_n_evars (arity proj_i) env_b sigma in
                    let proj_app = mkAppl (proj_i, eargs) in
                    let sigma, resolved = unify_resolve_evars env_b b proj_app sigma in
                    if Option.has_some resolved then
                      let (_, proj_app) = Option.get resolved in
                      let args = unfold_args proj_app in
                      sigma, Some (i, args, trm_eta)
                    else
                      check_is_proj_i (i + 1) tl sigma
                with _ ->
                  check_is_proj_i (i + 1) tl sigma)
              (fun _ -> check_is_proj_i (i + 1) tl)
              f
         | _ ->
            ret None
       in check_is_proj_i 0 proj_is sigma
    | _ ->
       ret None sigma

(* Check if a term applies any projection *)
let is_proj c env trm sigma =
  let proj_term_rules, proj_type_rules = get_proj_map c in
  if List.length proj_term_rules = 0 then
    sigma, None
  else
    let rec check proj_maps sigma =
      match proj_maps with
      | proj_map :: tl ->
         let proj_terms = List.map fst proj_map in
         let sigma, to_proj_o = check_is_proj c env trm proj_terms sigma in
         if Option.has_some to_proj_o then
           let i, args, trm_eta = Option.get to_proj_o in
           let (_, proj) = List.nth proj_map i in
           sigma, Some (proj, args, trm_eta)
         else
           check tl sigma
      | _ ->
         sigma, None
    in check [proj_term_rules; proj_type_rules] sigma

(*
 * Get the lifted identity function
 *)
let get_lifted_id_eta c = snd c.id_etas

(*
 * Check if a term may apply the eta-expanded identity function,
 * but don't bother checking the type
 *)
let may_apply_id_eta c env trm =
  (* Heuristic for unification without slowdown *)
  if equal (zoom_term zoom_lambda_term env (fst c.id_etas)) (mkRel 1) then
    true
  else
    let l = get_lifting c in
    match l.orn.kind with
    | Algebraic _ ->
       is_or_applies existT trm || is_or_applies (lift_back l) trm
    | UnpackSigma ->
       if l.is_fwd then
         is_or_applies existT trm || is_or_applies (lift_back l) trm
       else
         true
    | CurryRecord ->
       is_or_applies pair trm || is_or_applies (lift_back l) trm
    | SwapConstruct _ ->
       false (* impossible state *)

(*
 * Check if a term applies the eta-expanded identity function
 *
 * We can think of this as part of COHERENCE, since the identity
 * function is, in a sense, also a projection. Long-term, it may make
 * sense to combine this with the COHERENCE rules.
 *)
let applies_id_eta c env trm sigma =
  let right_type trm = type_is_from c env trm sigma in
  if may_apply_id_eta c env trm then
    let sigma, typ_args_o = right_type trm in
    let opt_proj_map = snd c.optimize_proj_id_rules in
    (* Heuristic for unification again *)
    if Option.has_some typ_args_o then
      let typ_args = Option.get typ_args_o in
      if equal (zoom_term zoom_lambda_term env (fst c.id_etas)) (mkRel 1) then
        sigma, Some (snoc trm typ_args)
      else
        let l = get_lifting c in
        if is_or_applies (lift_back l) trm then
          sigma, Some (snoc trm typ_args)
        else
          match l.orn.kind with
          | Algebraic _ ->
             let proj_value = snd (last opt_proj_map) in
             let proj_arg = proj_value trm in
             sigma, Some (snoc proj_arg typ_args)
          | UnpackSigma ->
             if l.is_fwd then
               let projT1, proj_index = List.hd opt_proj_map in
               let projT2, proj_value = last opt_proj_map in
               let s, h_eq = proj_index trm, proj_value trm in
               let sigma, b_sig_eq =
                 let b_sig_eq_typ = mkAppl (fst (get_types c), typ_args) in
                 Util.on_snd dest_sigT (reduce_term env sigma b_sig_eq_typ)
               in
               let i_b, b =
                 if is_or_applies existT s then
                   proj_index s, proj_value s
                 else
                   projections (dest_sigT b_sig_eq.index_type) s
               in sigma, Some (List.append typ_args [i_b; b; h_eq])
             else
               if is_or_applies eq_rect trm || is_or_applies eq_ind trm || is_or_applies eq_rec trm then
                 let sigma, trm = expand_eta env sigma trm in
                 let eq_args = Array.of_list (unfold_args trm) in
                 let i_b_typ = eq_args.(0) in
                 let i_b = eq_args.(1) in
                 let b_typ  = eq_args.(2) in
                 let b = eq_args.(3) in
                 let i_b' = eq_args.(4) in
                 let h_eq = eq_args.(5) in
                 let packed =
                   let index_type =
                     let packer =
                       let unpacked = mkAppl (shift b_typ, [mkRel 1]) in
                       mkLambda (Anonymous, i_b_typ, unpacked)
                     in pack_sigT { index_type = i_b_typ; packer }
                   in
                   let packer =
                     let at_type = shift i_b_typ in
                     let trm1 = project_index (dest_sigT (shift index_type)) (mkRel 1) in
                     let trm2 = shift i_b' in
                     mkLambda (Anonymous, index_type, apply_eq { at_type; trm1; trm2 })
                   in
                   let index =
                     let index_type_app = dest_sigT index_type in
                     let packer = index_type_app.packer in
                     pack_existT { index_type = i_b_typ; packer; index = i_b; unpacked = b }
                   in pack_existT { index_type; packer; index; unpacked = h_eq }
                 in sigma, Some (snoc packed typ_args)
               else
                 let sigma, packed =
                   if isRel trm then
                     sigma, trm
                   else
                     let sigma, b_sig_eq =
                       let b_sig_eq_typ = mkAppl (fst (get_types c), typ_args) in
                       Util.on_snd dest_sigT (reduce_term env sigma b_sig_eq_typ)
                     in
                     let index_type = b_sig_eq.index_type in
                     let packer = b_sig_eq.packer in
                     let index, unpacked =
                       let b_sig = dest_sigT index_type in
                       let index_type = b_sig.index_type in
                       let index_index = last typ_args in
                       let index =
                         if is_or_applies projT1 index_index && is_or_applies projT2 trm then
                           last_arg trm
                         else
                           let packer = b_sig.packer in
                           let index = last typ_args in
                           let unpacked = trm in
                           pack_existT { index_type; packer; index; unpacked }
                       in
                       let unpacked = apply_eq_refl { typ = index_type; trm = index_index } in
                       index, unpacked
                     in sigma, pack_existT { index_type; packer; index; unpacked }
                 in
                 sigma, Some (snoc packed typ_args)
          | CurryRecord ->
             sigma, Some (snoc trm typ_args)
          | SwapConstruct _ ->
             sigma, None (* impossible state *)
    else
      sigma, None
  else
    sigma, None

(* --- Smart simplification (for termination and efficiency) --- *)

(*
 * Sometimes we can do better than Coq's reduction and simplify eagerly.
 * In particular, this happens when we lift to projections of the eta-expanded
 * identity functions, like (projT1 (existT _ n v)).
 * When subterms recursively refer to the original type, like in UnpackSigma,
 * this also helps ensure that the algorithm terminates by simplifying away
 * redundant terms.
 *)
let initialize_optimize_proj_id_rules c env sigma =
  let l = get_lifting c in
  let rules_fwd =
    match l.orn.kind with
    | Algebraic (_, _) ->
       let proj1_rule = (fun a -> (dest_existT a).index) in
       let proj2_rule = (fun a -> (dest_existT a).unpacked) in
       [(projT1, proj1_rule); (projT2, proj2_rule)]
    | CurryRecord ->
       let proj1_rule = (fun a -> (dest_pair a).Produtils.trm1) in
       let proj2_rule = (fun a -> (dest_pair a).Produtils.trm2) in
       [(Desugarprod.fst_elim (), proj1_rule); (Desugarprod.snd_elim (), proj2_rule)]
    | SwapConstruct _ | UnpackSigma ->
       []
  in
  let rules_bwd =
    match l.orn.kind with
    | UnpackSigma ->
       (* not the best we can do *)
       let proj1_rule = (fun a -> (dest_existT a).index) in
       let proj2_rule = (fun a -> (dest_existT a).unpacked) in
       [(projT1, proj1_rule); (projT2, proj2_rule)]
    | SwapConstruct _ | Algebraic (_, _) | CurryRecord ->
       []
  in
  let optimize_proj_id_rules =
    if l.is_fwd then
      (rules_fwd, rules_bwd)
    else
      (rules_bwd, rules_fwd)
  in sigma, { c with optimize_proj_id_rules }

(*
 * Determine if we can probably be smarter than Coq and simplify earlier
 * If yes, return how
 * Otherwise, return None
 *
 * Sometimes, we need this for termination when lifted terms can be
 * self-referrential
 *)
let can_reduce_now c env trm =
  match kind trm with
  | App (_, args) when Array.length args > 0 ->
     let proj_packed_map = fst c.optimize_proj_id_rules in
     let optimize_proj_packed_o =
       try
         Some
           (List.find
              (fun (pr, _) -> is_or_applies pr trm)
              proj_packed_map)
       with _ ->
         None
     in
     if Option.has_some optimize_proj_packed_o then
       let _, reduce = Option.get optimize_proj_packed_o in
       Some (fun _ sigma trm -> sigma, reduce trm)
     else
       None
  | _ ->
     None

(*
 * Custom reduction function for coherence,
 * for efficiency and to ensure termination. For example, this may
 * simplify projections of existentials.
 *)
let reduce_coh c env sigma trm =
  let l = get_lifting c in
  let rec reduce_arg c env sigma arg =
    let sigma, arg = reduce_term env sigma arg in
    let how_reduce_o = can_reduce_now c env arg in
    if Option.has_some how_reduce_o then
      let proj_a = Option.get how_reduce_o in
      let arg_inner = last_arg arg in
      let sigma, arg_inner = reduce_arg c env sigma arg_inner in
      if may_apply_id_eta (reverse c) env arg_inner then
        let sigma, projected = proj_a env sigma arg_inner in
        reduce_arg c env sigma projected
      else
        sigma, arg
    else if isApp arg then
      let f = first_fun arg in
      let args = unfold_args arg in
      let sigma, args =
        map_state
          (fun trm sigma ->
            reduce_arg c env sigma trm)
          args
          sigma
      in sigma, mkAppl (f, args)
    else
      sigma, arg
  in
  match l.orn.kind with
  | UnpackSigma when not l.is_fwd ->
     let sigma, trm = reduce_term env sigma trm in
     if is_or_applies existT trm then
       let ex = dest_existT trm in
       let sigma, index = reduce_arg c env sigma ex.index in
       let sigma, unpacked = reduce_arg c env sigma ex.unpacked in
       sigma, pack_existT { ex with index; unpacked }
     else
       reduce_arg c env sigma trm
  | _ ->
     reduce_arg c env sigma trm

(*
 * Custom reduction function for lifted eta-expanded identity,
 * for efficiency and to ensure termination. For example, this may
 * simplify projections of existentials.
 *)
let reduce_lifted_id c env sigma trm =
  let l = get_lifting c in
  let sigma, trm = reduce_term env sigma trm in
  match c.l.orn.kind with
  | Algebraic _ when l.is_fwd ->
     let ex = dest_existT trm in
     let sigma, index = reduce_coh c env sigma ex.index in
     let sigma, unpacked = reduce_coh c env sigma ex.unpacked in
     sigma, pack_existT { ex with index; unpacked }
  | UnpackSigma ->
     if l.is_fwd then
       let args = unfold_args trm in
       if is_or_applies eq_refl (last args) then
         sigma, List.nth args 3
       else
         sigma, trm
     else
       let ex = dest_existT trm in
       let sigma, index = reduce_coh c env sigma ex.index in
       let sigma, unpacked = reduce_coh c env sigma ex.unpacked in
       sigma, pack_existT { ex with index; unpacked }
  | _ ->
     sigma, trm

(* --- Constructors --- *)

(*
 * Utility function: Map over the constructors of an inductive type 
 *)
let map_constrs f env typ sigma =
  let ((i, i_index), u) = destInd typ in
  let mutind_body = lookup_mind i env in
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = ind_bodies.(i_index) in
  map_state_array
    (f env)
    (Array.mapi
       (fun c_index _ -> mkConstructU (((i, i_index), c_index + 1), u))
       ind_body.mind_consnames)
    sigma

(*
 * Utility function: Expand all constructors of an inductive type
 *)
let eta_constrs =
  map_constrs (fun env constr sigma -> expand_eta env sigma constr)

(*
 * Initialize DepConstr for each type
 *)
let initialize_dep_constrs c cached env sigma =
  let l = c.l in
  let sigma, constrs =
    if Option.has_some cached then
      (* Use the cached DepConstr rules *)
      let (constrs, _, _) = Option.get cached in
      sigma, constrs
    else
      let a_typ, b_typ = c.typs in
      let sigma, a_constrs =
        match l.orn.kind with
        | Algebraic _ | CurryRecord | SwapConstruct _ ->
           eta_constrs env a_typ sigma
        | UnpackSigma ->
           let b_typ_inner = first_fun (zoom_term zoom_lambda_term env b_typ) in
           let sigma, constrs = eta_constrs env b_typ_inner sigma in
           let c = if l.is_fwd then reverse c else c in
           map_state_array
             (fun constr sigma ->
               let env_c_b, c_body = zoom_lambda_term env constr in
               let sigma, id_args_o = applies_id_eta c env_c_b c_body sigma in
               let lifted_id = get_lifted_id_eta c in
               let sigma, id_app = reduce_lifted_id c env_c_b sigma (mkAppl (lifted_id, Option.get id_args_o)) in
               sigma, reconstruct_lambda_n env_c_b id_app (nb_rel env))
             constrs
             sigma
      in
      let sigma, b_constrs =
        match l.orn.kind with
        | Algebraic _ ->
           let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_typ)).packer in
           let b_typ_inner = first_fun b_typ_packed in
           map_constrs
             (fun env constr sigma ->
               let sigma, constr_exp = expand_eta env sigma constr in
               let (env_c_b, c_body) = zoom_lambda_term env constr_exp in
               let c_body = reduce_stateless reduce_term env_c_b sigma c_body in
               let sigma, packed = pack env_c_b l c_body sigma in
               sigma, reconstruct_lambda_n env_c_b packed (nb_rel env))
             env
             b_typ_inner
             sigma
        | CurryRecord ->
           let a_constr = a_constrs.(0) in
           let (env_c_b, c_body) = zoom_lambda_term env a_constr in
           let l = { l with is_fwd = true } in
           let sigma, typ_args = type_from_args { c with l } env_c_b c_body sigma in
           let sigma, app = lift env_c_b l c_body typ_args sigma in
           let sigma, app = reduce_nf env sigma app in
           let constr = reconstruct_lambda_n env_c_b app (nb_rel env) in
           sigma, Array.make 1 constr
        | SwapConstruct _ ->
           eta_constrs env b_typ sigma
        | UnpackSigma ->
           eta_constrs env (first_fun (zoom_term zoom_lambda_term env b_typ)) sigma
      in
      let dep_constrs =
        let c_a_n, c_b_n =
          let promote = Constant.canonical (fst (destConst l.orn.promote)) in
          let (_, _, lab) = KerName.repr promote in
          let base_n = Label.to_id lab in
          (with_suffix base_n "dep_constr_a", with_suffix base_n "dep_constr_b")
        in
        let a_constrs, b_constrs = ((c_a_n, a_constrs), (c_b_n, b_constrs)) in
        try
          let a_constrs =
            Array.mapi
              (fun i c ->
                let n = with_suffix (fst a_constrs) (string_of_int i) in
                define_term n sigma c true)
              (snd a_constrs)
          in
          let b_constrs =
            Array.mapi
              (fun i c ->
                let n = with_suffix (fst b_constrs) (string_of_int i) in
                define_term n sigma c true)
              (snd b_constrs)
          in
          map_tuple (Array.map Universes.constr_of_global) (a_constrs, b_constrs)
        with _ ->
          snd a_constrs, snd b_constrs
      in
      save_dep_constrs (l.orn.promote, l.orn.forget) dep_constrs;
      sigma, dep_constrs
  in
  let constrs = if l.is_fwd then constrs else rev_tuple constrs in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let dep_constrs = map_tuple (Array.map (unwrap_definition env)) constrs in
  sigma, { c with dep_constrs }

(*
 * For packing constructor aguments: Pack, but only if it's B
 *)
let pack_to_typ c env unpacked sigma =
  let b_typ = (if c.l.is_fwd then snd else fst) c.elim_types in
  let l = c.l in
  if on_red_type_default (ignore_env (is_or_applies b_typ)) env sigma unpacked then
    match l.orn.kind with
    | Algebraic (_, off) ->
       pack env l unpacked sigma
    | _ ->
       raise NotAlgebraic
  else
    sigma, unpacked
             
(*
 * NORMALIZE (the result of this is cached)
 *)
let lift_constr env sigma c trm =
  let l = c.l in
  let sigma, typ_args = type_from_args c env trm sigma in
  let sigma, app = lift env l trm typ_args sigma in
  match l.orn.kind with
  | Algebraic _ ->
     let pack_args (sigma, args) = map_state (pack_to_typ c env) args sigma in
     let args = unfold_args (map_backward last_arg l trm) in
     let sigma, packed_args = map_backward pack_args l (sigma, args) in
     let sigma, rec_args = filter_state (fun tr sigma -> let sigma, o = type_is_from c env tr sigma in sigma, Option.has_some o) packed_args sigma in
     if List.length rec_args = 0 then
       (* base case - don't bother refolding *)
       reduce_nf env sigma app
     else
       (* inductive case - refold *)
       refold l env (lift_to l) app rec_args sigma
  | SwapConstruct _ ->
     let args = unfold_args trm in
     let sigma, rec_args = filter_state (fun tr sigma -> let sigma, o = type_is_from c env tr sigma in sigma, Option.has_some o) args sigma in
     if List.length rec_args = 0 then
       (* base case - don't bother refolding *)
       reduce_nf env sigma app
     else
       (* inductive case - refold *)
       refold l env (lift_to l) app rec_args sigma
  | UnpackSigma ->
     (* specialized refolding for a cleaner and more efficient result *)
     let delta app = specialize_delta_f env (first_fun app) (unfold_args app) in
     let sigma, app_red = reduce_term env sigma app in
     (* delta-reduce unpack_generic(_inv) (no custom equivalence support yet) *)
     let sigma, app_red = delta app_red sigma in
     let sigma, app_red = delta app_red sigma in
     let sigma, app_red = reduce_term env sigma app_red in
     if l.is_fwd then
       (* don't bother modifying; this never fires since ID rules always do, anyways *)
       sigma, app_red
     else
       let ex_eq = dest_existT app_red in
       let ex = dest_existT ex_eq.index in
       let f' = first_fun ex.unpacked in
       let args' = unfold_args ex.unpacked in
       let sigma, args'' =
         map_state
           (fun a sigma ->
             let sigma_right, is_from_o = type_is_from c env a sigma in
             if Option.has_some is_from_o then
               let typ_args = Option.get is_from_o in
               let sigma, a' = lift env (get_lifting (reverse c)) a typ_args sigma_right in
               let sigma, a'_red = delta a' sigma in
               let sigma, a'_red = delta a'_red sigma in
               reduce_term env sigma a'_red
             else
               sigma, a)
           args'
           sigma
       in
       if List.for_all2 equal args' args'' then
         (* base case *)
         sigma, app_red
       else
         (* inductive case (in future, need to tweak for vector to list case) *)
         let unpacked = mkAppl (f', args'') in
         let index = pack_existT { ex with unpacked } in
         sigma, pack_existT { ex_eq with index }
  | CurryRecord ->
     (* no inductive cases, so don't try to refold *)
     reduce_nf env sigma app

(*
 * Wrapper around NORMALIZE
 *)
let initialize_constr_rule c env constr sigma =
  let sigma, constr_exp = expand_eta env sigma constr in
  let (env_c_b, c_body) = zoom_lambda_term env constr_exp in
  let c_body = reduce_stateless reduce_term env_c_b sigma c_body in
  let sigma, lifted_body = lift_constr env_c_b sigma c c_body in
  sigma, reconstruct_lambda_n env_c_b lifted_body (nb_rel env)

(*
 * Run NORMALIZE for all constructors, so we can cache the result
 *)
let initialize_constr_rules c env sigma =
  let (fwd_constrs, bwd_constrs) = c.dep_constrs in
  let sigma, lifted_fwd_constrs =
    map_state_array (initialize_constr_rule c env) fwd_constrs sigma
  in
  let sigma, lifted_bwd_constrs =
    map_state_array (initialize_constr_rule (reverse c) env) bwd_constrs sigma
  in
  let constr_rules = (lifted_fwd_constrs, lifted_bwd_constrs) in
  sigma, { c with constr_rules }
           
(*
 * Get the cached unlifted and lifted constructors
 *)
let get_constrs c = fst c.dep_constrs
let get_lifted_constrs c = fst c.constr_rules

(*
 * Check if a term applies the eta-expanded constructor
 * Part of LIFT-CONSTR, basically a speedup over unification rather than
 * using the constructor rules and unification directly
 *)
let applies_constr_eta c env trm sigma =
  let l = get_lifting c in
  let constrs = get_constrs c in
    let is_inductive_constr project trm opaque =
    (* Helper function, faster than unifying with constructor rules *)
    try
      let unpacked = project trm in
      let f = first_fun unpacked in
      let args = unfold_args unpacked in
      match kind f with
      | Construct ((_, i), _) when i <= Array.length constrs ->
         let constr = constrs.(i - 1) in
         let f' = first_fun (project (zoom_term zoom_lambda_term env constr)) in
         if equal f f' && List.length args = arity constr then
           sigma, Some (i - 1, args, opaque)
         else
           sigma, None
      | _ ->
         sigma, None
    with _ ->
      sigma, None
  in
  if may_apply_id_eta c env trm then
    match l.orn.kind with
    | Algebraic _ ->
       is_inductive_constr (if l.is_fwd then id else last_arg) trm false
    | SwapConstruct _ ->
       is_inductive_constr id trm false
    | CurryRecord ->
       if l.is_fwd then
         is_inductive_constr id trm false
       else
         if applies (lift_back l) trm then
           sigma, None
         else
           (* we treat any pair of the right type as a constructor *)
           let sigma_right, args_opt = type_is_from c env trm sigma in
           if Option.has_some args_opt then
             let sigma = sigma_right in
             let constr = constrs.(0) in
             let pms = Option.get args_opt in
             let npm = List.length pms in
             let args = pair_projections_eta_rec_n trm (arity constr - npm) in
             sigma, Some (0, List.append pms args, false)
           else
             sigma, None
    | UnpackSigma ->
       if l.is_fwd then
         (* ID rules always take care of this, so no need *)
         sigma, None
       else
         is_inductive_constr id trm true
  else
    sigma, None

(*
 * Custom simplification for applications of constructors
 *)
let reduce_constr_app c env sigma trm =
  let l = get_lifting c in
  let sigma, trm = reduce_term env sigma trm in
  match l.orn.kind with
  | UnpackSigma when not l.is_fwd ->
     let ex = dest_existT trm in
     let sigma, index = reduce_coh c env sigma ex.index in
     let sigma, unpacked = reduce_coh c env sigma ex.unpacked in
     sigma, pack_existT { ex with index; unpacked }
  | _ ->
     sigma, trm

(* --- Eliminators --- *)

(*
 * Initialize the type of the eliminator
 *)
let initialize_elim_types c env sigma =
  let l = get_lifting c in
  let (a_t, b_t) = get_types c in
  let b_t =
    match l.orn.kind with
    | Algebraic _ ->
       let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_t)).packer in
       first_fun b_typ_packed
    | CurryRecord ->
       prod
    | _ ->
       first_fun (zoom_term zoom_lambda_term env b_t)
  in
  let a_t =
    match l.orn.kind with
    | UnpackSigma ->
       b_t
    | _ ->
       a_t
  in
  let fwd_elim_typ = directional l a_t b_t in
  let bwd_elim_typ = directional l b_t a_t in
  let elim_types = (fwd_elim_typ, bwd_elim_typ) in
  sigma, { c with elim_types }

let get_elim_type c = fst (c.elim_types)

(*
 * Initialize dep_elims
 *)
let initialize_dep_elims c cached env sigma =
  let sigma, elims =
    if Option.has_some cached then
      (* Use the cached DepElim rules *)
      let (_, elims, _) = Option.get cached in
      sigma, elims
    else
      (* Determine DepElim and cache if needed *)
      sigma, c.dep_elims
  in sigma, { c with dep_elims = elims }

(*
 * Check if the term applies the eliminator
 * If so return the eliminator application, parameters, and the arity
 * of the motive (the number of "final arguments" after inducting over
 * the term)
 *)
let applies_elim c env trm sigma =
  let l = get_lifting c in
  match kind (first_fun trm) with
  | Const (k, u) ->
     let maybe_ind = inductive_of_elim env (k, u) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       let elim_typ = get_elim_type c in
       if equal (mkInd (ind, 0)) elim_typ then
         let sigma, trm_eta = expand_eta env sigma trm in
         let env_elim, trm_b = zoom_lambda_term env trm_eta in
         let sigma, trm_elim = deconstruct_eliminator env_elim sigma trm_b in
         let sigma, elim_app_o =
           match l.orn.kind with
           | Algebraic _ | SwapConstruct _ | UnpackSigma ->
              let sigma, elim_typ_eta = expand_eta env sigma elim_typ in
              let nargs = (arity elim_typ_eta) - (List.length trm_elim.pms) + 1 in
              sigma, Some (trm_elim, trm_elim.pms, nargs)
           | CurryRecord ->
              let nargs = 1 in
              if l.is_fwd then
                let typ_f = first_fun (zoom_term zoom_lambda_term env_elim (snd (get_types c))) in
                let sigma, to_typ_prod = specialize_delta_f env_elim typ_f trm_elim.pms sigma in
                let to_elim = dest_prod to_typ_prod in
                let pms = [to_elim.Produtils.typ1; to_elim.Produtils.typ2] in
                sigma, Some (trm_elim, pms, nargs)
              else
                let sigma, is_from = type_is_from c env_elim (List.hd trm_elim.final_args) sigma in
                if Option.has_some is_from then
                  sigma, Some (trm_elim, Option.get is_from, nargs)
                else
                  sigma, None
         in
         if Option.has_some elim_app_o then
           let trm_elim, pms, nargs = Option.get elim_app_o in
           let opaque = (l.orn.kind = UnpackSigma) in
           if new_rels2 env_elim env > 0 then
             sigma, Some (Some trm_eta, trm_elim, pms, nargs, opaque)
           else
             sigma, Some (None, trm_elim, pms, nargs, opaque)
         else
           sigma, None
       else
         sigma, None
     else
       sigma, None
  | _ ->
     sigma, None

(* --- Initialization --- *)

(* Initialize the lift_config *)
let initialize_lift_config env l ignores sigma =
  let sigma, typs = initialize_types l env sigma in
  let cache = initialize_local_cache () in
  let opaques = initialize_local_cache () in
  List.iter (fun opaque -> cache_local opaques opaque opaque) ignores;
  let c =
    {
      l;
      typs;
      elim_types = (mkRel 1, mkRel 1);
      dep_elims = (mkRel 1, mkRel 1);
      dep_constrs = Array.make 0 (mkRel 1), Array.make 0 (mkRel 1);
      constr_rules = Array.make 0 (mkRel 1), Array.make 0 (mkRel 1);
      proj_rules = ([], []), ([], []);
      optimize_proj_id_rules = [], [];
      id_etas = (mkRel 1, mkRel 1);
      cache;
      opaques
    }
  in
  let cached = lookup_config (l.orn.promote, l.orn.forget) in
  let sigma, c = initialize_proj_rules c env sigma in
  let sigma, c = initialize_optimize_proj_id_rules c env sigma in
  let sigma, c = initialize_id_etas c cached env sigma in
  let sigma, c = initialize_elim_types c env sigma in
  let sigma, c = initialize_dep_elims c cached env sigma in
  let sigma, c = initialize_dep_constrs c cached env sigma in
  initialize_constr_rules c env sigma

