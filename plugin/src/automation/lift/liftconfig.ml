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
open Hofs
open Contextutils

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
 * simplification rules, definitional equality rules,
 * a cache for constants encountered as the algorithm traverses,
 * and a cache for the constructor rules that refolding determines.
 *)
type lift_config =
  {
    l : lifting;
    typs : types * types;
    elim_types : types * types;
    dep_elims : constr * constr;
    dep_constrs : constr array * constr array;
    proj_rules :
      ((constr * constr) list * (types * types) list) *
      ((constr * constr) list * (types * types) list);
    optimize_proj_id_rules :
      ((constr * (constr -> constr)) list) *
      ((constr * (constr -> constr)) list);
    etas : (constr * constr);
    iotas : (constr array * constr array);
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
    optimize_proj_id_rules = reverse c.optimize_proj_id_rules;
    etas = reverse c.etas;
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
    if equal trm (snd c.dep_elims) then
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
  | Custom typs ->
     sigma, typs

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
    | Algebraic _ ->
       (try
          let sig_typ = dest_sigT typ in
          let b_typ = sig_typ.packer in
          let unpacked_typ = first_fun (zoom_term zoom_lambda_term env b_typ) in
          let elim_typ = fst c.elim_types in
          if equal unpacked_typ elim_typ then
            let b = zoom_term zoom_lambda_term env b_typ in
            let args = unshift_all (deindex c.l (unfold_args b)) in
            let sigma, goal_app = reduce_term env sigma (mkAppl (goal_typ, args)) in
            let index_type = sig_typ.index_type in
            if equal index_type (dest_sigT goal_app).index_type then
              sigma, Some args
            else
              sigma, None
          else
            sigma, None
        with _ ->
          sigma, None)
    | SwapConstruct _ | Custom _ ->
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
    let sigma, typ = reduce_type env sigma trm in
    is_from c env typ sigma
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

(* --- Eta, iota, and coherence (for definitional equality) --- *)

(* 
 * Initialize the rules for lifting projections
 * This is COHERENCE, but cached
 *
 * A lot of this will likely go into Eta or Iota soon, at least what is
 * not here just for optimizaiton pruposes
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
    | SwapConstruct _ | Custom _ ->
       (* no projections *)
       sigma, (([], []), ([], []))
  in
  let sigma, proj_rules = Util.on_snd (map_backward rev_tuple l) (init c sigma) in
  sigma, { c with proj_rules }

(*
 * Define what it means to lift the identity function, since we must
 * preserve definitional equalities.
 *)
let initialize_etas c cached env sigma =
  let l = get_lifting c in
  let sigma, etas =
    if Option.has_some cached then
      (* Use the cached eta rules *)
      let (_, _, etas, _) = Option.get cached in
      sigma, etas
    else
      (* Determine the eta rules and cache them for later *)
      let (a_typ, b_typ) = get_types c in
      let sigma, fwd_typ = reduce_type env sigma (lift_to l) in
      let sigma, bwd_typ = reduce_type env sigma (lift_back l) in
      let sigma, eta_a =
        let env_eta = zoom_env zoom_product_type env (if l.is_fwd then fwd_typ else bwd_typ) in
        let a = mkRel 1 in
        match l.orn.kind with
        | UnpackSigma ->
           (* eta for nested sigT *)
           let typ_args = shift_all (mk_n_rels (nb_rel env_eta - 1)) in
           let sigma, typ = reduce_term env_eta sigma (mkAppl (a_typ, typ_args)) in
           let s_eq_typ = dest_sigT typ in
           let index_type = s_eq_typ.index_type in
           let packer = s_eq_typ.packer in
           let s, unpacked = projections s_eq_typ a in
           let sigma, index =
             let sigma, typ = reduce_type env_eta sigma s in
             let s_typ = dest_sigT typ in
             let index_type = s_typ.index_type in
             let packer = s_typ.packer in
             let index, unpacked = projections s_typ s in
             sigma, pack_existT { index_type; packer; index; unpacked}
           in
           let e = pack_existT {index_type; packer; index; unpacked} in
           sigma, reconstruct_lambda env_eta e
        | Algebraic _ | CurryRecord | SwapConstruct _ | Custom _ ->
           (* identity *)
           sigma, reconstruct_lambda env_eta a
      in
      let sigma, eta_b =
        let env_eta = zoom_env zoom_product_type env (if l.is_fwd then bwd_typ else fwd_typ) in
        let b = mkRel 1 in
        match l.orn.kind with
        | Algebraic _ ->
           (* eta for sigT *)
           let typ_args = shift_all (mk_n_rels (nb_rel env_eta - 1)) in
           let sigma, typ = reduce_term env_eta sigma (mkAppl (b_typ, typ_args)) in
           let s_typ = dest_sigT typ in
           let index_type = s_typ.index_type in
           let packer = s_typ.packer in
           let index, unpacked = projections s_typ b in
           let e = pack_existT {index_type; packer; index; unpacked} in
           sigma, reconstruct_lambda env_eta e
        | CurryRecord ->
           (* eta for nested prod *)
           let typ_args = shift_all (mk_n_rels (nb_rel env_eta - 1)) in
           let sigma, typ = reduce_term env_eta sigma (mkAppl (b_typ, typ_args)) in
           let f = first_fun typ in
           let args = unfold_args typ in
           let sigma, typ_red = specialize_delta_f env_eta f args sigma in
           sigma, reconstruct_lambda env_eta (eta_prod_rec b typ_red)
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
        | SwapConstruct _ | Custom _ ->
           (* identity *)
           sigma, reconstruct_lambda env_eta b
      in
      let etas =
        let eta_a_n, eta_b_n =
          let promote = Constant.canonical (fst (destConst l.orn.promote)) in
          let (_, lab) = KerName.repr promote in
          let base_n = Label.to_id lab in
          (with_suffix base_n "eta_a", with_suffix base_n "eta_b")
        in
        let eta_a, eta_b = ((eta_a_n, eta_a), (eta_b_n, eta_b)) in
        try
          let eta_a = define_term (fst eta_a) sigma (snd eta_a) in
          let eta_b = define_term (fst eta_b) sigma (snd eta_b) in
          map_tuple UnivGen.constr_of_monomorphic_global (eta_a, eta_b)
        with _ ->
          snd eta_a, snd eta_b
      in save_eta (l.orn.promote, l.orn.forget) etas; sigma, etas
  in
  let etas = if l.is_fwd then etas else rev_tuple etas in
  let env = Global.env () in
  let etas = map_tuple (unwrap_definition env) etas in
  sigma, { c with etas }

(*
 * Define what it means to lift equality proofs.
 * TODO implement trivial useless iotas for search procedures 
 *)
let initialize_iotas c cached env sigma =
  let l = get_lifting c in
  let sigma, iotas =
    if Option.has_some cached then
      (* Use the cached rew rules *)
      let (_, _, _, iotas) = Option.get cached in
      sigma, iotas
    else
      (* Determine the rew rules and cache them for later *)
      let sigma, fwd_typ = reduce_type env sigma (lift_to l) in
      let sigma, bwd_typ = reduce_type env sigma (lift_back l) in
      let sigma, iota_a =
        map_state_array
          (fun _ sigma -> (* TODO args should be case of dep_elim later *)
            let env_iota = zoom_env zoom_product_type env (if l.is_fwd then fwd_typ else bwd_typ) in
            let a = mkRel 1 in
            let sigma, a_typ = reduce_type env_iota sigma a in
            let iota_a_bod = apply_eq_refl { typ = a_typ; trm = mkRel 1 } in
            sigma, reconstruct_lambda_n env_iota iota_a_bod (nb_rel env))
          ((if l.is_fwd then fst else snd) c.dep_constrs)
          sigma
      in
      let sigma, iota_b =
        map_state_array
          (fun _ sigma -> (* TODO args should be case of elim later *)
            let env_iota = zoom_env zoom_product_type env (if l.is_fwd then bwd_typ else fwd_typ) in
            let b = mkRel 1 in
            let sigma, b_typ = reduce_type env_iota sigma b in
            let iota_b_bod = apply_eq_refl { typ = b_typ; trm = mkRel 1 } in
            sigma, reconstruct_lambda_n env_iota iota_b_bod (nb_rel env))
          ((if l.is_fwd then snd else fst) c.dep_constrs)
          sigma
      in
      let iotas =
        let iota_a_n, iota_b_n =
          let promote = Constant.canonical (fst (destConst l.orn.promote)) in
          let (_, lab) = KerName.repr promote in
          let base_n = Label.to_id lab in
          (with_suffix base_n "iota_a", with_suffix base_n "iota_b")
        in
        let iota_a, iota_b = ((iota_a_n, iota_a), (iota_b_n, iota_b)) in
        let iota_as =
          Array.mapi
            (fun i rew ->
              let n = with_suffix (fst iota_a) (string_of_int i) in
              define_term n sigma rew)
            (snd iota_a)
        in
        let iota_bs =
          Array.mapi
            (fun i rew ->
              let n = with_suffix (fst iota_b) (string_of_int i) in
              define_term n sigma rew)
            (snd iota_b)
        in map_tuple (Array.map UnivGen.constr_of_monomorphic_global) (iota_as, iota_bs)
      in save_iota (l.orn.promote, l.orn.forget) iotas; sigma, iotas
  in
  let iotas = if l.is_fwd then iotas else rev_tuple iotas in
  let env = Global.env () in
  let iotas = map_tuple (Array.map (unwrap_definition env)) iotas in
  sigma, { c with iotas }

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
  (* TODO this function is a source of divergence, investigate *)
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
        in 
        if List.length proj_type_rules = 0 then
          check [proj_term_rules; proj_type_rules] sigma
        else
          check [proj_term_rules; proj_type_rules] sigma

(*
 * Get the lifted eta expansion function
 *)
let get_lifted_eta c = snd c.etas

(*
 * Check if a term may apply the eta expansion function,
 * but don't bother checking the type
 *)
let may_apply_eta c env trm =
  (* Heuristic for unification without slowdown *)
  if equal (zoom_term zoom_lambda_term env (fst c.etas)) (mkRel 1) then
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
    | Custom _ ->
       true (* not enough information without unification *)

(*
 * Check if a term applies the eta expansion function function
 *)
let applies_eta c env trm sigma =
  if may_apply_eta c env trm then
    let sigma, typ_args_o = type_is_from c env trm sigma in
    let opt_proj_map = snd c.optimize_proj_id_rules in
    (* Heuristic for unification again *)
    if Option.has_some typ_args_o then
      let typ_args = Option.get typ_args_o in
      let is_custom = match c.l.orn.kind with | Custom _ -> true | _ -> false in
      if (not is_custom) && equal (zoom_term zoom_lambda_term env (fst c.etas)) (mkRel 1) then
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
                       mkLambda (get_rel_ctx_name Anonymous, i_b_typ, unpacked)
                     in pack_sigT { index_type = i_b_typ; packer }
                   in
                   let packer =
                     let at_type = shift i_b_typ in
                     let trm1 = project_index (dest_sigT (shift index_type)) (mkRel 1) in
                     let trm2 = shift i_b' in
                     mkLambda (get_rel_ctx_name Anonymous, index_type, apply_eq { at_type; trm1; trm2 })
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
                 in sigma, Some (snoc packed typ_args)
          | CurryRecord ->
             sigma, Some (snoc trm typ_args)
          | SwapConstruct _ ->
             sigma, None (* impossible state *)
          | Custom _ ->
             (* attempt unification *)
             let eta = fst c.etas in
             let sigma, eargs = mk_n_evars (arity eta) env sigma in
             let eta_app = mkAppl (eta, eargs) in
             let sigma, resolved = unify_resolve_evars env trm eta_app sigma in
             if Option.has_some resolved then
               let (_, eta_app) = Option.get resolved in
               let args = unfold_args eta_app in
               sigma, Some args
             else
               sigma, None
    else
      sigma, None
  else
    sigma, None

let get_iota c = fst c.iotas
let get_lifted_iota c = snd c.iotas

(*
 * When iota is not rewriting by reflexivity, check if we apply Iota
 *)
let applies_iota c env trm sigma =
  match c.l.orn.kind with
  | Custom _ ->
     (* no custom unification yet---require explicit expansion *)
     sigma, None
  | _ ->
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
    | SwapConstruct _ | UnpackSigma | Custom _ ->
       []
  in
  let rules_bwd =
    match l.orn.kind with
    | UnpackSigma ->
       (* not the best we can do *)
       let proj1_rule = (fun a -> (dest_existT a).index) in
       let proj2_rule = (fun a -> (dest_existT a).unpacked) in
       [(projT1, proj1_rule); (projT2, proj2_rule)]
    | SwapConstruct _ | Algebraic (_, _) | CurryRecord | Custom _ ->
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
      if may_apply_eta (reverse c) env arg_inner then
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
 * Custom reduction function for lifted eta expansion function,
 * for efficiency and to ensure termination. For example, this may
 * simplify projections of existentials.
 *)
let reduce_lifted_eta c env sigma trm =
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
 * Initialize the arguments to a case of a DepConstr
 *
 * This needs significant refactoring and cleaning post-deadline
 *)
let initialize_constr_args c env_constr_body env_packed args sigma =
  let l = get_lifting c in
  match l.orn.kind with
  | Algebraic (_, off) ->
     (* Pack arguments *)
     let c = if c.l.is_fwd then reverse c else c in
     let b_typ = fst c.elim_types in
     let rec lift_args sigma args is sh =
       match args with
       | n :: tl ->
          if List.exists (fun (i, _) -> equal n i) is then
            let (_, i') = List.find (fun (i, _) -> equal n i) is in
            Util.on_snd
              (fun tl -> i' :: tl)
              (lift_args sigma tl is (sh + 1))
          else
            let sigma, t = reduce_type env_constr_body sigma n in
            if is_or_applies b_typ t then
              let n = unshift_by sh n in
              let sigma, b_sig = reduce_type env_packed sigma n in
              let b_sig_typ = dest_sigT b_sig in
              let i', b' = projections b_sig_typ n in
              Util.on_snd
                (fun tl -> b' :: tl)
                (lift_args sigma tl ((get_arg off t, i') :: is) sh)
            else
              Util.on_snd
                (fun tl -> unshift_by sh n :: tl)
                (lift_args sigma tl is sh)
       | _ ->
          sigma, []
     in Util.on_snd List.rev (lift_args sigma (List.rev args) [(mkRel 0, mkRel 0)] 0)
  | _ ->
     sigma, args

(*
 * Determine the environment for DepConstr
 *)
let initialize_constr_env c env b_constr sigma =
  let rec init env ind typ constr sigma =
    match kind constr with
    | Lambda (n, t, b) ->
       if is_or_applies ind t then
         let sigma, t' =
           let args = unfold_args t in
           reduce_term env sigma (mkAppl (typ, args))
         in init (push_local (n.binder_name, t') env) ind typ b sigma 
       else
         init (push_local (n.binder_name, t) env) ind typ b sigma
    | _ ->
       sigma, env
  in
  match c.l.orn.kind with
  | Algebraic (_, off) ->
     let a_ind = (if c.l.is_fwd then fst else snd) c.elim_types in
     let a_constr =
       let ((_, c_index), _) = destConstruct b_constr in
       let ((i, i_index), u) = destInd a_ind in
       mkConstructU (((i, i_index), c_index), u)
     in
     let sigma, a_constr_eta = expand_eta env sigma a_constr in
     init env a_ind (snd c.typs) a_constr_eta sigma
  | UnpackSigma ->
     let b_typ = (if c.l.is_fwd then snd else fst) c.elim_types in
     init env b_typ (fst c.typs) b_constr sigma
  | _ ->
     failwith "not implemented"

(*
 * Initialize DepConstr for each type
 *)
let initialize_dep_constrs c cached env sigma =
  let l = c.l in
  let sigma, constrs =
    if Option.has_some cached then
      (* Use the cached DepConstr rules *)
      let (constrs, _, _, _) = Option.get cached in
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
           let c = if l.is_fwd then c else reverse c in
           map_state_array
             (fun constr sigma ->
               let env_c_b, c_body = zoom_lambda_term env constr in
               let sigma, env_packed = initialize_constr_env c env constr sigma in
               let sigma, typ_args = type_from_args (reverse c) env_c_b c_body sigma in
               let sigma, app = lift env_c_b (reverse c).l c_body typ_args sigma in
               let delta app = specialize_delta_f env_c_b (first_fun app) (unfold_args app) in
               let sigma, app_red = reduce_term env_c_b sigma app in
               (* delta-reduce unpack_generic(_inv) *)
               let sigma, app_red = delta app_red sigma in
               let sigma, app_red = delta app_red sigma in
               let sigma, app_red = reduce_term env_c_b sigma app_red in
               let ex_eq = dest_existT app_red in
               let ex = dest_existT ex_eq.index in
               let f' = first_fun ex.unpacked in
               let args' = unfold_args ex.unpacked in
               let sigma, args'' =
                 map_state
                   (fun a sigma ->
                     let sigma_right, is_from_o = type_is_from (reverse c) env_c_b a sigma in
                     if Option.has_some is_from_o then
                       let typ_args = Option.get is_from_o in
                       let sigma, a' = lift env_c_b (get_lifting c) a typ_args sigma_right in
                       let sigma, a'_red = delta a' sigma in
                       let sigma, a'_red = delta a'_red sigma in
                       reduce_term env_c_b sigma a'_red
                     else
                       sigma, a)
                   args'
                   sigma
               in
               let sigma, app_red =
                 if List.for_all2 equal args' args'' then
                   (* base case *)
                   sigma, app_red
                 else
                   (* inductive case (in future, need to tweak for vector to list case) *)
                   let unpacked = mkAppl (f', args'') in
                   let index = pack_existT { ex with unpacked } in
                   sigma, pack_existT { ex_eq with index }
               in sigma, reconstruct_lambda_n env_packed app_red (nb_rel env))
             constrs
             sigma
        | Custom _ ->
           failwith "impossible"
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
               let f = first_fun c_body in
               let sigma, env_packed =  initialize_constr_env c env constr sigma in
               let sigma, args = initialize_constr_args c env_c_b env_packed (unfold_args c_body) sigma in
               let c_body = reduce_stateless reduce_term env_packed sigma (mkAppl (f, args)) in
               let sigma, packed = pack env_packed l c_body sigma in
               sigma, reconstruct_lambda_n env_packed packed (nb_rel env))
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
        | SwapConstruct swaps ->
           let sigma, constrs = eta_constrs env b_typ sigma in
           map_state_array
             (fun i sigma -> sigma, constrs.(List.assoc i swaps - 1))
             (Array.of_list (range 1 (Array.length constrs + 1)))
             sigma
        | UnpackSigma ->
           let sigma, constrs = eta_constrs env (first_fun (zoom_term zoom_lambda_term env b_typ)) sigma in
           map_state_array
             (fun constr sigma ->
               let sigma, constr_exp = expand_eta env sigma constr in
               let (env_c_b, c_body) = zoom_lambda_term env constr_exp in
               let sigma, eta_args_o = applies_eta (if l.is_fwd then reverse c else c) env_c_b c_body sigma in
               let lifted_eta = get_lifted_eta (if l.is_fwd then reverse c else c) in
               let sigma, eta_app = reduce_lifted_eta (if l.is_fwd then reverse c else c) env_c_b sigma (mkAppl (lifted_eta, Option.get eta_args_o)) in
               let c_body_id = reduce_stateless reduce_term env_c_b sigma eta_app in
               let sigma, typ_args = type_from_args (if l.is_fwd then reverse c else c) env_c_b c_body sigma in
               let sigma, app = lift env_c_b (if l.is_fwd then l else flip_dir l) c_body_id typ_args sigma in
               let delta app = specialize_delta_f env_c_b (first_fun app) (unfold_args app) in
               let sigma, app_red = reduce_term env_c_b sigma app in
               (* delta-reduce unpack_generic(_inv) *)
               let sigma, app_red = delta app_red sigma in
               let sigma, app_red = delta app_red sigma in
               let sigma, app_red = reduce_term env_c_b sigma app_red in
               sigma, reconstruct_lambda_n env_c_b app_red (nb_rel env))
             constrs
             sigma
        | Custom _ ->
           failwith "impossible"
      in
      let dep_constrs =
        let c_a_n, c_b_n =
          let promote = Constant.canonical (fst (destConst l.orn.promote)) in
          let (_, lab) = KerName.repr promote in
          let base_n = Label.to_id lab in
          (with_suffix base_n "dep_constr_a", with_suffix base_n "dep_constr_b")
        in
        let a_constrs, b_constrs = ((c_a_n, a_constrs), (c_b_n, b_constrs)) in
        let a_constrs =
          Array.mapi
            (fun i c ->
              let n = with_suffix (fst a_constrs) (string_of_int i) in
              define_term n sigma c)
            (snd a_constrs)
        in
        let b_constrs =
          Array.mapi
            (fun i c ->
              let n = with_suffix (fst b_constrs) (string_of_int i) in
              define_term n sigma c)
            (snd b_constrs)
        in map_tuple (Array.map UnivGen.constr_of_monomorphic_global) (a_constrs, b_constrs)
      in
      save_dep_constrs (l.orn.promote, l.orn.forget) dep_constrs;
      Array.iter2
        (fun c1 c2 ->
          save_lifting (l.orn.promote, l.orn.forget, c1) c2;
          save_lifting (l.orn.forget, l.orn.promote, c2) c1)
        (fst dep_constrs)
        (snd dep_constrs);
      sigma, dep_constrs
  in
  let constrs = if l.is_fwd then constrs else rev_tuple constrs in
  let env = Global.env () in
  let dep_constrs = map_tuple (Array.map (unwrap_definition env)) constrs in
  sigma, { c with dep_constrs }

(*
 * Get the cached unlifted and lifted constructors
 *)
let get_constrs c = fst c.dep_constrs
let get_lifted_constrs c = snd c.dep_constrs

(*
 * Check if a term applies the eta-expanded constructor
 * Part of LIFT-CONSTR, basically a speedup over unification rather than
 * using the constructor rules and unification directly
 *)
let applies_constr_eta c env trm sigma =
  let l = get_lifting c in
  let is_inductive_constr project constrs trm sigma =
    (* Helper function, faster than unifying with constructor rules *)
    try
      let unpacked = project trm in
      let f = first_fun unpacked in
      match kind f with
      | Construct ((_, i), _) when i <= Array.length constrs ->
         let c_i =
           match l.orn.kind with
           | SwapConstruct swaps when not l.is_fwd ->
              List.assoc i swaps - 1
           | _ ->
              i - 1
         in
         let constr = constrs.(c_i) in
         let carity = arity constr in
         let f' = first_fun (project (zoom_term zoom_lambda_term env constr)) in
         let rec forget args is sigma =
           match l.orn.kind with
           | Algebraic _ when not l.is_fwd ->
              (match args with
               | h :: tl ->
                  let sigma, is_i = exists_state (convertible env h) is sigma in
                  if is_i then
                    forget tl is sigma
                  else
                    (try
                       let sigma, b = pack env c.l h sigma in
                       let sigma_right, args_opt = type_is_from c env b sigma in
                       if Option.has_some args_opt then
                         let i_b = (dest_existT b).index in
                         let sigma, tl' = forget tl (i_b :: is) sigma_right in
                         sigma, b :: tl'
                       else
                         let sigma, tl' = forget tl is sigma in
                         sigma, h :: tl'
                     with _ ->
                       let sigma, tl' = forget tl is sigma in
                       sigma, h :: tl')
               | _ ->
                  sigma, args)
           | _ ->
              sigma, args
         in
         let sigma, args = Util.on_snd List.rev (forget (List.rev (unfold_args unpacked)) [] sigma) in
         if equal f f' && List.length args = carity then
           sigma, Some (c_i, args)
         else
           sigma, None
      | _ ->
         sigma, None
    with _ ->
      sigma, None
  in
  if may_apply_eta c env trm then
    match l.orn.kind with
    | Algebraic _ ->
       is_inductive_constr (if l.is_fwd then id else last_arg) (get_constrs c) trm sigma
    | SwapConstruct _ ->
       is_inductive_constr id (get_constrs c) trm sigma
    | CurryRecord ->
       if l.is_fwd then
         is_inductive_constr id (get_constrs c) trm sigma
       else
         if applies (lift_back l) trm then
           sigma, None
         else
           (* we treat any pair of the right type as a constructor *)
           let sigma_right, args_opt = type_is_from c env trm sigma in
           if Option.has_some args_opt then
             let sigma = sigma_right in
             let constr = (get_constrs c).(0) in
             let pms = Option.get args_opt in
             let npm = List.length pms in
             let args = pair_projections_eta_rec_n trm (arity constr - npm) in
             sigma, Some (0, List.append pms args)
           else
             sigma, None
    | UnpackSigma ->
       if l.is_fwd then
         (* Eta rules always take care of this, so no need *)
         sigma, None
       else
         let b_typ_inner = first_fun (zoom_term zoom_lambda_term env (snd c.typs)) in
         let sigma, constrs = eta_constrs env b_typ_inner sigma in 
         is_inductive_constr id constrs trm sigma
    | Custom _ ->
       (* attempt unification *)
       let dep_constrs = Array.to_list (fst c.dep_constrs) in
       let rec applies_dep_constr i constrs sigma =
         match constrs with
         | constr :: tl ->
            if is_or_applies constr trm then
              sigma, Some (i, unfold_args trm)
            else
              let constr_def = unwrap_definition env constr in
              if is_or_applies constr_def trm then
                sigma, Some (i, unfold_args trm)
              else
                (* Unfortunately, unification reduces eliminators :( *)
                (* so we can't even be this smart yet *)
                applies_dep_constr (i + 1) tl sigma
         | _ ->
            sigma, None
       in applies_dep_constr 0 dep_constrs sigma
  else
    sigma, None

(*
 * Custom simplification for applications of constructors
 *)
let reduce_constr_app c env sigma trm =
  let l = get_lifting c in
  let sigma, trm = reduce_term env sigma trm in
  match l.orn.kind with
  | Algebraic _ when l.is_fwd ->
     let ex = dest_existT trm in
     let sigma, index = reduce_coh c env sigma ex.index in
     let sigma, unpacked = reduce_coh c env sigma ex.unpacked in
     sigma, pack_existT { ex with index; unpacked }
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

(* Determine the parameters for DepElim *)
let initialize_dep_elim_pms c env_elim pms is_match sigma =
  match c.l.orn.kind with
  | CurryRecord when not c.l.is_fwd ->
     if is_match then
       sigma, pms
     else
       let typ_f = first_fun (zoom_term zoom_lambda_term env_elim (snd (get_types c))) in
       let sigma, to_typ_prod = specialize_delta_f env_elim typ_f pms sigma in
       let to_elim = dest_prod to_typ_prod in
       sigma, [to_elim.Produtils.typ1; to_elim.Produtils.typ2]
  | _ ->
     sigma, pms
                          
(* Determine the motive for DepElim (needs cleaning post-deadline) *)
let initialize_dep_elim_p c env_elim elim_pms npms p is_match sigma =
  match c.l.orn.kind with
  | Algebraic (indexer, off) when not c.l.is_fwd ->
     let (_, p_typ, _) = destLambda elim_pms in
     let env_p_b, p_b = zoom_product_type env_elim p_typ in
     let nargs = new_rels2 env_p_b env_elim in
     let f = shift_by nargs p in
     let sigma, args =
       let old_args = mk_n_rels nargs in
       let b = last old_args in
       if is_match then
         (* We are detecting applications of dep_elim *)
         let sigma, b_sig_typ = reduce_type env_p_b sigma b in
         let b_sig = dest_sigT b_sig_typ in
         let i_b, b = projections b_sig b in
         let value_off = List.length old_args - 1 in
         let orn = { c.l.orn with kind = Algebraic (indexer, off - npms) } in
         let l = { c.l with orn } in (* no parameters here *)
         sigma, index l i_b (reindex value_off b old_args)
       else
         (* We are instantiating dep_elim for the first time *)
         let sigma, b = pack env_p_b c.l b sigma in
         let value_off = List.length old_args - 1 in
         let orn = { c.l.orn with kind = Algebraic (indexer, off - npms) } in
         let l = { c.l with orn } in (* no parameters here *)
         sigma, deindex l (reindex value_off b old_args)
     in
     let sigma, p_b = reduce_term env_p_b sigma (mkAppl (f, args)) in
     sigma, reconstruct_lambda_n env_p_b p_b (nb_rel env_elim)
  | CurryRecord when not c.l.is_fwd ->
     let (_, p_typ, _) = destLambda elim_pms in
     let env_p_b, p_b = zoom_product_type env_elim p_typ in
     let nargs = new_rels2 env_p_b env_elim in
     let f = shift_by nargs p in
     let sigma, args =
       let old_args = mk_n_rels nargs in
       let b = last old_args in
       if is_match then
         (* We are detecting applications of dep_elim *)
         sigma, [b]
       else
         (* We are instantiating dep_elim for the first time *)
         let sigma, b = pack env_p_b c.l b sigma in
         sigma, [b]
     in
     let sigma, p_b = reduce_term env_p_b sigma (mkAppl (f, args)) in
     sigma, reconstruct_lambda_n env_p_b p_b (nb_rel env_elim)
  | _ ->
     sigma, p

(*
 * Initialize the arguments to a case of a constructor of DepElim
 *
 * This needs cleaning post-deadline
 *)
let initialize_dep_elim_c_args c env_case env_elim case_typ nargs npms case is_match sigma =
  let l = get_lifting c in
  match l.orn.kind with
  | Algebraic (_, off) when not l.is_fwd ->
     let sigma, case_typ = reduce_type env_elim sigma case in
     let env_case_typ = zoom_env zoom_product_type env_elim case_typ in
     let args = mk_n_rels (new_rels2 env_case_typ env_elim) in
     let b_typ = get_elim_type c in
     if is_match then
       (* matching against DepElim *)
       let rec lift_args sigma args is sh =
         match args with
         | n :: tl ->
            if List.exists (fun (i, _) -> equal n i) is then
              let (_, i') = List.find (fun (i, _) -> equal n i) is in
              Util.on_snd
                (fun tl -> i' :: tl)
                (lift_args sigma tl is (sh + 1))
            else
              let sigma, t = reduce_type env_case_typ sigma n in
              if is_or_applies b_typ t then
                let n = unshift_by sh n in
                let sigma, b_sig = reduce_type env_case sigma n in
                let b_sig_typ = dest_sigT b_sig in
                let i', b' = projections b_sig_typ n in
                Util.on_snd
                  (fun tl -> b' :: tl)
                  (lift_args sigma tl ((get_arg off t, i') :: is) sh)
              else
                Util.on_snd
                  (fun tl -> unshift_by sh n :: tl)
                  (lift_args sigma tl is sh)
         | _ ->
            sigma, []
       in Util.on_snd List.rev (lift_args sigma (List.rev args) [(mkRel 0, mkRel 0)] 0)
     else
       (* initializing DepElim for the first time *)
       let rec lift_args sigma args is =
         match args with
         | n :: tl ->
            if List.exists (equal n) is then
              lift_args sigma (shift_all (n :: tl)) is
            else
              let sigma, t = reduce_type env_case sigma n in
              if is_or_applies b_typ t then
                let sigma, b' = pack env_case c.l n sigma in
                let i = get_arg off t in
                Util.on_snd
                  (fun tl -> b' :: tl)
                  (lift_args sigma tl (i :: is))
              else
                Util.on_snd
                  (fun tl -> n :: tl)
                  (lift_args sigma tl is)
         | _ ->
            sigma, []
       in Util.on_snd List.rev (lift_args sigma (List.rev args) [mkRel 0])
  | CurryRecord when not l.is_fwd ->
     let args = mk_n_rels nargs in
     let b_typ = get_elim_type c in
     if not is_match then
       let c_args, b_args = take_split 2 args in
       let sigma, args_tl = prod_projections_rec env_case (List.hd (List.tl c_args)) sigma in
       sigma, List.append (List.hd c_args :: args_tl) b_args
     else
       let (ind, _) = destInd b_typ in
       let sigma, c_typ = reduce_type env_case sigma (mkConstruct (ind, 1)) in
       let nargs_lifted = arity c_typ in
       let c_args, b_args = take_split nargs_lifted args in
       let sigma, arg_pair = pack_pair_rec env_case (List.tl c_args) sigma in
       sigma, List.append [List.hd c_args; arg_pair] b_args
  | _ ->
     sigma, mk_n_rels nargs
              
(*
 * Determine a single case for DepElim
 *)
let initialize_dep_elim_c c env_elim elim_c npms case is_match sigma =
  match c.l.orn.kind with
  | Algebraic _ | CurryRecord when not c.l.is_fwd ->
     let (_, case_typ, _) = destLambda elim_c in
     let env_c = zoom_env zoom_product_type env_elim case_typ in
     let nargs = new_rels2 env_c env_elim in
     let case = if c.l.orn.kind = CurryRecord || is_match then case else unshift case in
     if nargs = 0 then
       (* no need to get arguments *)
       sigma, case
     else
       (* get arguments *)
       let sigma, c_eta = expand_eta env_elim sigma case in
       let (env_c_b, c_body) = zoom_lambda_term env_elim c_eta in
       let (c_f, _) = destApp c_body in
       let sigma, args = initialize_dep_elim_c_args c env_c env_elim (shift_by nargs case_typ) nargs npms case is_match sigma in
       let f = unshift_by (new_rels2 env_c_b env_c) c_f in
       let sigma, body = reduce_term env_c sigma (mkAppl (f, args)) in
       sigma, reconstruct_lambda_n env_c body (nb_rel env_elim)
  | _ ->
     sigma, case

(* Determine the cases for DepElim *)
let initialize_dep_elim_cs c env_dep_elim elim_p npms cs is_match sigma =
  let cs =
    match (get_lifting (if is_match then reverse c else c)).orn.kind with
    | SwapConstruct swaps ->
       (* swap the order before eliminating *)
       let cs_arr = Array.of_list cs in
       List.map
         (fun i -> cs_arr.(List.assoc i swaps - 1))
         (range 1 (List.length cs + 1))
    | _ ->
       (* leave the order alone *)
       cs
  in
  bind
    (fold_left_state
       (fun (elim_c, cs) case sigma ->
         let sigma, case = initialize_dep_elim_c c env_dep_elim elim_c npms case is_match sigma in
         let sigma, elim_c = reduce_term env_dep_elim sigma (mkAppl (elim_c, [case])) in
         sigma, (elim_c, snoc case cs))
       (elim_p, [])
       cs)
    (fun (_, cs) -> ret cs)
    sigma

(* Determine the arguments for DepElim *)
let initialize_dep_elim_args c env_elim elim_cs npms args is_match sigma =
  let l = get_lifting c in
  match l.orn.kind with
  | Algebraic (indexer, off) when not l.is_fwd ->
     let value_off = arity elim_cs - 1 in
     let off = off - npms in (* no parameters here *)
     if is_match then
       (* match against DepElim and find arguments *)
       let b_old = last args in
       let sigma, b = pack env_elim l b_old sigma in
       sigma, reindex value_off b (deindex l args)
     else
       (* initialize DepElim for the first time *)
       let up_to_i_b, after_i_b = take_split (off + 1) args in
       let up_to_i_b = unshift_all up_to_i_b in
       let b_old = last after_i_b in
       let sigma, b_typ = reduce_type env_elim sigma b_old in
       let b_sig_typ = dest_sigT b_typ in
       let i_b, b = projections b_sig_typ b_old in
       let up_to_i_b = reindex off i_b up_to_i_b in
       let after_i_b = reindex (value_off - off - 1) b after_i_b in
       sigma, List.append up_to_i_b after_i_b
  | _ ->
     sigma, args

(* Determine the environment for DepElim (needs mega cleaning post-deadline) *)
let initialize_dep_elim_env c env sigma =
  match c.l.orn.kind with
  | Algebraic _ | SwapConstruct _ | CurryRecord when not c.l.is_fwd ->
     let elim_typ_rev = get_elim_type (reverse c) in
     let elim_rev = type_eliminator env (fst (destInd elim_typ_rev)) in
     let sigma, elim_rev_eta = expand_eta env sigma elim_rev in
     let env_elim_rev, elim_body_rev = zoom_lambda_term env elim_rev_eta in
     let sigma, elim_app_rev = deconstruct_eliminator env_elim_rev sigma elim_body_rev in
     let env, elim_rev = zoom_n_lambda env (List.length elim_app_rev.pms) elim_rev_eta in
     let (p_n, p_typ, b) = destLambda elim_rev in
     let rec init_p_typ env p_typ sigma =
       match kind p_typ with
       | Prod (n, t, b) ->
          let env_b = push_local (n.binder_name, t) env in
          let sigma, b' = init_p_typ env_b b sigma in
          if is_or_applies elim_typ_rev t then
            let args = unfold_args t in
            let sigma, t' =
              if List.length args = 0 then
                sigma, snd (get_types c)
              else
                reduce_term env sigma (mkAppl (snd (get_types c), args))
            in sigma, mkProd (n, t', b')
          else
            sigma, mkProd (n, t, b')
       | _ ->
          sigma, p_typ
     in
     let sigma, p_typ' = init_p_typ env p_typ sigma in
     let env_p = push_local (p_n.binder_name, p_typ') env in
     let rec init_case_typ env case_typ p sigma =
       match kind case_typ with
       | Prod (n, t, b) ->
          let env_b = push_local (n.binder_name, t) env in
          let sigma, b' = init_case_typ env_b b (shift p) sigma in
          if is_or_applies elim_typ_rev t then
            let args = unfold_args t in
            let sigma, t' =
              if List.length args = 0 then
                sigma, snd (get_types c)
              else
                reduce_term env sigma (mkAppl (snd (get_types c), args))
            in sigma, mkProd (n, t', b')
          else if is_or_applies p t then
            let sigma, t' =
              let f = first_fun t in
              let args = all_but_last (unfold_args t) in
              let arg = last_arg t in
              let lifted_eta = fst c.etas in
              let pms = mk_n_rels (List.length elim_app_rev.pms) in
              let pms = shift_all_by (nb_rel env - List.length pms) pms in
              let sigma, arg' = reduce_term env sigma (mkAppl (lifted_eta, List.append pms (snoc arg args))) in
              reduce_term env sigma (mkAppl (f, snoc arg' args))
            in sigma, mkProd (n, t', b')
          else
            sigma, mkProd (n, t, b')
       | _ ->
          let f = first_fun case_typ in
          let args = all_but_last (unfold_args case_typ) in
          let arg = last_arg case_typ in
          let sigma, app_o = applies_constr_eta (reverse c) env arg sigma in
          let i, c_args = Option.get app_o in
          let lifted_constr = (get_constrs c).(i) in
          let sigma, arg' = reduce_term env sigma (mkAppl (lifted_constr, c_args)) in
          reduce_term env sigma (mkAppl (f, snoc arg' args))
     in
     let rec init env elim i sigma =
       match kind elim with
       | Lambda (n, t, b) ->
          if i < List.length elim_app_rev.cs then
            let sigma, t' = init_case_typ env t (mkRel (i + 1)) sigma in
            init (push_local (n.binder_name, t') env) b (i + 1) sigma
          else if is_or_applies elim_typ_rev t then
            let args = unfold_args t in
            let sigma, t' =
              if List.length args = 0 then
                sigma, snd (get_types c)
              else
                reduce_term env sigma (mkAppl (snd (get_types c), args))
            in init (push_local (n.binder_name, t') env) b (i + 1) sigma
          else
            init (push_local (n.binder_name, t) env) b (i + 1) sigma
       | _ ->
          sigma, env
     in init env_p b 0 sigma
  | _ ->
     sigma, env

(* Determine DepElim (needs cleaning post-deadline) *)
let initialize_dep_elim c env sigma =
  let elim_typ = get_elim_type c in
  let elim = type_eliminator env (fst (destInd elim_typ)) in
  match c.l.orn.kind with
  | Algebraic _ | SwapConstruct _ | CurryRecord when not c.l.is_fwd ->
     let sigma, env_dep_elim = initialize_dep_elim_env c env sigma in
     let sigma, elim_eta = expand_eta env_dep_elim sigma elim in
     let sigma, dep_elim =
       let npms =
         if c.l.orn.kind = CurryRecord then
           nb_rel env_dep_elim - 3
         else
           let env_elim, elim_body = zoom_lambda_term env_dep_elim elim_eta in
           let sigma, elim_app = deconstruct_eliminator env_elim sigma elim_body in
           List.length elim_app.pms
       in
       let sigma, pms =
         let pms = shift_all_by (nb_rel env_dep_elim - npms) (mk_n_rels npms) in
         initialize_dep_elim_pms c env_dep_elim pms false sigma
       in
       let sigma, elim_pms = reduce_term env_dep_elim sigma (mkAppl (elim_eta, pms)) in
       let sigma, p = initialize_dep_elim_p c env_dep_elim elim_pms npms (shift_by (nb_rel env_dep_elim - npms - 1) (mkRel 1)) false sigma in
       let sigma, elim_p = reduce_term env_dep_elim sigma (mkAppl (elim_pms, [p])) in
       let sigma, cs =
         let sigma, elim_eta = expand_eta env_dep_elim sigma elim_p in
         let env_elim, elim_body = zoom_lambda_term env_dep_elim elim_eta in
         let sigma, elim_body = reduce_term env_elim sigma elim_body in
         let sigma, elim_app = deconstruct_eliminator env_elim sigma elim_body in
         initialize_dep_elim_cs c env_dep_elim elim_p npms elim_app.cs false sigma
       in
       let sigma, elim_cs = reduce_term env_dep_elim sigma (mkAppl (elim_p, cs)) in
       let sigma, final_args =
         let nargs = arity elim_cs in
         let args = mk_n_rels nargs in
         initialize_dep_elim_args c env_dep_elim elim_cs npms args false sigma
       in reduce_term env_dep_elim sigma (mkAppl (elim_cs, final_args))
     in sigma, reconstruct_lambda_n env_dep_elim dep_elim (nb_rel env)
  | _ ->
     expand_eta env sigma elim

(*
 * Initialize dep_elims
 *)
let initialize_dep_elims c cached env sigma =
  let sigma, elims =
    if Option.has_some cached then
      (* Use the cached DepElim rules *)
      let (_, elims, _, _) = Option.get cached in
      sigma, elims
    else
      (* Determine DepElim and cache if needed *)
      let c = if c.l.is_fwd then c else reverse c in
      let sigma, a_elim = initialize_dep_elim c env sigma in
      let sigma, b_elim = initialize_dep_elim (reverse c) env sigma in
      let elim_a_n, elim_b_n =
        let promote = Constant.canonical (fst (destConst c.l.orn.promote)) in
        let (_, lab) = KerName.repr promote in
        let base_n = Label.to_id lab in
        (with_suffix base_n "dep_elim_a", with_suffix base_n "dep_elim_b")
      in
      let elim_a, elim_b = ((elim_a_n, a_elim), (elim_b_n, b_elim)) in
      let elim_a = define_term (fst elim_a) sigma (snd elim_a) in
      let elim_b = define_term (fst elim_b) sigma (snd elim_b) in
      let elims = map_tuple UnivGen.constr_of_monomorphic_global (elim_a, elim_b) in
      save_dep_elim (c.l.orn.promote, c.l.orn.forget) elims;
      save_lifting (c.l.orn.promote, c.l.orn.forget, (fst elims)) (snd elims);
      save_lifting (c.l.orn.forget, c.l.orn.promote, (snd elims)) (fst elims);
      sigma, elims
  in
  let elims = if c.l.is_fwd then elims else rev_tuple elims in
  sigma, { c with dep_elims = elims }

let get_dep_elim c = fst (c.dep_elims)
let get_lifted_dep_elim c = snd (c.dep_elims)

(*
 * Check if the term applies dep_elim, and if so return the arguments
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
           | Algebraic _ | SwapConstruct _ | CurryRecord ->
              (* We return the elimination of dep_elim here *)
              if l.is_fwd then
                let args = unfold_args (apply_eliminator trm_elim) in
                sigma, Some args
              else
                let sigma, is_from = if l.orn.kind = CurryRecord then type_is_from c env_elim (List.hd trm_elim.final_args) sigma else sigma, None in
                if (not (l.orn.kind = CurryRecord)) || Option.has_some is_from then
                  let elim = get_dep_elim c in
                  let sigma, pms =
                    let pms_old =
                      if l.orn.kind = CurryRecord then
                        Option.get is_from
                      else
                        trm_elim.pms
                    in initialize_dep_elim_pms c env_elim pms_old true sigma
                  in
                  let npms = List.length trm_elim.pms in
                  let elim_delta = unwrap_definition env_elim elim in
                  let sigma, elim_pms = reduce_term env_elim sigma (mkAppl (elim_delta, pms)) in
                  let sigma, p = initialize_dep_elim_p c env_elim elim_pms npms trm_elim.p true sigma in
                  let sigma, elim_p = reduce_term env_elim sigma (mkAppl (elim_pms, [p])) in
                  let sigma, cs = initialize_dep_elim_cs c env_elim elim_p npms trm_elim.cs true sigma in
                  let sigma, elim_cs = reduce_term env_elim sigma (mkAppl (elim_p, cs)) in
                  let sigma, final_args = initialize_dep_elim_args c env_elim elim_cs npms trm_elim.final_args true sigma in
                  let trm_elim = { elim; pms; p; cs; final_args } in
                  let args = unfold_args (apply_eliminator trm_elim) in
                  sigma, Some args
                else
                  sigma, None
           | UnpackSigma ->
              (* eventually, use explicit depelim here too *)
              let args = unfold_args (apply_eliminator trm_elim) in
              sigma, Some args
           | Custom _ ->
              (* attempt unification *)
              let dep_elim = fst c.dep_elims in
              if is_or_applies dep_elim trm then
                sigma, Some (unfold_args trm)
              else
                let dep_elim_def = lookup_definition env dep_elim in
                if is_or_applies dep_elim_def trm then
                  sigma, Some (unfold_args trm)
                else
                  let sigma, dep_elim_eta = expand_eta env sigma dep_elim in
                  let sigma, eargs = mk_n_evars (arity dep_elim_eta) env sigma in
                  let elim_app = mkAppl (dep_elim, eargs) in
                  let sigma, resolved = unify_resolve_evars env trm elim_app sigma in
                  if Option.has_some resolved then
                    let (_, elim_app) = Option.get resolved in
                    let args = unfold_args elim_app in
                    sigma, Some args
                  else
                    sigma, None
         in
         if Option.has_some elim_app_o then
           let args = Option.get elim_app_o in
           if new_rels2 env_elim env > 0 then
             sigma, Some (Some trm_eta, args)
           else
             sigma, Some (None, args)
         else
           sigma, None
       else
         sigma, None
     else
       sigma, None
  | _ ->
     sigma, None

(* Reduce the lifted eliminator application *)
let reduce_lifted_elim c env sigma trm =
  let (f, args) = destApp trm in
  let f' = (try lookup_definition env f with _ -> f) in
  let sigma, trm' = reduce_term env sigma (mkApp (f', args)) in
  match c.l.orn.kind with
  | Algebraic _ when c.l.is_fwd ->
     let map_reduce t sigma =
       map_unit_env_if_lazy
         (fun env sigma t ->
           match kind t with
           | App (f, args) when Array.length args > 0 ->
              let arg = last (Array.to_list args) in
              sigma, may_apply_eta (reverse c) env arg
           | _ ->
              sigma, false)
         (fun env sigma t ->
           let how_reduce_o = can_reduce_now c env t in
           if Option.has_some how_reduce_o then
             let reduce = Option.get how_reduce_o in
             reduce env sigma (last_arg t)
           else
             sigma, t)
         env
         sigma
         t
     in
     let sigma, elim_app = deconstruct_eliminator env sigma trm' in
     let sigma, cs = map_state map_reduce elim_app.cs sigma in
     let sigma, final_args = map_state map_reduce elim_app.final_args sigma in
     sigma, apply_eliminator { elim_app with cs; final_args }
  | _ ->
     sigma, trm'

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
      proj_rules = ([], []), ([], []);
      optimize_proj_id_rules = [], [];
      etas = (mkRel 1, mkRel 1);
      iotas = (Array.make 0 (mkRel 1), Array.make 0 (mkRel 1));
      cache;
      opaques
    }
  in
  let cached = lookup_config (l.orn.promote, l.orn.forget) in
  let sigma, c = initialize_proj_rules c env sigma in
  let sigma, c = initialize_optimize_proj_id_rules c env sigma in
  let sigma, c = initialize_etas c cached env sigma in
  let sigma, c = initialize_elim_types c env sigma in
  let sigma, c = initialize_dep_constrs c cached env sigma in
  let sigma, c = initialize_iotas c cached env sigma in
  initialize_dep_elims c cached env sigma
  

