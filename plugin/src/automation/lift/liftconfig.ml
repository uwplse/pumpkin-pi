open Lifting
open Constr
open Environ
open Evd
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
open Evarutil
open Evarconv
open Names
open Equtils
open Idutils
open Convertibility

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
    packed_constrs : types array * types array;
    constr_rules : types array * types array;
    proj_rules :
      ((constr * constr) list * (types * types) list) *
      ((constr * constr) list * (types * types) list);
    optimize_proj_id_rules :
      ((constr * (constr -> constr)) list) *
      ((constr * (constr -> constr)) list);
    id_rules : (constr * constr);
    cache : temporary_cache;
    opaques : temporary_cache
  }

(* --- Convenient shorthand --- *)

let convertible env t1 t2 sigma =
  if equal t1 t2 then
    sigma, true
  else
    convertible env sigma t1 t2

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

(* --- Questions about types A and B --- *)

let get_types c = c.typs

let get_elim_type c = fst (c.elim_types)

(*
 * Optimization for is_from: things to try rather than trying unification,
 * if our type is in a format that is very easy to reason about without
 * unification.
 *)
let optimize_is_from c env goal_typ typ sigma =
  if c.l.is_fwd then
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
  let (a_typ, b_typ) = c.typs in
  let goal_typ = if c.l.is_fwd then a_typ else b_typ in
  let sigma, args_o = optimize_is_from c env goal_typ typ sigma in
  if Option.has_some args_o then
    sigma, args_o
  else
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
                    let sigma, eargs =
                      map_state
                        (fun r sigma ->
                          let sigma, (earg_typ, _) = new_type_evar env_b sigma univ_flexible in
                          let sigma, earg = new_evar env_b sigma earg_typ in
                          sigma, EConstr.to_constr sigma earg)
                        (mk_n_rels (arity proj_i))
                        sigma
                    in
                    (* TODO move this to your own evarutils or something. maybe force resolve in is_from too. see how slow *)
                    let proj_app = EConstr.of_constr (mkAppl (proj_i, eargs)) in
                    let sigma_ref = ref (the_conv_x env_b (EConstr.of_constr b) proj_app sigma) in
                    let proj_app = Typing.e_solve_evars env_b sigma_ref proj_app in
                    let sigma = !sigma_ref in
                    let args = unfold_args (EConstr.to_constr sigma proj_app) in
                    sigma, Some (i, args, trm_eta)
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
      | (proj_map, proj_opaque) :: tl ->
         let proj_terms = List.map fst proj_map in
         let sigma, to_proj_o = check_is_proj c env trm proj_terms sigma in
         if Option.has_some to_proj_o then
           let i, args, trm_eta = Option.get to_proj_o in
           let (_, proj) = List.nth proj_map i in
           sigma, Some (proj, args, trm_eta, proj_opaque)
         else
           check tl sigma
      | _ ->
         sigma, None
    in check [(proj_term_rules, false); (proj_type_rules, true)] sigma

(*
 * Get the cached unlifted constructors
 *)
let get_constrs c = fst c.packed_constrs

(*
 * Get the cached lifted constructors
 *)
let get_lifted_constrs c = fst c.constr_rules

(*
 * Check if a term may apply the eta-expanded identity function,
 * but don't bother checking the type
 *)
let may_apply_id_eta c env trm =
  (* Heuristic for unification without slowdown *)
  if equal (zoom_term zoom_lambda_term env (fst c.id_rules)) (mkRel 1) then
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
      if equal (zoom_term zoom_lambda_term env (fst c.id_rules)) (mkRel 1) then
        sigma, Some (snoc trm typ_args, trm)
      else
        let l = get_lifting c in
        if is_or_applies (lift_back l) trm then
          sigma, Some (snoc trm typ_args, trm)
        else
          match l.orn.kind with
          | Algebraic _ ->
             let proj_value = snd (last opt_proj_map) in
             let proj_arg = proj_value trm in
             sigma, Some (snoc proj_arg typ_args, proj_arg)
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
               in sigma, Some (List.append typ_args [i_b; b; h_eq], b)
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
                 in sigma, Some (snoc packed typ_args, packed)
               else
                 (* TODO redundant TBH *)
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
                         (* TODO this is p1 *)
                         let packer = b_sig.packer in
                         let index = last typ_args in
                         let unpacked = trm in
                         pack_existT { index_type; packer; index; unpacked }
                       in
                       (* TODO this is p2 *)
                       let unpacked = apply_eq_refl { typ = index_type; trm = index_index } in
                       index, unpacked
                     in sigma, pack_existT { index_type; packer; index; unpacked }
                 in
                 sigma, Some (snoc packed typ_args, packed)
          | CurryRecord ->
             sigma, Some (snoc trm typ_args, trm)
          | SwapConstruct _ ->
             sigma, None (* impossible state *)
    else
      sigma, None
  else
    sigma, None

(*
 * Get the cached lifted identity function
 *)
let get_lifted_id_eta c = snd c.id_rules

(* --- Modifying the configuration --- *)

let reverse c =
  {
    c with
    l = flip_dir c.l;
    elim_types = reverse c.elim_types;
    packed_constrs = reverse c.packed_constrs;
    proj_rules = reverse c.proj_rules;
    constr_rules = reverse c.constr_rules;
    optimize_proj_id_rules = reverse c.optimize_proj_id_rules;
    id_rules = reverse c.id_rules;
  }

let zoom c =
  match c.l.orn.kind with
  | Algebraic (indexer, off) ->
     let typs = map_tuple shift c.typs in
     { c with typs }
  | _ ->
     c

(* --- Smart simplification --- *)

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

(* --- Initialization --- *)

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
 * Initialize the packed constructors for each type
 * TODO use id rules to pack
 *)
let initialize_packed_constrs c env sigma =
  let a_typ, b_typ = c.typs in
  let l = c.l in
  let sigma, a_constrs =
    match l.orn.kind with
    | Algebraic _ | CurryRecord | SwapConstruct _ ->
       eta_constrs env a_typ sigma
    | UnpackSigma ->
       (* We create a proxy "constructor" here, though it is just a function *)
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
       let packed =
         let index_type =
           let index_type = eq_typ_app.at_type in
           let packer =
             let unpacked = mkAppl (shift b_typ, [mkRel 1]) in
             mkLambda (Anonymous, index_type, unpacked)
           in pack_sigT { index_type; packer }
         in
         let packer =
           let at_type = shift eq_typ_app.at_type in
           let trm1 = project_index (dest_sigT (shift index_type)) (mkRel 1) in
           let trm2 = shift eq_typ_app.trm2 in
           mkLambda (Anonymous, index_type, apply_eq { at_type; trm1; trm2 })
         in
         let index =
           let index_type_app = dest_sigT index_type in
           let index_type = index_type_app.index_type in
           let packer = index_type_app.packer in
           let index = eq_typ_app.trm1 in
           pack_existT { index_type; packer; index; unpacked = b }
         in pack_existT { index_type; packer; index; unpacked = eq }
       in sigma, Array.make 1 (reconstruct_lambda_n env_eq packed (nb_rel env))
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
       let id_b = if l.is_fwd then snd c.id_rules else fst c.id_rules in
       (* TODO move constrs into here *)
       sigma, Array.make 1 id_b
  in
  let fwd_constrs = if l.is_fwd then a_constrs else b_constrs in
  let bwd_constrs = if l.is_fwd then b_constrs else a_constrs in
  sigma, { c with packed_constrs = (fwd_constrs, bwd_constrs) }
           
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
     (* specialized folding for a cleaner and more efficient result *)
     let delta app = specialize_delta_f env (first_fun app) (unfold_args app) in
     let sigma, app = reduce_term env sigma app in
     (* delta-reduce unpack_generic(_inv) (no custom equivalence support yet) *)
     let sigma, app = delta app sigma in
     let sigma, app = delta app sigma in
     let f = first_fun app in
     let args = unfold_args app in
     let sigma, args =
       if l.is_fwd then
         (* simplify projections of existentials *)
         map_state
           (fun a sigma ->
             let how_reduce_o = can_reduce_now (reverse c) env a in
             if Option.has_some how_reduce_o then
               let proj_a = Option.get how_reduce_o in
               let a_inner = last_arg a in
               let how_reduce_o = can_reduce_now (reverse c) env a_inner in
               if Option.has_some how_reduce_o then
                 let proj_a_inner = Option.get how_reduce_o in
                 let a_inner_inner = last_arg a_inner in
                 let sigma, a_red = proj_a_inner env sigma a_inner_inner in
                 proj_a env sigma a_red
               else
                 proj_a env sigma a_inner
             else
               sigma, a)
           args
           sigma
       else
         sigma, args
     in sigma, (mkAppl (f, args))
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
  let (fwd_constrs, bwd_constrs) = c.packed_constrs in
  let sigma, lifted_fwd_constrs =
    map_state_array (initialize_constr_rule c env) fwd_constrs sigma
  in
  let sigma, lifted_bwd_constrs =
    map_state_array (initialize_constr_rule (reverse c) env) bwd_constrs sigma
  in
  let constr_rules = (lifted_fwd_constrs, lifted_bwd_constrs) in
  sigma, { c with constr_rules }
                       
(* 
 * Initialize the rules for lifting projections
 * This is COHERENCE, but cached
 *)
let initialize_proj_rules c env sigma =
  let init c sigma =
    let l = get_lifting c in
    let sigma, lift_typ = reduce_type env sigma (lift_to l) in
    let env_proj = zoom_env zoom_product_type env lift_typ in
    let t = mkRel 1 in
    let sigma, typ_args = type_from_args c env_proj t sigma in
    let sigma, lift_t = lift env_proj l t typ_args sigma in
    match l.orn.kind with
    | Algebraic (indexer, _) ->
       if l.is_fwd then (* indexer -> projT1 *)
         let sigma, b_sig_typ = Util.on_snd dest_sigT (reduce_type env_proj sigma lift_t) in
         let p1 = reconstruct_lambda env_proj (project_index b_sig_typ lift_t) in
         let indexer = reconstruct_lambda env_proj (mkAppl (indexer, mk_n_rels (nb_rel env_proj))) in
         sigma, ([(indexer, p1)], [])
       else (* projT1 -> indexer, projT2 -> id *)
         let args = shift_all (mk_n_rels (nb_rel env_proj - 1)) in
         let p1 = reconstruct_lambda env_proj (mkAppl (indexer, snoc lift_t args)) in
         let p2 = reconstruct_lambda env_proj lift_t in
         let sigma, b_sig_typ = Util.on_snd dest_sigT (reduce_type env_proj sigma t) in
         let projT1 = reconstruct_lambda env_proj (project_index b_sig_typ t) in
         let projT2 = reconstruct_lambda env_proj (project_value b_sig_typ t) in
         sigma, ([(projT1, p1); (projT2, p2)], [])
    | UnpackSigma ->
       let packed, unpacked = if l.is_fwd then (t, lift_t) else (lift_t, t) in
       let sigma, b_sig_eq_typ = reduce_type env_proj sigma packed in
       let b_sig_eq_typ_app = dest_sigT b_sig_eq_typ in
       let proj_bods = projections b_sig_eq_typ_app packed in
       let projT1, projT2 = map_tuple (reconstruct_lambda env_proj) proj_bods in
       let sigma, (index_type, index) =
         let sigma, args = unpack_typ_args env_proj b_sig_eq_typ sigma in
         sigma, (List.hd args, last args)
       in
       let b_sig_typ = b_sig_eq_typ_app.index_type in
       let p1 =
         let packer = (dest_sigT b_sig_typ).packer in
         let indexer = pack_existT { index_type; packer; index; unpacked } in
         reconstruct_lambda env_proj indexer
       in
       let p2 =
         let eq = apply_eq_refl { typ = index_type; trm = index } in
         reconstruct_lambda env_proj eq
       in
       (* TODO can we move this into identity? also clean up w/ rules above and explain why different (basically need to capture rew in op. dir since can't capture arbitrary refl) *)
       let sigma, p1_p2 = (* TODO maybe remove after proj1_bwd works, if it does *)
         let index_type = b_sig_typ in
         let packer = b_sig_eq_typ_app.packer in
         let sigma, index = reduce_term env_proj sigma (mkAppl (p1, mk_n_rels (nb_rel env_proj))) in
         let sigma, unpacked = reduce_term env_proj sigma (mkAppl (p2, mk_n_rels (nb_rel env_proj))) in
         let packed = pack_existT { index_type; packer; index; unpacked } in
         sigma, reconstruct_lambda env_proj packed
       in
       let id = reconstruct_lambda env_proj lift_t in
       if l.is_fwd then (* projT1 -> pack, projT2 -> eq_refl *)
         sigma, ([(projT1, p1); (projT2, p2)], [])
       else (* pack -> projT1, existT _ pack eq_refl -> existT _ _ projT2 *)
         (* (we can't infer the arguments to eq_refl in more general cases,
            and not every eq_refl n is coherence. so we need to restrict
            our inputs to a certain format, which makes sense given the
            self reference) TODO clean and move comment *)
         (* TODO then for typs do we want to restrict below? *)
         let p1_typ = reconstruct_lambda (pop_rel_context 2 env_proj) (unshift_by 2 b_sig_typ) in
         let p2_typ = reconstruct_lambda (pop_rel_context 1 env_proj) (unshift b_sig_eq_typ_app.packer) in
         let sigma, projT1_bwd =
           let packer = (dest_sigT b_sig_typ).packer in
           let index = mkRel 2 in
           let unpacked =
             let at_type = index_type in
             let trm1 = project_index (dest_sigT b_sig_typ) (fst proj_bods) in
             let trm2 = mkRel 2 in
             let b = project_value (dest_sigT b_sig_typ) (fst proj_bods) in
             let eq = snd proj_bods in
             mkAppl (eq_rect, [at_type; trm1; packer; b; trm2; eq])
           in
           let proj_bod = pack_existT { index_type; packer; index; unpacked } in
           sigma, reconstruct_lambda env_proj proj_bod
         in
         sigma, ([(p1, projT1_bwd) (*; (p1_p2, id)*)], [(p1_typ, p1_typ); (p2_typ, p2_typ)])
    | CurryRecord ->
       (* accessors <-> projections *)
       let accessors =
         let (a_typ, _) = get_types c in
         let ((i, i_index), u) = destInd a_typ in
         let accessor_opts = Recordops.lookup_projections (i, i_index) in
         let args = mk_n_rels (nb_rel env_proj) in
         try
           List.map (fun a_o -> reconstruct_lambda env_proj (mkAppl ((mkConst (Option.get a_o)), args))) accessor_opts
         with _ ->
           []
       in
       let sigma, (ps, ps_to) =
         if l.is_fwd then (* accessors -> projections *)
           let sigma, lifted_projections =
             let sigma, p_bodies = prod_projections_rec env_proj lift_t sigma in
             map_state (fun p -> ret (reconstruct_lambda env_proj p)) p_bodies sigma
           in sigma, (accessors, lifted_projections)
         else (* projections -> accessors *)
           let sigma, lifted_accessors =
             map_state
               (fun a sigma ->
                 let args = shift_all (mk_n_rels (nb_rel env_proj - 1)) in
                 let sigma, app = reduce_term env sigma (mkAppl (a, snoc lift_t args)) in
                 ret (reconstruct_lambda env_proj app) sigma)
               accessors
               sigma
           in
           let sigma, projections =
             let sigma, p_bodies = prod_projections_rec env_proj (mkRel 1) sigma in
             map_state (fun p -> ret (reconstruct_lambda env_proj p)) p_bodies sigma
           in sigma, (projections, lifted_accessors)
       in
       if List.length ps = List.length ps_to then
         let sigma, ps = map2_state (fun p1 p2 -> ret (p1, p2)) ps ps_to sigma in
         sigma, (ps, [])
       else
         let _ =
           Feedback.msg_warning
             (Pp.str "Can't find record accessors; skipping an optimization")
         in sigma, ([], [])
    | SwapConstruct _ ->
       (* no projections *)
       sigma, ([], [])
  in
  let sigma, fwd_proj_rules = init c sigma in
  let sigma, bwd_proj_rules = init (reverse c) sigma in
  let proj_rules = fwd_proj_rules, bwd_proj_rules in
  sigma, { c with proj_rules }

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
  in sigma, { c with optimize_proj_id_rules } (* TODO somewhere, rewrite eq_refl in ... *)

(*
 * Define what it means to lift the identity function, since we must
 * preserve definitional equalities.
 *)
let initialize_id_rules c env sigma =
  let (a_typ, b_typ) = get_types c in
  let l = get_lifting c in
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
  let id_rules = if l.is_fwd then (id_a, id_b) else (id_b, id_a) in
  sigma, { c with id_rules }

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
      packed_constrs = Array.make 0 (mkRel 1), Array.make 0 (mkRel 1);
      constr_rules = Array.make 0 (mkRel 1), Array.make 0 (mkRel 1);
      proj_rules = ([], []), ([], []);
      optimize_proj_id_rules = [], [];
      id_rules = (mkRel 1, mkRel 1);
      cache;
      opaques
    }
  in
  let sigma, c = initialize_proj_rules c env sigma in
  let sigma, c = initialize_optimize_proj_id_rules c env sigma in
  let sigma, c = initialize_id_rules c env sigma in
  let sigma, c = initialize_elim_types c env sigma in
  let sigma, c = initialize_packed_constrs c env sigma in
  initialize_constr_rules c env sigma

