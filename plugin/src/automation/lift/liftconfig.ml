open Lifting
open Constr
open Environ
open Hofs
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
open Desugarprod
open Specialization
open Debruijn
open Substitution
open Typehofs
open Convertibility
open Ornerrors
open Hypotheses
open Declarations
open Utilities
open Desugarprod

(*
 * Lifting configuration: Includes the lifting, types, and cached rules
 * for optimizations, as well as interfaces to ask questions about
 * the configuration and some initialization code.
 *
 * This is where lifting constructors and projections live, since those
 * are configured ahead of time. Eventually, the bulk of lifting eliminators
 * may live here as well.
 *)

(* --- Convenient shorthand (TODO move/comment/remove duplicates) --- *)

let dest_sigT_type = on_red_type_default (ignore_env dest_sigT)

(* TODO move/comment *)
let convertible env t1 t2 sigma =
  if equal t1 t2 then
    sigma, true
  else
    convertible env sigma t1 t2

(* --- Datatype --- *)
       
(*
 * Lifting configuration, along with the types A and B,
 * rules for constructors and projections that are configurable by equivalence,
 * a cache for constants encountered as the algorithm traverses,
 * and a cache for the constructor rules that refolding determines.
 *)
type lift_config =
  {
    l : lifting;
    typs : types * types;
    constr_rules : types array;
    proj_rules : (constr * constr) list;
    optimize_proj_packed_rules :
      (constr -> bool) * ((constr * (constr -> constr)) list);
    cache : temporary_cache;
    opaques : temporary_cache
  }

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
                
(*
 * Determine whether a type is the type we are ornamenting from
 * That is, A when we are promoting, and B when we are forgetting
 * Return the arguments to the type if so
 *)
let is_from_with_conv conv c env typ sigma =
  let (a_typ, b_typ) = c.typs in
  if c.l.is_fwd then
    if is_or_applies a_typ typ then
      sigma, Some (unfold_args typ)
    else
      sigma, None
  else
    match c.l.orn.kind with
    | Algebraic _ -> (* TODO explain the opaque thing *)
       if is_or_applies sigT typ && not (is_opaque c sigT) then
         let packed = dummy_index env sigma (dest_sigT typ).packer in
         let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_typ)).packer in
         if equal (first_fun b_typ_packed) (first_fun packed) then
           sigma, Some (deindex c.l (unfold_args packed))
         else
           sigma, None
       else
         sigma, None
    | CurryRecord ->
       (* TODO optimize, don't do unless you need to *)
       (* TODO have this function return useful metadata, like the arguments, for all of these cases. for now let's just be slow *)
       (* v TODO common functionality w/ specialization, move somewhere common *)
       (* TODO explain the reason we need this *)
       (* TODO really should be able to reuse unification somehow... *)
       (* TODO try to work around by substituting with constant version earlier so as to avoid this *)
       let sigma, a_typ_typ = reduce_type env sigma a_typ in
       if not (isApp typ || isConst typ) then
         sigma, None
       else if arity a_typ_typ = 0 then
         branch_state
           (conv env b_typ)
           (fun _ -> ret (Some []))
           (fun _ -> ret None)
           typ
           sigma
       else if not (is_opaque c (first_fun typ)) then
         let typ_f = unwrap_definition env (first_fun typ) in
         let typ_args = unfold_args typ in
         let typ_red = mkAppl (typ_f, typ_args) in
         let sigma, typ_red = reduce_term env sigma typ_red in
         if not (is_or_applies prod typ_red) then
           sigma, None
         else
           let f = lift_to c.l in
           let f = unwrap_definition env f in
           let f_arity = arity f in
           let env_f, f_bod = zoom_lambda_term env f in
           let sigma, typ_app = reduce_type env_f sigma (mkRel 1) in
           let sigma, typ_app_red = specialize_delta_f env_f (first_fun typ_app) (unfold_args typ_app) sigma in
           let abs_args = prod_typs_rec typ_app_red in
           let conc_args = prod_typs_rec_n (shift_by f_arity typ_red) (List.length abs_args) in
           if not (List.length abs_args = List.length conc_args) then
             sigma, None
           else
             let subbed = (* TODO move some of this ... *) (* TODO may fail sometimes, do better? try to make it fail ... *)
               List.fold_right2
                 (fun abs conc -> all_eq_substs (abs, conc))
                 abs_args
                 conc_args
                 typ_app
             in
             let subbed = unshift_by f_arity subbed in
             let sigma, conv = conv env subbed typ sigma in
             sigma, Some (unfold_args subbed)
       else
         sigma, None

(*
 * Actually check is_from
 *)
let is_from = is_from_with_conv convertible

(*
 * Just get all of the unfolded arguments, skipping the check
 *)
let from_args c env trm sigma =
  Util.on_snd
    Option.get
    (is_from_with_conv (fun _ _ _ -> ret true) c env trm sigma)
                    
(* 
 * Determine whether a term has the type we are ornamenting from
 * Return the arguments to the type if so
 *)
let type_is_from c env trm sigma =
  on_red_type
    reduce_nf
    (fun env sigma typ -> is_from c env typ sigma)
    env
    sigma
    trm

(* 
 * Just return the arguments to from, assuming term has the right type,
 * skipping the check
 *)
let type_from_args c env trm sigma =
  on_red_type
    reduce_nf
    (fun env sigma typ -> from_args c env typ sigma)
    env
    sigma
    trm

(*
 * Get the map of projections for the type
 *)
let get_proj_map c = c.proj_rules

(*
 * Get the cached lifted constructors of A (which construct B)
 *)
let get_lifted_constrs c = c.constr_rules

(* --- Smart simplification --- *)

(*
 * Return true if a term is packed
 *)
let is_packed c = fst (c.optimize_proj_packed_rules)

(*
 * Determine if we can be smarter than Coq and simplify earlier
 * If yes, return how
 * Otherwise, return None
 *)
let can_reduce_now c trm =
  let _, proj_packed_map = c.optimize_proj_packed_rules in
  let optimize_proj_packed_o = (* TODO refactor/clean *)
    if (get_lifting c).is_fwd then
      try
        Some
          (List.find (fun (pr, _) -> is_or_applies pr trm) proj_packed_map)
      with _ ->
        None
    else
      None
  in
  if Option.has_some optimize_proj_packed_o then
    let _, reduce = Option.get optimize_proj_packed_o in
    Some (fun _ sigma trm -> sigma, reduce trm)
  else
    None

(* --- Initialization --- *)

(*
 * For packing constructor aguments: Pack, but only if it's B
 *)
let pack_to_typ env sigma c unpacked =
  let (_, b_typ) = c.typs in
  let l = c.l in
  let b_typ_inner =
    match l.orn.kind with
    | Algebraic _ ->
       let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_typ)).packer in
       first_fun b_typ_packed
    | _ ->
       b_typ
  in
  if on_red_type_default (ignore_env (is_or_applies b_typ_inner)) env sigma unpacked then
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
  let args = unfold_args (map_backward last_arg l trm) in
  let pack_args (sigma, args) = map_state (fun arg sigma -> pack_to_typ env sigma c arg) args sigma in
  let sigma, packed_args = map_backward pack_args l (sigma, args) in
  let sigma, typ_args = type_from_args c env trm sigma in
  let sigma, app = lift env l trm typ_args sigma in
  match l.orn.kind with
  | Algebraic _ ->
     let sigma, rec_args = filter_state (fun tr sigma -> let sigma, o = type_is_from c env tr sigma in sigma, Option.has_some o) packed_args sigma in (* TODO use result? *)
     if List.length rec_args = 0 then
       (* base case - don't bother refolding *)
       reduce_nf env sigma app
     else
       (* inductive case - refold *)
       refold l env (lift_to l) app rec_args sigma
  | CurryRecord ->
     (* no inductive cases, so don't try to refold *)
     reduce_nf env sigma app

(*
 * Wrapper around NORMALIZE
 *)
let initialize_constr_rule c env constr sigma =
  let l = get_lifting c in
  let sigma, constr_exp = expand_eta env sigma constr in
  let (env_c_b, c_body) = zoom_lambda_term env constr_exp in
  let c_body = reduce_stateless reduce_term env_c_b sigma c_body in
  let sigma, to_lift =
    if l.is_fwd then
      sigma, c_body
    else
      match l.orn.kind with
      | Algebraic (_, off) ->
         pack env_c_b l c_body sigma
      | CurryRecord ->
         sigma, c_body
  in
  let sigma, lifted =
    match l.orn.kind with
    | Algebraic _ ->
       lift_constr env_c_b sigma c to_lift
    | CurryRecord ->
       if l.is_fwd then
         lift_constr env_c_b sigma c to_lift
       else
         (* We searched backwards, so we just use that (TODO explain/clean) *)
         sigma, to_lift
  in sigma, reconstruct_lambda_n env_c_b lifted (nb_rel env)

(*
 * Run NORMALIZE for all constructors, so we can cache the result
 *)
let initialize_constr_rules env sigma c =
  let (a_typ, b_typ) = get_types c in
  match c.l.orn.kind with
  | Algebraic _ ->
     let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_typ)).packer in
     let b_typ_inner = first_fun b_typ_packed in
     let ((i, i_index), u) = destInd (directional c.l a_typ b_typ_inner) in
     let mutind_body = lookup_mind i env in
     let ind_bodies = mutind_body.mind_packets in
     let ind_body = ind_bodies.(i_index) in
     map_state_array
       (initialize_constr_rule c env)
       (Array.mapi
          (fun c_index _ -> mkConstructU (((i, i_index), c_index + 1), u))
          ind_body.mind_consnames)
       sigma
  | CurryRecord ->
     let ((i, i_index), u) = destInd a_typ in
     let constr = mkConstructU (((i, i_index), 1), u) in
     let sigma, c_rule = initialize_constr_rule c env constr sigma in
     sigma, Array.make 1 c_rule
                       
(* 
 * Initialize the rules for lifting projections
 * This is COHERENCE, but cached
 *)
let initialize_proj_rules env sigma c =
  let l = get_lifting c in
  let lift_f = unwrap_definition env (lift_to l) in
  let env_proj = zoom_env zoom_lambda_term env lift_f in
  let t = mkRel 1 in
  let sigma, typ_args = type_from_args c env_proj t sigma in
  let sigma, lift_t = lift env_proj l t typ_args sigma in
  match l.orn.kind with
  | Algebraic (indexer, _) ->
     if l.is_fwd then (* indexer -> projT1 *)
       let sigma, b_sig_typ = Util.on_snd dest_sigT (reduce_type env_proj sigma lift_t) in
       let p1 = reconstruct_lambda env_proj (project_index b_sig_typ lift_t) in
       sigma, [(indexer, p1)]
     else (* projT1 -> indexer, projT2 -> id *)
       let args = shift_all (mk_n_rels (nb_rel env_proj - 1)) in
       let p1 = reconstruct_lambda env_proj (mkAppl (indexer, snoc lift_t args)) in
       let p2 = reconstruct_lambda env_proj lift_t in
       sigma, [(projT1, p1); (projT2, p2)]
  | CurryRecord ->
     (* accessors <-> projections *)
     let rec build arg sigma = (* TODO merge w/ common build in lift_case, or get projections and use those there *)
       try
         let sigma, arg_typ_prod = dest_prod_type env_proj arg sigma in
         let arg_fst = prod_fst_elim arg_typ_prod arg in
         let arg_snd = prod_snd_elim arg_typ_prod arg in
         let sigma, args_tl = build arg_snd sigma in
         sigma, arg_fst :: args_tl
       with _ ->
         sigma, [arg]
     in
     let accessors =
       let (a_typ, _) = get_types c in
       let ((i, i_index), u) = destInd a_typ in
       let accessor_opts = Recordops.lookup_projections (i, i_index) in
       try
         List.map (fun a_o -> mkConst (Option.get a_o)) accessor_opts
       with _ ->
         []
     in
     let sigma, (ps, ps_to) =
       if l.is_fwd then (* accessors -> projections *)
         let sigma, lifted_projections =
           let sigma, p_bodies = build lift_t sigma in
           map_state (fun p -> ret (reconstruct_lambda env_proj p)) p_bodies sigma
         in sigma, (accessors, lifted_projections)
       else (* projections -> accessors *)
         let sigma, lifted_accessors =
           map_state
             (fun a ->
               let args = shift_all (mk_n_rels (nb_rel env_proj - 1)) in
               let app = mkAppl (a, snoc lift_t args) in
               ret (reconstruct_lambda env_proj app))
             accessors
             sigma
         in
         let sigma, projections =
           let sigma, p_bodies = build (mkRel 1) sigma in
           map_state (fun p -> ret (reconstruct_lambda env_proj p)) p_bodies sigma
         in sigma, (projections, lifted_accessors)
     in
     if List.length ps = List.length ps_to then
       map2_state (fun p1 p2 -> ret (p1, p2)) ps ps_to sigma
     else
       let _ =
         Feedback.msg_warning
           (Pp.str "Can't find record accessors; skipping an optimization")
       in sigma, []

(* TODO comment/explain: we can sometimes be smarter than coq's reduction
  TODO unify some infrastructure with proj rules and is_proj? *)
(* TODO clean up a lot *)
(* TODO note this takes in lifted f, args and then decides what to do *)
let initialize_optimize_proj_packed_rules c =
  match (get_lifting c).orn.kind with
  | Algebraic (_, _) ->
     let proj1_rule = (fun a -> (dest_existT a).index) in
     let proj2_rule = (fun a -> (dest_existT a).unpacked) in
     is_or_applies existT, [(projT1, proj1_rule); (projT2, proj2_rule)]
  | CurryRecord ->
     let proj1_rule = (fun a -> (dest_pair a).Produtils.trm1) in
     let proj2_rule = (fun a -> (dest_pair a).Produtils.trm2) in
     is_or_applies pair, [(Desugarprod.fst_elim (), proj1_rule); (Desugarprod.snd_elim (), proj2_rule)]
                           
(* Initialize the lift_config *)
let initialize_lift_config env l typs ignores sigma =
  let cache = initialize_local_cache () in
  let opaques = initialize_local_cache () in
  List.iter (fun opaque -> cache_local opaques opaque opaque) ignores;
  let c = { l ; typs ; constr_rules = Array.make 0 (mkRel 1) ; proj_rules = []; optimize_proj_packed_rules = ((fun _ -> false), []); cache ; opaques } in
  let sigma, constr_rules = initialize_constr_rules env sigma c in
  let sigma, proj_rules = initialize_proj_rules env sigma c in
  let optimize_proj_packed_rules = initialize_optimize_proj_packed_rules c in
  sigma, { c with constr_rules; proj_rules; optimize_proj_packed_rules }
    
(* --- Modifying the configuration --- *)

let reverse c = { c with l = flip_dir c.l }

let zoom c =
  match c.l.orn.kind with
  | Algebraic (indexer, (ib_typ, off)) ->
     let orn = { c.l.orn with kind = Algebraic (indexer, (shift ib_typ, off)) } in
     let l = { c.l with orn } in
     let typs = map_tuple shift c.typs in
     { c with l; typs }
  | _ ->
     c
