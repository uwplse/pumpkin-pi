(*
 * Core lifting algorithm
 *)

open Util
open Constr
open Environ
open Zooming
open Lifting
open Debruijn
open Utilities
open Indexing
open Hypotheses
open Names
open Caching
open Declarations
open Specialization
open Inference
open Typehofs
open Indutils
open Apputils
open Sigmautils
open Reducers
open Envutils
open Funutils
open Constutils
open Stateutils
open Hofs
open Desugarprod
open Substitution
open Convertibility
open Ornerrors
open Promotion
open Evd

(* --- Convenient shorthand --- *)

let dest_sigT_type = on_red_type_default (ignore_env dest_sigT)
let dest_prod_type env sigma trm =
  let sigma, typ = reduce_type env sigma trm in
  let typ_f = unwrap_definition env (first_fun typ) in
  let typ_args = unfold_args typ in
  let typ_red = mkAppl (typ_f, typ_args) in
  let sigma, typ_red = reduce_term env sigma typ_red in
  ignore_env dest_prod env sigma typ_red

let convertible env t1 t2 sigma =
  if equal t1 t2 then
    sigma, true
  else
    convertible env sigma t1 t2

(* --- Internal lifting configuration --- *)

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
    proj_rules : types array;
    optimize_proj_packed_rules : (constr * (lift_config -> env -> constr -> constr array -> (lift_config, constr) transformer_with_env -> evar_map -> types state)) list; (* TODO clean type *)
    cache : temporary_cache;
    opaques : temporary_cache
  }

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

(* --- Index/deindex functions --- *)

let index l =
  match l.orn.kind with
  | Algebraic (_, (_, off)) ->
     insert_index off
  | _ ->
     raise NotAlgebraic

let deindex l =
  match l.orn.kind with
  | Algebraic (_, (_, off)) ->
     remove_index off
  | _ ->
     raise NotAlgebraic

(* --- Recovering types from ornaments --- *)

(*
 * Get the types A, B, and IB from the ornament
 *)
let typs_from_orn l env sigma =
  let (a_i_t, b_i_t) = on_red_type_default (ignore_env promotion_type_to_types) env sigma l.orn.promote in
  let a_t = first_fun a_i_t in
  match l.orn.kind with
  | Algebraic _ ->
     let b_t = zoom_sig b_i_t in
     let i_b_t = (dest_sigT b_i_t).index_type in
     (a_t, b_t, Some i_b_t)
  | CurryRecord ->
     let b_t = first_fun b_i_t in
     (a_t, b_t, None)

(* --- Premises --- *)

(*
 * Determine whether a type is the type we are ornamenting from
 * That is, A when we are promoting, and B when we are forgetting
 *
 * TODO it's more like e_is_from with pms/indices
 *)
let is_from conv c env sigma typ =
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
         if equal b_typ (first_fun packed) then
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
 * Determine whether a term has the type we are ornamenting from
 *)
let type_is_from conv c = on_red_type reduce_nf (is_from conv c)

(* Premises for LIFT-CONSTR *) (* TODO clean *)
let is_packed_constr c env sigma trm =
  let right_type trm sigma = type_is_from convertible c env sigma trm in
  match kind trm with
  | Construct (((_, _), i), _)  ->
     let sigma, typ_args_o = right_type trm sigma in
     if Option.has_some typ_args_o then
       sigma, Some (i, [])
     else
       sigma, None
  | App (f, args) ->
     if is_opaque c (first_fun f) then
       sigma, None
     else if c.l.is_fwd then
       (match kind f with
        | Construct (((_, _), i), _) ->
           let sigma, typ_args_o = right_type trm sigma in
           if Option.has_some typ_args_o then
             sigma, Some (i, unfold_args trm)
           else
             sigma, None
        | _ ->
           sigma, None)
     else
       (match c.l.orn.kind with
        | Algebraic _ ->
           if equal existT f then (* TODO why here is f OK, but in other case we need first_fun? eta? *)
             let sigma_right, args_opt = right_type trm sigma in
             if Option.has_some args_opt then
               (* TODO what does this exist for? *)
               (* TODO do we want to send back the typ args too? *)
               let last_arg = last (Array.to_list args) in
               if isApp last_arg then
                 (match kind (first_fun last_arg) with
                  | Construct (((_, _), i), _) ->
                     sigma_right, Some (i, unfold_args last_arg)
                  | _ ->
                     sigma, None)
               else
                 sigma, None
             else
               sigma, None
           else
             sigma, None
        | CurryRecord ->
           if equal pair (first_fun trm) then
             let sigma_right, pms_opt = right_type trm sigma in
             if Option.has_some pms_opt then
               let sigma = sigma_right in
               let p = dest_pair trm in
               let (a_typ, _) = c.typs in
               let c = mkConstruct (fst (destInd a_typ), 1) in
               let sigma, c_typ = reduce_type env sigma c in
               let c_arity = arity c_typ in
               let rec build_args p sigma n = (* TODO clean, move to optimization *)
                 let trm1 = p.Produtils.trm1 in
                 if n <= 2 then
                   let trm2 = p.Produtils.trm2 in
                   sigma, [trm1; trm2]
                 else
                   if applies pair p.Produtils.trm2 then
                     let sigma, trm2s = build_args (dest_pair p.Produtils.trm2) sigma (n - 1) in
                     sigma, trm1 :: trm2s
                   else
                     let sigma_typ, typ2 = reduce_type env sigma p.Produtils.trm2 in
                     if applies prod typ2 then (* TODO should just be able to use number instead of type-checking every time *)
                       let prod_app = dest_prod typ2 in
                       let typ1 = prod_app.Produtils.typ1 in
                       let typ2 = prod_app.Produtils.typ2 in
                       let trm2_pair = Produtils.{ typ1; typ2; trm1 = prod_fst_elim prod_app p.Produtils.trm2; trm2 = prod_snd_elim prod_app p.Produtils.trm2 } in
                       let sigma, trm2s = build_args trm2_pair sigma (n - 1) in
                       sigma, trm1 :: trm2s
                     else
                       let trm2 = p.Produtils.trm2 in
                       sigma, [trm1; trm2]
               in
               let pms = Option.get pms_opt in
               let sigma, args = build_args p sigma (c_arity - List.length pms) in
               sigma, Some (1, List.append pms args)
             else
               sigma, None
           else
             sigma, None)
  | _ ->
     sigma, None

(* Premises for LIFT-PACK *)
let is_pack c env sigma trm =
  let right_type = type_is_from convertible c env sigma in
  if c.l.is_fwd then
    if isRel trm then
      (* pack *)
      Util.on_snd Option.has_some (right_type trm)
    else
      sigma, false
  else
    match c.l.orn.kind with
    | Algebraic (_, _) ->
       (match kind trm with
        | App (f, args) ->
           if equal existT f then
             (* unpack *)
             Util.on_snd Option.has_some (right_type trm)
           else
             sigma, false
        | _ ->
           sigma, false)
    | CurryRecord ->
       (* taken care of by constructor rule *)
       sigma, false

(* Auxiliary function for premise for LIFT-PROJ *)
let check_is_proj c env trm proj_is =
  let right_type = type_is_from convertible c in
  match kind trm with
  | App _ | Const _ ->
     let f = first_fun trm in
     let rec check_is_proj_i i proj_is =
       match proj_is with
       | proj_i :: tl ->
          let env_proj_b, proj_b = zoom_lambda_term env proj_i in
          let proj_i_f = first_fun proj_b in
          branch_state
            (convertible env proj_i_f)
            (fun _ sigma ->
              let sigma, trm_eta = expand_eta env sigma trm in
              let env_b, b = zoom_lambda_term env trm_eta in
              let args = unfold_args b in
              if List.length args = 0 then
                check_is_proj_i (i + 1) tl sigma
              else
                if c.l.orn.kind = CurryRecord && not c.l.is_fwd then
                  (* TODO hacky; clean/refactor common *)
                  let rec get_arg j args =
                    let a = last args in
                    if j = 0 then
                      a
                    else
                      get_arg (j - 1) (unfold_args a)
                  in
                  let j = if i = List.length proj_is then i - 1 else i in
                  (* ^ TODO why not length - 1? confused ... *)
                  try
                    let a = get_arg j args in
                    let sigma_right, typ_args_o = right_type env_b sigma a in
                    if Option.has_some typ_args_o then
                      let typ_args = Option.get typ_args_o in
                      let p_app = mkAppl (proj_i, snoc a typ_args) in
                      branch_state (* TODO check w/ pms *)
                        (convertible env_b p_app)
                        (fun _ -> ret (Some (a, i, typ_args, trm_eta)))
                        (fun _ -> check_is_proj_i (i + 1) tl)
                        b
                        sigma
                    else
                      check_is_proj_i (i + 1) tl sigma       
                  with _ ->
                    check_is_proj_i (i + 1) tl sigma
                else
                  let a = last args in
                  let sigma_right, typ_args_o = right_type env_b sigma a in
                  if Option.has_some typ_args_o then
                    ret (Some (a, i, Option.get typ_args_o, trm_eta)) sigma_right
                  else
                    check_is_proj_i (i + 1) tl sigma)
            (fun _ -> check_is_proj_i (i + 1) tl)
            f
       | _ ->
          ret None
     in check_is_proj_i 0 proj_is
  | _ ->
     ret None

(* Premises for LIFT-PROJ *)
let is_proj c env trm =
  if Array.length c.proj_rules = 0 then
    ret None
  else
    match c.l.orn.kind with
    | Algebraic (indexer, _) ->
       if c.l.is_fwd then
         check_is_proj c env trm [indexer]
       else
         check_is_proj c env trm [projT1; projT2]
    | CurryRecord ->
       if c.l.is_fwd then
         try
           (* TODO unify w/ stuff in initialize_proj_rules *)
           let (a_typ, _) = c.typs in
           let ((i, i_index), u) = destInd a_typ in
           let p_opts = Recordops.lookup_projections (i, i_index) in
           let ps = List.map (fun p_opt -> mkConst (Option.get p_opt)) p_opts in
           if not (Array.length c.proj_rules = List.length ps) then
             ret None
           else
             check_is_proj c env trm ps
         with _ ->
           Feedback.msg_warning
             (Pp.str "Can't find record accessors; skipping an optimization");
           ret None
       else
         let lift_f = unwrap_definition env (lift_to c.l) in
         let env_proj = zoom_env zoom_lambda_term env lift_f in
         let rec build arg sigma = (* TODO merge w/ common build elsewhere *)
           try
             let arg_typ_prod = dest_prod_type env_proj sigma arg in
             let arg_fst = prod_fst_elim arg_typ_prod arg in
             let arg_snd = prod_snd_elim arg_typ_prod arg in
             let sigma, args_tl = build arg_snd sigma in
             sigma, arg_fst :: args_tl
           with _ ->
             sigma, [arg]
         in
         bind
           (build (mkRel 1))
           (fun p_bodies ->
             let ps =
               List.map
                 (fun p -> reconstruct_lambda_n env_proj p (nb_rel env))
                 p_bodies
             in
             if not (Array.length c.proj_rules = List.length ps) then
               ret None
             else
               check_is_proj c env trm ps)

(*
 * Premises for LIFT-ELIM
 * For optimization, if true, return the eta-expanded term
 *
 * TODO clean
 *)
let is_eliminator c env trm sigma =
  let (a_typ, b_typ) = c.typs in
  let b_typ =
    if (not c.l.is_fwd) && c.l.orn.kind = CurryRecord then
      prod
    else
      b_typ
  in
  let f = first_fun trm in
  match kind f with
  | Const (k, u) ->
     let maybe_ind = inductive_of_elim env (k, u) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       let is_elim = equal (mkInd (ind, 0)) (directional c.l a_typ b_typ) in
       if is_elim then
         let sigma, trm_eta = expand_eta env sigma trm in
         if (not c.l.is_fwd) && c.l.orn.kind = CurryRecord then
           let env_elim, trm_b = zoom_lambda_term env trm_eta in
           let sigma, trm_elim = deconstruct_eliminator env_elim sigma trm_b in
           let (final_args, post_args) = take_split 1 trm_elim.final_args in
           let sigma, is_from = type_is_from convertible c env_elim sigma (List.hd final_args) in
           if Option.has_some is_from then
             sigma, Some trm_eta
           else
             sigma, None
         else
           sigma, Some trm_eta
       else
         sigma, None
     else
       sigma, None
  | _ ->
     sigma, None

(* --- Configuring the constructor liftings --- *)
       
(*
 * For packing constructor aguments: Pack, but only if it's B
 *)
let pack_to_typ env sigma c unpacked =
  let (_, b_typ) = c.typs in
  if on_red_type_default (ignore_env (is_or_applies b_typ)) env sigma unpacked then
    match c.l.orn.kind with
    | Algebraic (_, off) ->
       pack env c.l unpacked sigma
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
  let sigma, typ_args_o = type_is_from (fun _ _ _ -> ret true) c env sigma trm in
  let typ_args = Option.get typ_args_o in
  let sigma, app = lift env l trm typ_args sigma in
  match l.orn.kind with
  | Algebraic _ ->
     let sigma, rec_args = filter_state (fun tr sigma -> let sigma, o = type_is_from convertible c env sigma tr in sigma, Option.has_some o) packed_args sigma in (* TODO use result? *)
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
  let sigma, constr_exp = expand_eta env sigma constr in
  let (env_c_b, c_body) = zoom_lambda_term env constr_exp in
  let c_body = reduce_stateless reduce_term env_c_b sigma c_body in
  let sigma, to_lift =
    if c.l.is_fwd then
      sigma, c_body
    else
      match c.l.orn.kind with
      | Algebraic (_, off) ->
         pack env_c_b c.l c_body sigma
      | CurryRecord ->
         sigma, c_body
  in
  let sigma, lifted =
    match c.l.orn.kind with
    | Algebraic _ ->
       lift_constr env_c_b sigma c to_lift
    | CurryRecord ->
       if c.l.is_fwd then
         lift_constr env_c_b sigma c to_lift
       else
         (* We searched backwards, so we just use that (TODO explain/clean) *)
         sigma, to_lift
  in sigma, reconstruct_lambda_n env_c_b lifted (nb_rel env)

(*
 * Run NORMALIZE for all constructors, so we can cache the result
 *)
let initialize_constr_rules env sigma c =
  let (a_typ, b_typ) = c.typs in
  match c.l.orn.kind with
  | Algebraic _ ->
    let ((i, i_index), u) = destInd (directional c.l a_typ b_typ) in
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
  let l = c.l in
  let lift_f = unwrap_definition env (lift_to l) in
  let env_proj = zoom_env zoom_lambda_term env lift_f in
  let t = mkRel 1 in
  let sigma, typ_args_o = type_is_from (fun _ _ _ -> ret true) c env_proj sigma t in (* TODO refactor these *)
  let typ_args = Option.get typ_args_o in
  let sigma, lift_t = lift env_proj l t typ_args sigma in
  match l.orn.kind with
  | Algebraic (indexer, _) ->
     if l.is_fwd then (* indexer -> projT1 *)
       let sigma, b_sig_typ = Util.on_snd dest_sigT (reduce_type env_proj sigma lift_t) in
       let p1 = reconstruct_lambda env_proj (project_index b_sig_typ lift_t) in
       sigma, Array.make 1 p1
     else (* projT1 -> indexer, projT2 -> id *)
       let args = shift_all (mk_n_rels (nb_rel env_proj - 1)) in
       let p1 = reconstruct_lambda env_proj (mkAppl (indexer, snoc lift_t args)) in
       let p2 = reconstruct_lambda env_proj lift_t in
       sigma, Array.of_list [p1; p2]
  | CurryRecord ->
     if l.is_fwd then (* accessors -> projections *)
       let rec build arg sigma = (* TODO merge w/ common build in lift_case, or get projections and use those there *)
         try
           let arg_typ_prod = dest_prod_type env_proj sigma arg in
           let arg_fst = prod_fst_elim arg_typ_prod arg in
           let arg_snd = prod_snd_elim arg_typ_prod arg in
           let sigma, args_tl = build arg_snd sigma in
           sigma, arg_fst :: args_tl
         with _ ->
           sigma, [arg]
       in
       let sigma, p_bodies = build lift_t sigma in
       map_state_array (fun p -> ret (reconstruct_lambda env_proj p)) (Array.of_list p_bodies) sigma
     else (* projections -> accessors *)
       let (a_typ, _) = c.typs in
       let ((i, i_index), u) = destInd a_typ in
       try
         let p_opts = Recordops.lookup_projections (i, i_index) in
         map_state_array
           (fun p ->
             let f = mkConst p in
             let args = shift_all (mk_n_rels (nb_rel env_proj - 1)) in
             let app = mkAppl (f, snoc lift_t args) in
             ret (reconstruct_lambda env_proj app))
           (Array.of_list (List.map Option.get p_opts))
           sigma
       with _ ->
         Feedback.msg_warning
           (Pp.str "Can't find record accessors; skipping an optimization");
         sigma, Array.make 0 t
  

(* TODO comment/explain: we can sometimes be smarter than coq's reduction
  TODO unify some infrastructure with proj rules and is_proj? *)
(* TODO clean up a lot, especially recursive lifting here which is gross, and performance benefits are marginal if any *)
let initialize_optimize_proj_packed_rules c =
  (* TODO comment/move/clean/etc *)
  let common_proj_rule is_packed project c env f args lift_rec sigma =
    let sigma, args' = map_rec_args lift_rec env sigma c args in
    let arg' = last (Array.to_list args') in
    let arg'' = reduce_stateless reduce_term env sigma arg' in
    if is_packed arg'' then
      (sigma, project arg'')
    else
      let sigma, f' = lift_rec env sigma c f in
      (sigma, mkApp (f', args'))
  in (* TODO refactor/clean/make proper map *)
  match c.l.orn.kind with
  | Algebraic (_, _) ->
     let proj_rule = common_proj_rule (is_or_applies existT) in
     let proj1_rule = proj_rule (fun a -> (dest_existT a).index) in
     let proj2_rule = proj_rule (fun a -> (dest_existT a).unpacked) in
     [(projT1, proj1_rule); (projT2, proj2_rule)]
  | CurryRecord ->
     let proj_rule = common_proj_rule (is_or_applies pair) in
     let proj1_rule = proj_rule (fun a -> (dest_pair a).Produtils.trm1) in
     let proj2_rule = proj_rule (fun a -> (dest_pair a).Produtils.trm2) in
     [(Desugarprod.fst_elim (), proj1_rule); (Desugarprod.snd_elim (), proj2_rule)]
                           
(* Initialize the lift_config *)
let initialize_lift_config env sigma l typs ignores =
  let cache = initialize_local_cache () in
  let opaques = initialize_local_cache () in
  List.iter (fun opaque -> cache_local opaques opaque opaque) ignores;
  let c = { l ; typs ; constr_rules = Array.make 0 (mkRel 1) ; proj_rules = Array.make 0 (mkRel 1); optimize_proj_packed_rules = []; cache ; opaques } in
  let sigma, constr_rules = initialize_constr_rules env sigma c in
  let sigma, proj_rules = initialize_proj_rules env sigma c in
  let optimize_proj_packed_rules = initialize_optimize_proj_packed_rules c in
  sigma, { c with constr_rules; proj_rules; optimize_proj_packed_rules }

(* --- Lifting the induction principle --- *)

(*
 * This implements the rules for lifting the eliminator.
 * The rules here look a bit different because of de Bruijn indices,
 * some optimizations, and non-primitive eliminators.
 *)

(*
 * In LIFT-ELIM, this is what gets a or the projection of b
 * The one difference is that there are extra arguments because of
 * non-primitve eliminators, and also parameters
 *)
let lift_elim_args env sigma c npms args =
  let l = c.l in
  match l.orn.kind with
  | Algebraic (indexer, (ib_typ, off)) ->
     let arg = map_backward last_arg l (last args) in
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let sigma, lifted_arg = lift env l arg typ_args sigma in
     let value_off = List.length args - 1 in
     let orn = { l.orn with kind = Algebraic (indexer, (ib_typ, off - npms)) } in (* TODO how to adjust ib_typ? *)
     let l = { l with orn } in (* no parameters here *)
     if l.is_fwd then
       (* project and index *)
       let b_sig = lifted_arg in
       let b_sig_typ = dest_sigT_type env sigma b_sig in
       let i_b = project_index b_sig_typ b_sig in
       let b = project_value b_sig_typ b_sig in
       sigma, index l i_b (reindex value_off b args)
     else
       (* don't project and deindex *)
       let a = lifted_arg in
       sigma, deindex l (reindex value_off a args)
  | CurryRecord ->
     let arg = last args in
     let sigma, typ_args_o = type_is_from (fun _ _ _ -> ret true) c env sigma arg in
     let typ_args = Option.get typ_args_o in
     let sigma, lifted_arg = lift env l arg typ_args sigma in
     sigma, [lifted_arg]

(*
 * MOTIVE
 *)
let lift_motive env sigma c npms parameterized_elim p =
  let l = c.l in
  let sigma, parameterized_elim_type = reduce_type env sigma parameterized_elim in
  let (_, p_to_typ, _) = destProd parameterized_elim_type in
  let env_p_to = zoom_env zoom_product_type env p_to_typ in
  let nargs = new_rels2 env_p_to env in
  let p = shift_by nargs p in
  let args = mk_n_rels nargs in
  let sigma, arg =
    map_backward
      (fun (sigma, t) -> pack env_p_to (flip_dir l) t sigma)
      (flip_dir l)
      (sigma, last args)
  in
  let sigma, typ_args_o = type_is_from (fun _ _ _ -> ret true) { c with l = flip_dir l } env_p_to sigma arg in
  let typ_args = Option.get typ_args_o in
  let sigma, lifted_arg = lift env_p_to (flip_dir l) arg typ_args sigma in
  let args =
    match l.orn.kind with
    | Algebraic (indexer, (ib_typ, off)) ->
       let value_off = nargs - 1 in
       let orn = { l.orn with kind = Algebraic (indexer, (ib_typ, off - npms)) } in (* TODO how to adjust ib_typ? *)
       let l = { l with orn } in (* no parameters here *)
       if l.is_fwd then
         (* forget packed b to a, don't project, and deindex *)
         let a = lifted_arg in
         deindex l (reindex value_off a args)
       else
         (* promote a to packed b, project, and index *)
         let b_sig = lifted_arg in
         let b_sig_typ = dest_sigT_type env_p_to sigma b_sig in
         let i_b = project_index b_sig_typ b_sig in
         let b = project_value b_sig_typ b_sig in
         index l i_b (reindex value_off b args)
    | CurryRecord ->
       [lifted_arg]
  in
  let p_app = reduce_stateless reduce_term env_p_to sigma (mkAppl (p, args)) in
  sigma, reconstruct_lambda_n env_p_to p_app (nb_rel env)

(*
 * The argument rules for lifting eliminator cases in the promotion direction.
 * Note that since we save arguments and reduce at the end, this looks a bit
 * different, and the call to new is no longer necessary.
 *)
let promote_case_args env sigma c args =
  let (_, b_typ) = c.typs in
  let rec lift_args sigma args i_b =
    match args with
    | n :: tl ->
       if equal n i_b then
         (* DROP-INDEX *)
         Util.on_snd
           (fun tl -> shift n :: tl)
           (lift_args sigma (shift_all tl) i_b)
       else
         let sigma, t = reduce_type env sigma n in
         if is_or_applies b_typ t then
           (* FORGET-ARG *)
           match c.l.orn.kind with
           | Algebraic (_, (_, off)) ->
              let sigma, n =
                map_backward
                  (fun (sigma, t) -> pack env (flip_dir c.l) t sigma)
                  (flip_dir c.l)
                  (sigma, n)
              in 
              let sigma, typ_args_o = type_is_from (fun _ _ _ -> ret true) { c with l = flip_dir c.l } env sigma n in
              let typ_args = Option.get typ_args_o in
              let sigma, a = lift env (flip_dir c.l) n typ_args sigma in
              Util.on_snd
                (fun tl -> a :: tl)
                (lift_args sigma tl (get_arg off t))
           | _ ->
              raise NotAlgebraic
         else
           (* ARG *)
           Util.on_snd (fun tl -> n :: tl) (lift_args sigma tl i_b)
    | _ ->
       (* CONCL in inductive case *)
       sigma, []
  in lift_args sigma args (mkRel 0)

(*
 * The argument rules for lifting eliminator cases in the forgetful direction.
 * Note that since we save arguments and reduce at the end, this looks a bit
 * different, and the call to new is no longer necessary.
 *)
let forget_case_args env_c_b env sigma c args =
  let (_, b_typ) = c.typs in
  let rec lift_args sigma args (i_b, proj_i_b) =
    match args with
    | n :: tl ->
       if equal n i_b then
         (* ADD-INDEX *)
         Util.on_snd
           (fun tl -> proj_i_b :: tl)
           (lift_args sigma (unshift_all tl) (i_b, proj_i_b))
       else
         let sigma, t = reduce_type env_c_b sigma n in
         if is_or_applies b_typ t then
           (* PROMOTE-ARG *)
           match c.l.orn.kind with
           | Algebraic (_, (_, off)) ->
              let sigma, n =
                map_backward
                  (fun (sigma, t) -> pack env (flip_dir c.l) t sigma)
                  (flip_dir c.l)
                  (sigma, n)
              in 
              let sigma, typ_args_o = type_is_from (fun _ _ _ -> ret true) { c with l = flip_dir c.l } env sigma n in
              let typ_args = Option.get typ_args_o in
              let sigma, b_sig = lift env (flip_dir c.l) n typ_args sigma in
              let b_sig_typ = dest_sigT_type env sigma b_sig in
              let proj_b = project_value b_sig_typ b_sig in
              let proj_i_b = project_index b_sig_typ b_sig in
              Util.on_snd
                (fun tl -> proj_b :: tl)
                (lift_args sigma tl (get_arg off t, proj_i_b))
           | _ ->
              raise NotAlgebraic
         else
           (* ARG *)
           Util.on_snd
             (fun tl -> n :: tl)
             (lift_args sigma tl (i_b, proj_i_b))
    | _ ->
       (* CONCL in inductive case *)
       sigma, []
  in lift_args sigma args (mkRel 0, mkRel 0)

(* Common wrapper function for both directions *)
let lift_case_args env_c_b env sigma c args =
  let lifter =
    if c.l.is_fwd then
      promote_case_args
    else
      forget_case_args env_c_b
  in Util.on_snd List.rev (lifter env sigma c (List.rev args))

(*
 * CASE
 *)
let lift_case env c p c_elim constr sigma =
  let (a_typ, b_typ) = c.typs in
  let to_typ = directional c.l b_typ a_typ in
  let sigma, c_eta = expand_eta env sigma constr in
  let sigma, c_elim_type = reduce_type env sigma c_elim in
  let (_, to_c_typ, _) = destProd c_elim_type in
  match c.l.orn.kind with
  | Algebraic _ ->
     let nihs = num_ihs env sigma to_typ to_c_typ in
     if nihs = 0 then
       (* base case *)
       sigma, constr
     else
       (* inductive case---need to get the arguments *)
       let env_c = zoom_env zoom_product_type env to_c_typ in
       let nargs = new_rels2 env_c env in
       let c_eta = shift_by nargs c_eta in
       let (env_c_b, c_body) = zoom_lambda_term env_c c_eta in
       let (c_f, c_args) = destApp c_body in
       let split_i = if c.l.is_fwd then nargs - nihs else nargs + nihs in
       let (c_args, b_args) = take_split split_i (Array.to_list c_args) in
       let c_args = unshift_all_by (List.length b_args) c_args in
       let sigma, args = lift_case_args env_c_b env_c sigma c c_args in
       let f = unshift_by (new_rels2 env_c_b env_c) c_f in
       let body = reduce_stateless reduce_term env_c sigma (mkAppl (f, args)) in
       sigma, reconstruct_lambda_n env_c body (nb_rel env)
  | CurryRecord ->
     (* TODO explain *)
     let env_c = zoom_env zoom_product_type env to_c_typ in
     let nargs = new_rels2 env_c env in
     let c_eta = shift_by nargs c_eta in
     let (env_c_b, c_body) = zoom_lambda_term env_c c_eta in
     let (c_f, _) = destApp c_body in
     let args = mk_n_rels nargs in
     let sigma, args = (* TODO make a function *)
       if c.l.is_fwd then
         let c_args, b_args = take_split 2 args in
         let rec build arg sigma =
           let sigma, arg_typ = reduce_type env_c sigma arg in
           if equal (first_fun arg_typ) prod then
             let arg_typ_prod = dest_prod arg_typ in
             let arg_fst = prod_fst_elim arg_typ_prod arg in
             let arg_snd = prod_snd_elim arg_typ_prod arg in
             let sigma, args_tl = build arg_snd sigma in
             sigma, arg_fst :: args_tl
           else
             sigma, [arg]
         in
         let sigma, args_tl = build (List.hd (List.tl c_args)) sigma in
         sigma, List.append (List.hd c_args :: args_tl) b_args
       else
         let ((i, i_n), _) = destInd to_typ in
         let c = mkConstruct ((i, i_n), 1) in
         let sigma, c_typ = reduce_type env_c sigma c in
         let pms = all_but_last (unfold_args c_elim) in
         let nargs = arity c_typ in
         let c_args, b_args = take_split (nargs - List.length pms) args in
         let rec build args sigma =
           match args with
           | trm1 :: (h :: tl) ->
              let sigma, typ1 = infer_type env_c sigma trm1 in
              let sigma, trm2 = build (h :: tl) sigma in
              let sigma, typ2 = infer_type env_c sigma trm2 in
              sigma, apply_pair Produtils.{ typ1; typ2; trm1; trm2 }
           | h :: tl ->
              sigma, h
           | _ ->
              failwith "bad arguments passed to build; please report bug"
         in
         let sigma, arg_pair = build (List.tl c_args) sigma in
         sigma, List.append [List.hd c_args; arg_pair] b_args
     in
     let f = unshift_by (new_rels2 env_c_b env_c) c_f in
     let body = reduce_stateless reduce_term env_c sigma (mkAppl (f, args)) in
     sigma, reconstruct_lambda_n env_c body (nb_rel env)

(* Lift cases *)
let lift_cases env c p p_elim cs =
  bind
    (fold_left_state
       (fun (p_elim, cs) constr sigma ->
         let sigma, constr = lift_case env c p p_elim constr sigma in
         let p_elim = mkAppl (p_elim, [constr]) in
         sigma, (p_elim, snoc constr cs))
       (p_elim, [])
       cs)
    (fun (_, cs) -> ret cs)

(*
 * LIFT-ELIM steps before recursing into the rest of the algorithm
 *)
let lift_elim env sigma c trm_app =
  let (a_t, b_t) = c.typs in
  let to_typ = directional c.l b_t a_t in
  match c.l.orn.kind with
  | Algebraic _ ->
     let npms = List.length trm_app.pms in
     let elim = type_eliminator env (fst (destInd to_typ)) in
     let param_elim = mkAppl (elim, trm_app.pms) in
     let sigma, p = lift_motive env sigma c npms param_elim trm_app.p in
     let p_elim = mkAppl (param_elim, [p]) in
     let sigma, cs = lift_cases env c p p_elim trm_app.cs sigma in
     let sigma, final_args = lift_elim_args env sigma c npms trm_app.final_args in
     sigma, apply_eliminator { trm_app with elim; p; cs; final_args }
  | CurryRecord ->
     if c.l.is_fwd then
       let npms = List.length trm_app.pms in
       let to_typ_f = unwrap_definition env to_typ in
       let to_typ_app = mkAppl (to_typ_f, trm_app.pms) in
       let sigma, to_typ_prod = reduce_term env sigma to_typ_app in
       let to_elim = dest_prod to_typ_prod in
       let param_elim = mkAppl (prod_rect, [to_elim.Produtils.typ1; to_elim.Produtils.typ2]) in
       let sigma, p = lift_motive env sigma c npms param_elim trm_app.p in
       let p_elim = mkAppl (param_elim, [p]) in
       let sigma, proof = lift_case env c p p_elim (List.hd trm_app.cs) sigma in
       let sigma, args = lift_elim_args env sigma c npms trm_app.final_args in
       let arg = List.hd args in
       sigma, elim_prod Produtils.{ to_elim; p; proof; arg }
     else
       let elim = type_eliminator env (fst (destInd to_typ)) in
       let to_elim = List.hd (fst (take_split 1 trm_app.final_args)) in
       let sigma, pms = Util.on_snd Option.get (type_is_from convertible c env sigma to_elim) in (* TODO redundant *)
       let npms = List.length pms in
       let param_elim = mkAppl (elim, pms) in
       let sigma, p = lift_motive env sigma c npms param_elim trm_app.p in
       let p_elim = mkAppl (param_elim, [p]) in
       let sigma, cs = lift_cases env c p p_elim trm_app.cs sigma in
       let sigma, final_args = lift_elim_args env sigma c npms trm_app.final_args in
       sigma, apply_eliminator { elim; pms; p; cs; final_args }

(*
 * REPACK
 *
 * This is to deal with non-primitive projections
 *)
let repack c env lifted typ sigma =
  match c.l.orn.kind with
  | Algebraic (_, (ib_typ, _)) ->
     let lift_typ = dest_sigT (shift typ) in
     let n = project_index lift_typ (mkRel 1) in
     let b = project_value lift_typ (mkRel 1) in
     let packer = lift_typ.packer in
     let e = pack_existT {index_type = ib_typ; packer; index = n; unpacked = b} in
     sigma, mkLetIn (Anonymous, lifted, typ, e)
  | CurryRecord ->
     let f = first_fun typ in
     let args = unfold_args typ in
     let sigma, typ_red = specialize_delta_f env f args sigma in
     sigma, mkLetIn (Anonymous, lifted, typ, (eta_prod_rec (mkRel 1) (shift typ_red)))

(*
 * Sometimes we must repack because of non-primitive projections.
 * For sigma types, we pack into an existential, and for products, we pack
 * into a pair. It remains to be seen how this generalizes to other types.
 *
 * We are strategic about when we repack in order to avoid slowing down
 * the code too much and producing ugly terms.
 *)
let maybe_repack lift_rec c env trm lifted try_repack sigma =
  if try_repack then
    let sigma_typ, typ = infer_type env sigma trm in
    let typ = reduce_stateless reduce_nf env sigma_typ typ in
    let sigma_typ, is_from_typ = Util.on_snd Option.has_some (is_from convertible c env sigma_typ typ) in
    if is_from_typ then
      let lifted_red = reduce_stateless reduce_nf env sigma lifted in
      let optimize_ignore_repack =
        (* Don't bother repacking when the result would reduce *)
        match c.l.orn.kind with
        | Algebraic (_, _) ->
           is_or_applies existT lifted_red
        | CurryRecord ->
           is_or_applies pair lifted_red
      in
      if not optimize_ignore_repack then
        let sigma, lifted_typ = lift_rec env sigma_typ c typ in
        repack c env lifted lifted_typ sigma
      else
        sigma, lifted
    else
      sigma, lifted
  else
    sigma, lifted
    
(* --- Core algorithm --- *)

(*
 * TODO move/comment/etc
 *)
let zoom_c c =
  match c.l.orn.kind with
  | Algebraic (indexer, (ib_typ, off)) ->
     let orn = { c.l.orn with kind = Algebraic (indexer, (shift ib_typ, off)) } in
     let l = { c.l with orn } in
     { c with l }
  | _ ->
     c
       
(*
 * Core lifting algorithm for algebraic ornaments.
 * A few extra rules to deal with real Coq terms as opposed to CIC,
 * including caching.
 *
 * TODO clean after changing, split up a lot
 *
 * TODO unification when relevant rather than hand-inferring
 *
 * TODO dependent i_b_typ shifting
 *)
let lift_core env sigma c trm =
  let l = c.l in
  let (a_typ, b_typ) = c.typs in
  let sigma, a_typ_eta = expand_eta env sigma a_typ in
  let a_arity = arity a_typ_eta in
  let rec lift_rec en sigma c tr : types state =
    let (sigma, lifted), try_repack =
      let lifted_opt = lookup_lifting (lift_to l, lift_back l, tr) in
      if Option.has_some lifted_opt then
        (* GLOBAL CACHING *)
        (sigma, Option.get lifted_opt), false
      else if is_locally_cached c.cache tr then
        (* LOCAL CACHING *)
        (sigma, lookup_local_cache c.cache tr), false
      else if is_opaque c tr then
        (* OPAQUE CONSTANTS *)
        (sigma, tr), false
      else
        let sigma, args_o = is_from convertible c en sigma tr in
        if Option.has_some args_o then
          (* EQUIVALENCE *)
          let args = Array.of_list (Option.get args_o) in
          let sigma, lifted_args = map_rec_args lift_rec en sigma c args in
          if l.is_fwd then
            match l.orn.kind with
            | Algebraic (_, (ib_typ, _)) ->
               let b_is = mkApp (b_typ, lifted_args) in
               let n = mkRel 1 in
               let abs_ib = reindex_body (reindex_app (index l n)) in
               let packer = abs_ib (mkLambda (Anonymous, ib_typ, shift b_is)) in
               (sigma, pack_sigT { index_type = ib_typ; packer }), false
            | CurryRecord ->
               (sigma, mkApp (b_typ, lifted_args)), false
          else
            (sigma, mkApp (a_typ, lifted_args)), false
        else
          let sigma, i_and_args_o = is_packed_constr c en sigma tr in
          (* LIFT-CONSTR *)
          (* The extra logic here is an optimization *)
          (* It also deals with the fact that we are lazy about eta *)
          if Option.has_some i_and_args_o then
            let i, args = Option.get i_and_args_o in
            let lifted_constr = c.constr_rules.(i - 1) in
            let sigma, constr_app = reduce_term en sigma (mkAppl (lifted_constr, args)) in
            if List.length args > 0 then
              if not c.l.is_fwd then
                let (f', args') = destApp constr_app in
                let sigma, args'' = map_rec_args lift_rec en sigma c args' in
                (sigma, mkApp (f', args'')), false
              else
                (* optimization that skips some subterms *)
                match l.orn.kind with
                | Algebraic (_, _) ->
                   let lifted_inner = last_arg constr_app in
                   let (f', args') = destApp lifted_inner in
                   let sigma, args'' = map_rec_args lift_rec en sigma c args' in
                   let b = mkApp (f', args'') in
                   let ex = dest_existT constr_app in
                   let sigma, n = lift_rec en sigma c ex.index in
                   let sigma, packer = lift_rec en sigma c ex.packer in
                   (sigma, pack_existT { ex with packer; index = n; unpacked = b }), false
                | CurryRecord ->
                   let open Produtils in
                   let pair = dest_pair constr_app in
                   let sigma, typ1 = lift_rec en sigma c pair.typ1 in
                   let sigma, typ2 = lift_rec en sigma c pair.typ2 in
                   let sigma, trm1 = lift_rec en sigma c pair.trm1 in
                   let sigma, trm2 = lift_rec en sigma c pair.trm2 in
                   (sigma, apply_pair {typ1; typ2; trm1; trm2}), false
            else
              (sigma, constr_app), false
          else
            let sigma, run_lift_pack = is_pack c en sigma tr in
            if run_lift_pack then
              (* LIFT-PACK (extra rule for non-primitive projections) *)
              if l.is_fwd then
                (* pack *)
                (sigma, tr), true
              else
                (* unpack (when not covered by constructor rule) *)
                lift_rec en sigma c (dest_existT tr).unpacked, false
            else
              let sigma, to_proj_o = is_proj c en tr sigma in
              if Option.has_some to_proj_o then
                (* COHERENCE *)
                let to_proj, i, args, tr_eta = Option.get to_proj_o in
                if arity tr_eta > arity tr then
                  (* lazy eta expansion; recurse *)
                  (* TODO move to a common place *)
                  lift_rec en sigma c tr_eta, false
                else
                  let p = c.proj_rules.(i) in
                  let sigma, projected = reduce_term en sigma (mkAppl (p, snoc to_proj args)) in
                  lift_rec en sigma c projected, false
              else
                let sigma, is_elim_o = is_eliminator c en tr sigma in
                if Option.has_some is_elim_o then
                  (* LIFT-ELIM *)
                  let tr_eta = Option.get is_elim_o in
                  if arity tr_eta > arity tr then
                    (* lazy eta expansion; recurse *)
                    lift_rec en sigma c tr_eta, false
                  else
                    let sigma, tr_elim = deconstruct_eliminator en sigma tr_eta in
                    let nargs = (* TODO unify/clean/explain *)
                      match c.l.orn.kind with
                      | Algebraic (_, _) ->
                         a_arity - (List.length tr_elim.pms) + 1
                      | CurryRecord ->
                         1
                    in
                    let (final_args, post_args) = take_split nargs tr_elim.final_args in
                    let sigma, tr' = lift_elim en sigma c { tr_elim with final_args } in
                    let sigma, tr'' = lift_rec en sigma c tr' in
                    let sigma, post_args' = map_rec_args lift_rec en sigma c (Array.of_list post_args) in
                    (sigma, mkApp (tr'', post_args')), l.is_fwd
                else
                  match kind tr with
                  | App (f, args) ->
                     if equal (lift_back l) f then
                       (* SECTION/RETRACTION *)
                       lift_rec en sigma c (last_arg tr), false
                     else if equal (lift_to l) f then
                       (* INTERNALIZE *)
                       lift_rec en sigma c (last_arg tr), false
                     else
                       (* APP *)
                       let proj_packed_map = c.optimize_proj_packed_rules in
                       let optimize_proj_packed_o = (* TODO refactor/clean *)
                         (if l.is_fwd then
                           try
                             Some
                               (find_off
                                  proj_packed_map
                                  (fun (proj, _) -> is_or_applies proj tr))
                           with _ ->
                             None
                         else
                           None)
                       in
                       if Option.has_some optimize_proj_packed_o then
                         (* optimize simplifying projections of packed terms, which are common *)
                         let i = Option.get optimize_proj_packed_o in
                         let (_, proj_i_rule) = List.nth proj_packed_map i in
                         proj_i_rule c en f args lift_rec sigma, false
                       else
                         let sigma, f' = lift_rec en sigma c f in
                         if (not l.is_fwd) && Array.length args > 0 && equal f f' && (not (is_opaque c f)) && ((not (isConst f)) || (not (Option.has_some (inductive_of_elim en (destConst f))))) then 
                             (* TODO can we disable w option? More complete this way, but can produce ugly terms. I think we only need this here because the type we are looking for in the backward direction is prod instantiating to something specific; unsure if ever comes up for algebraic  *)
                           (* TODO explain *)
                           let f_delta = unwrap_definition en f in
                           let sigma, app' = reduce_term en sigma (mkApp (f_delta, args)) in
                           let sigma, args' = map_rec_args lift_rec en sigma c args in
                           if equal tr app' then
                             (sigma, mkApp (f', args')), l.is_fwd
                           else
                             let sigma, lifted_red = lift_rec en sigma c app' in
                             if equal lifted_red app' then
                               (sigma, mkApp (f', args')), l.is_fwd
                             else
                               (* TODO explain: refold as in prod_rect example *)
                               let f_delta' = unwrap_definition en f' in
                               let sigma, app'' = reduce_term en sigma (mkApp (f_delta', args')) in
                               if equal lifted_red app'' then
                                 (sigma, mkApp (f', args')), l.is_fwd
                               else
                                 (sigma, lifted_red), l.is_fwd
                         else
                           let sigma, args' = map_rec_args lift_rec en sigma c args in 
                           (sigma, mkApp (f', args')), l.is_fwd
                  | Cast (ca, k, t) ->
                     (* CAST *)
                     let sigma, ca' = lift_rec en sigma c ca in
                     let sigma, t' = lift_rec en sigma c t in
                     (sigma, mkCast (ca', k, t')), false
                  | Prod (n, t, b) ->
                     (* PROD *)
                     let sigma, t' = lift_rec en sigma c t in
                     let en_b = push_local (n, t) en in
                     let sigma, b' = lift_rec en_b sigma (zoom_c c) b in
                     (sigma, mkProd (n, t', b')), false
                  | Lambda (n, t, b) ->
                     (* LAMBDA *)
                     let sigma, t' = lift_rec en sigma c t in
                     let en_b = push_local (n, t) en in
                     let sigma, b' = lift_rec en_b sigma (zoom_c c) b in
                     (sigma, mkLambda (n, t', b')), false
                  | LetIn (n, trm, typ, e) ->
                     (* LETIN *)
                     if l.is_fwd then
                       let sigma, trm' = lift_rec en sigma c trm in
                       let sigma, typ' = lift_rec en sigma c typ in
                       let en_e = push_let_in (n, trm, typ) en in
                       let sigma, e' = lift_rec en_e sigma (zoom_c c) e in
                       (sigma, mkLetIn (n, trm', typ', e')), false
                     else
                       (* Needed for #58 we implement #42 *) (* TODO what? Also why are these different by direction? *)
                       lift_rec en sigma c (reduce_stateless whd en sigma tr), false
                  | Case (ci, ct, m, bs) ->
                     (* CASE (will not work if this destructs over A; preprocess first) *)
                     let sigma, ct' = lift_rec en sigma c ct in
                     let sigma, m' = lift_rec en sigma c m in
                     let sigma, bs' = map_rec_args lift_rec en sigma c bs in
                     (sigma, mkCase (ci, ct', m', bs')), false
                  | Fix ((is, i), (ns, ts, ds)) ->
                     (* FIX (will not work if this destructs over A; preprocess first) *)
                     let sigma, ts' = map_rec_args lift_rec en sigma c ts in
                     let sigma, ds' = map_rec_args (fun env sigma a trm -> map_rec_env_fix lift_rec zoom_c en sigma a ns ts trm) en sigma c ds in
                     (sigma, mkFix ((is, i), (ns, ts', ds'))), false
                  | CoFix (i, (ns, ts, ds)) ->
                     (* COFIX (will not work if this destructs over A; preprocess first) *)
                     let sigma, ts' = map_rec_args lift_rec en sigma c ts in
                     let sigma, ds' = map_rec_args (fun env sigma a trm -> map_rec_env_fix lift_rec zoom_c en sigma a ns ts trm) en sigma c ds in
                     (sigma, mkCoFix (i, (ns, ts', ds'))), false
                  | Proj (pr, co) ->
                     (* PROJ *)
                     let sigma, co' = lift_rec en sigma c co in
                     (sigma, mkProj (pr, co')), false
                  | Construct (((i, i_index), _), u) ->
                     let ind = mkInd (i, i_index) in
                     (* TODO is this right for curryrecord or will it miss some constructors? *)
                     if equal ind (directional l a_typ b_typ) then
                       (* lazy eta expansion *)
                       let sigma, tr_eta = expand_eta en sigma tr in
                       lift_rec en sigma c tr_eta, false
                     else
                       (sigma, tr), false
                  | Const (co, u) ->
                     let sigma, lifted =
                       (try
                          (* CONST *)
                          if Option.has_some (inductive_of_elim en (co, u)) then
                            sigma, tr
                          else
                            let def = lookup_definition en tr in
                            let sigma, try_lifted = lift_rec en sigma c def in
                            if equal def try_lifted then
                              sigma, tr
                            else
                              reduce_term en sigma try_lifted
                        with _ ->
                          (* AXIOM *)
                          sigma, tr)
                     in smart_cache c tr lifted; (sigma, lifted), false
                  | _ ->
                     (sigma, tr), false
       in maybe_repack lift_rec c en tr lifted try_repack sigma 
  in lift_rec env sigma c trm
              
(*
 * Run the core lifting algorithm on a term
 *)
let do_lift_term env sigma (l : lifting) trm opaques =
  let (a_t, b_t, i_b_t_o) = typs_from_orn l env sigma in
  let sigma, c = initialize_lift_config env sigma l (a_t, b_t) opaques in
  lift_core env sigma c trm

(*
 * Run the core lifting algorithm on a definition
 *)
let do_lift_defn env sigma (l : lifting) def =
  do_lift_term env sigma l def

(************************************************************************)
(*                           Inductive types                            *)
(************************************************************************)

let define_lifted_eliminator ?(suffix="_sigT") l ind0 ind sort =
  let env = Global.env () in
  let ident =
    let ind_name = (Inductive.lookup_mind_specif env ind |> snd).mind_typename in
    let raw_ident = Indrec.make_elimination_ident ind_name sort in
    Nameops.add_suffix raw_ident suffix
  in
  let elim0 = Indrec.lookup_eliminator ind0 sort in
  let elim = Indrec.lookup_eliminator ind sort in
  let env, term = open_constant env (Globnames.destConstRef elim) in
  let expr = Eta.eta_extern env (Evd.from_env env) Id.Set.empty term in
  ComDefinition.do_definition
    ~program_mode:false
    ident
    (Decl_kinds.Global, false, Decl_kinds.Scheme)
    None
    []
    None
    expr
    None
    (Lemmas.mk_hook
       (fun _ lifted ->
         let elim0 = Universes.constr_of_global elim0 in
         let lifted = Universes.constr_of_global lifted in
         save_lifting (lift_to l, lift_back l, elim0) lifted;
         save_lifting (lift_back l, lift_to l, lifted) elim0))

let declare_inductive_liftings l ind ind' ncons =
  save_lifting (lift_to l, lift_back l, mkInd ind) (mkInd ind');
  save_lifting (lift_back l, lift_to l, mkInd ind') (mkInd ind);
  List.iter2
    (fun o n ->
      save_lifting (lift_to l, lift_back l, o) n;
      save_lifting (lift_back l, lift_to l, n) o)
    (List.init ncons (fun i -> mkConstruct (ind, i + 1)))
    (List.init ncons (fun i -> mkConstruct (ind', i + 1)))

(*
 * Lift the inductive type using sigma-packing.
 *
 * This algorithm assumes that type parameters are left constant and will lift
 * every binding and every term of the base type to the sigma-packed ornamented
 * type. (IND and CONSTR via caching)
 *)
let do_lift_ind env sigma l typename suffix ind ignores =
  let (a_t, b_t, i_b_t_o) = typs_from_orn l env sigma in
  let sigma, c = initialize_lift_config env sigma l (a_t, b_t) ignores in
  let (mind_body, ind_body) as mind_specif = Inductive.lookup_mind_specif env ind in
  if is_opaque c (mkInd ind) then
    let _ = Feedback.msg_warning (Pp.str "Ignoring inductive type") in
    ind
  else
    let _ = check_inductive_supported mind_body in
    let env, univs, arity, constypes = open_inductive ~global:true env mind_specif in
    let sigma = Evd.update_sigma_env sigma env in
    let nparam = mind_body.mind_nparams_rec in
    let sigma, arity' = do_lift_term env sigma l arity ignores in
    let sigma, constypes' = map_state (fun trm sigma -> do_lift_term env sigma l trm ignores) constypes sigma in
    let consnames =
      Array.map_to_list (fun id -> Nameops.add_suffix id suffix) ind_body.mind_consnames
    in
    let is_template = is_ind_body_template ind_body in
    let ind' =
      declare_inductive typename consnames is_template univs nparam arity' constypes'
    in
    List.iter (define_lifted_eliminator l ind ind') [Sorts.InType; Sorts.InProp];
    declare_inductive_liftings l ind ind' (List.length constypes);
    ind'
