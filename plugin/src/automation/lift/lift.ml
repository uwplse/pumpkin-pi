(*
 * Core lifting algorithm
 *)

open Util
open Constr
open Lifting
open Utilities
open Caching
open Declarations
open Specialization
open Indutils
open Apputils
open Reducers
open Envutils
open Stateutils
open Hofs
open Promotion
open Liftconfig
open Liftrules
open Evd
open Equivutils
open Equtils

(*
 * The top-level lifting algorithm
 *)

(* --- Convenient shorthand --- *)

let map_rec_args_list lift_rec env sigma c args =
  Util.on_snd
    Array.to_list
    (map_rec_args lift_rec env sigma c (Array.of_list args))

(* --- Application --- *)

(*
 * LIFT-IDENTITY, COHERENCE, and EQUIVALENCE all run here.
 *
 * First this lifts the arguments, then it applies the lifted function
 * (which is cached) and uses a custom reducer to simplify the result.
 * The custom reducer creates simpler terms (for example, by simplifying
 * pojections of existentials), and in doing so helps ensure termination
 * and correctness when the lifted type refers to the unlifted type.
 *)
let lift_app_simplify c env lifted_f args simplify lift_rec sigma =
  let sigma, lifted_args = map_rec_args_list lift_rec env sigma c args in
  if List.length lifted_args = 0 then
    sigma, lifted_f
  else
    simplify env sigma (mkAppl (lifted_f, lifted_args))

(* --- Optimization implementations --- *)

(*
 * When we lift to a projection of the eta-expanded identity function,
 * simplify early rather than wait for Coq 
 *)
let lift_simplify_project_id c env reduce f args lift_rec sigma =
  let sigma, arg' = lift_rec env sigma c (last (Array.to_list args)) in
  let arg'' = reduce_stateless reduce_term env sigma arg' in
  if may_apply_eta (reverse c) env arg'' then
    (* projection of expanded identity *)
    reduce env sigma arg''
  else
    (* false positive; projection of something else *)
    let sigma, f' = lift_rec env sigma c f in
    let lifted_args =
      if ((get_lifting c).orn.kind = UnpackSigma && not (get_lifting c).is_fwd) then
        snoc arg' (all_but_last (Array.to_list args))
      else
        let sigma, args' = map_rec_args lift_rec env sigma c args in
        Array.to_list args'
    in sigma, mkAppl (f', lifted_args)

(*
 * Lift applications, possibly being lazy about delta if we can get away with it.
 *
 * This can still lift some code very slowly if functions are not set as opaque.
 * However, delta is sometimes needed for correctness. To lift code quickly,
 * it's advisable to set appropriate functions as opaque.
 *)
let lift_app_lazy_delta c env f args lift_rec sigma =
  let sigma, f' = lift_rec env sigma c f in
  let sigma, args' = map_rec_args lift_rec env sigma c args in
  if (not (equal f f')) || Array.length args = 0 || is_opaque c f then
    let app' = mkApp (f', args') in
    if equal f' (get_lifted_dep_elim c) then
      (* eliminator---custom reduction *)
      reduce_lifted_elim c env sigma app'
    else
      sigma, app'
  else
    match kind f with
    | Const (c, u) when Option.has_some (inductive_of_elim env (c, u)) ->
       sigma, mkApp (f', args')
    | _ ->
       let sigma, app' = specialize_delta_f env f (Array.to_list args) sigma in
       if equal (mkApp (f, args)) app' then
         sigma, mkApp (f', args')
       else
         let sigma, lifted_red = lift_rec env sigma c app' in
         if equal lifted_red app' then
           sigma, mkApp (f', args')
         else
           let sigma, app'' = specialize_delta_f env f' (Array.to_list args') sigma in
           if equal lifted_red app'' then
             sigma, mkApp (f', args')
           else
             sigma, lifted_red

(*
 * Lift constants, possibly being lazy about delta if we can get away with it
 *)
let lift_const_lazy_delta c env (co, u) lift_rec sigma =
  let trm = mkConstU (co, u) in
  let sigma, lifted =
    (try
       if Option.has_some (inductive_of_elim env (co, u)) then
         sigma, trm
       else
         let def = lookup_definition env (mkConstU (co, u)) in
         let sigma, try_lifted = lift_rec env sigma c def in
         if equal def try_lifted then
           sigma, trm
         else
           reduce_remove_identities env sigma try_lifted
     with _ ->
       (* axiom *)
       sigma, trm)
  in smart_cache c trm lifted; (sigma, lifted)

(* Lift existential variables *)
let lift_evar c env trm lift_rec sigma =
  (* For now, this has many extra EConstr conversions, which can be slow *)
  let (etrm, _) = destEvar trm in
  let sigma, typ = Inference.infer_type env sigma trm in
  let info = Evd.find sigma etrm in
  let sigma, lifted_info =
    let sigma, evar_concl =
      let sigma, lifted_typ = lift_rec env sigma c typ in
      sigma, EConstr.of_constr lifted_typ
    in
    let sigma, evar_body =
      match info.evar_body with
      | Evar_empty -> sigma, Evar_empty
      | Evar_defined bod ->
         let bod = EConstr.to_constr sigma bod in
         let sigma, lifted_bod = lift_rec env sigma c bod in
         sigma, Evar_defined (EConstr.of_constr lifted_bod)
    in
    let sigma, evar_candidates =
      if Option.has_some info.evar_candidates then
        let candidates = List.map (EConstr.to_constr sigma) (Option.get info.evar_candidates) in
        let sigma, lifted_candidates = map_rec_args_list lift_rec env sigma c candidates in
        sigma, Some (List.map EConstr.of_constr lifted_candidates)
      else
        sigma, None
    in sigma, { info with evar_concl; evar_body; evar_candidates }
  in Evd.add (Evd.remove sigma etrm) etrm lifted_info, trm

(* Lift equality types *)
let lift_eq_app c env l lift_rec sigma =
  let kind = (get_lifting c).orn.kind in
  match kind with
  | Setoid (typs, (eq_types, eq_rels, eq_proofs)) ->
     let eq_type = List.hd l in
     let sigma, lifted_eq_type = lift_rec env sigma c eq_type in
     let rel_map = List.combine eq_types eq_rels in
     (try
       (let eq_rel = snd (List.find (fun t -> snd (Convertibility.convertible env sigma (fst t) lifted_eq_type)) rel_map) in
        let sigma, lifted_args = map_rec_args_list lift_rec env sigma c (List.tl l) in
        sigma, (mkAppl (eq_rel, lifted_args)))
      with Not_found ->
       failwith "Tried to lift an equality on a type for which no equivalence relation was provided.")
  | _ -> failwith "Eq lifting unsupported outside of Setoid lifting"

(* Lift eq_refl applications *)
let lift_eq_refl_app c env l lift_rec sigma =
  let kind = (get_lifting c).orn.kind in
  match kind with
  | Setoid (typs, (eq_types, eq_rels, eq_proofs)) ->
     let eq_type = List.hd l in
     let sigma, lifted_eq_type = lift_rec env sigma c eq_type in
     let rel_map = List.combine eq_types (List.combine eq_rels eq_proofs) in
     (try
       (let eq_rel, eq_proof = snd (List.find (fun t -> snd (Convertibility.convertible env sigma (fst t) lifted_eq_type)) rel_map) in
        let sigma, lifted_args = map_rec_args_list lift_rec env sigma c (List.tl l) in
        let refl_proof = mkAppl (Equivutils.equiv_refl_getter, [lifted_eq_type ; eq_rel ; eq_proof]) in
        sigma, mkAppl (refl_proof, lifted_args))
      with Not_found ->
        failwith "Tried to lift an eq_refl proof on a type for which no equivalence relation was provided.")
  | _ -> failwith "Eq_refl lifting unsupported outside of Setoid lifting."

let lift_rewrite_args c env (rewrite_info : Equtils.rewrite_args) lift_rec sigma =
  let sigma, a = lift_rec env sigma c rewrite_info.a in
  let sigma, x = lift_rec env sigma c rewrite_info.x in
  let sigma, p = lift_rec env sigma c rewrite_info.p in
  let sigma, px = lift_rec env sigma c rewrite_info.px in
  let sigma, y = lift_rec env sigma c rewrite_info.y in
  let sigma, eq = lift_rec env sigma c rewrite_info.eq in
  let sigma, params = map_rec_args lift_rec env sigma c (Array.copy rewrite_info.params) in
  { a = a ; x ; p ; px ; y ; eq ; params ; left = rewrite_info.left}

open Names
open Tactics

let coq_program_basics =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["Basics"; "Program"; "Coq"]))

let funtype =
  mkConst (Constant.make2 coq_program_basics (Label.make "arrow"))

open Decompiler

(*
 * Create a tactic performing the rewrite represented by rewrite_info. 
 * Based on show_tactic from the Decompiler module.
 * (I am presently skeptical that this will work.)
 *)
let rewrite_tactic_from_args c env rewrite_info sigma =
  let prnt e = Printer.pr_constr_env e sigma in
  let s = prnt env rewrite_info.eq in
  let arrow = if rewrite_info.left then "<- " else "" in
  Decompiler.parse_tac_str (Pp.string_of_ppcmds (Pp.app (Pp.str ("rewrite " ^ arrow)) s))

(* Lift equality rewriting *)
let lift_eq_rewrite c env rewrite_info lift_rec sigma =
  let lifted_rewrite_info = lift_rewrite_args c env rewrite_info lift_rec sigma in
  let goal_consequent = mkAppl(rewrite_info.p, [lifted_rewrite_info.y]) in
  let goal = mkAppl(funtype, [lifted_rewrite_info.px ; goal_consequent]) in
  let proof = Proof.start sigma [(env, EConstr.of_constr goal)] in
  let (proof, _) = Proof.run_tactic env Tactics.intros proof in
  let (proof, _) = Proof.run_tactic env (rewrite_tactic_from_args c env rewrite_info sigma) proof in
  let (proof, _) = Proof.run_tactic env Tactics.assumption proof in
  if (Proof.is_done proof) then
    match Proof.partial_proof proof with
    | [] -> failwith "No proof of rewrite goal found."
    | h :: t -> sigma, EConstr.to_constr sigma h 
  else
    failwith "Failed when attempting to lift a rewrite."
     

(* --- Core algorithm --- *)

(*
 * Core lifting algorithm.
 * A few extra rules to deal with real Coq terms as opposed to CIC,
 * including caching.
 *)
let lift_core env c trm sigma =
  let rec lift_rec prev_rules en sigma c tr : types state =
    let sigma, lift_rule = determine_lift_rule c en tr prev_rules sigma in
    let lift_rules = lift_rule :: prev_rules in
    match lift_rule with
    | Optimization (GlobalCaching lifted) | Optimization (LocalCaching lifted) ->
       sigma, lifted
    | Optimization OpaqueConstant ->
       sigma, tr
    | Optimization (LazyEta tr_eta) ->
       lift_rec lift_rules en sigma c tr_eta
    | Eta (simplify, (f, args)) | Coherence (simplify, (f, args))
    | LiftConstr (simplify, (f, args)) ->
       lift_app_simplify c en f args simplify (lift_rec lift_rules) sigma
    | Equivalence (f, args) | Iota (f, args) ->
       lift_app_simplify c en f args reduce_term (lift_rec lift_rules) sigma
    | Optimization (SimplifyProjectId (reduce, (f, args))) ->
       lift_simplify_project_id c en reduce f args (lift_rec lift_rules) sigma
    | Optimization (AppLazyDelta (f, args)) ->
       lift_app_lazy_delta c en f args (lift_rec lift_rules) sigma
    | Optimization (ConstLazyDelta (co, u)) ->
       lift_const_lazy_delta c en (co, u) (lift_rec lift_rules) sigma
    | Eq l ->
       lift_eq_app c en l (lift_rec lift_rules) sigma
    | EqRefl l ->
       lift_eq_refl_app c en l (lift_rec lift_rules) sigma
    | EqRewrite rewrite_info ->
       lift_eq_rewrite c en rewrite_info (lift_rec lift_rules) sigma
    | CIC k ->
       let lift_rec = lift_rec lift_rules in
       (match k with
        | Evar (etrm, _) ->
           (* EVAR *)
           lift_evar c en tr lift_rec sigma
        | Cast (ca, k, t) ->
           (* CAST *)
           let sigma, ca' = lift_rec en sigma c ca in
           let sigma, t' = lift_rec en sigma c t in
           (sigma, mkCast (ca', k, t'))
        | Prod (n, t, b) ->
           (* PROD *)
           let sigma, t' = lift_rec en sigma c t in
           let en_b = push_local (n, t) en in
           let sigma, b' = lift_rec en_b sigma (zoom c) b in
           (sigma, mkProd (n, t', b'))
        | Lambda (n, t, b) ->
           (* LAMBDA *)
           let sigma, t' = lift_rec en sigma c t in
           let en_b = push_local (n, t) en in
           let sigma, b' = lift_rec en_b sigma (zoom c) b in
           (sigma, mkLambda (n, t', b'))
        | LetIn (n, trm, typ, e) ->
           (* LETIN *)
           let sigma, trm' = lift_rec en sigma c trm in
           let sigma, typ' = lift_rec en sigma c typ in
           let en_e = push_let_in (n, trm, typ) en in
           let sigma, e' = lift_rec en_e sigma (zoom c) e in
           (sigma, mkLetIn (n, trm', typ', e'))
        | Case (ci, ct, m, bs) ->
           (* CASE (will not work if this destructs over A; preprocess first) *)
           let sigma, ct' = lift_rec en sigma c ct in
           let sigma, m' = lift_rec en sigma c m in
           let sigma, bs' = map_rec_args lift_rec en sigma c bs in
           (sigma, mkCase (ci, ct', m', bs'))
        | Fix ((is, i), (ns, ts, ds)) ->
           (* FIX (will not work if this destructs over A; preprocess first) *)
           let sigma, ts' = map_rec_args lift_rec en sigma c ts in
           let sigma, ds' = map_rec_args (fun en sigma a trm -> map_rec_env_fix lift_rec zoom en sigma a ns ts trm) en sigma c ds in
           (sigma, mkFix ((is, i), (ns, ts', ds')))
        | CoFix (i, (ns, ts, ds)) ->
           (* COFIX (will not work if this destructs over A; preprocess first) *)
           let sigma, ts' = map_rec_args lift_rec en sigma c ts in
           let sigma, ds' = map_rec_args (fun en sigma a trm -> map_rec_env_fix lift_rec zoom en sigma a ns ts trm) en sigma c ds in
           (sigma, mkCoFix (i, (ns, ts', ds')))
        | Proj (pr, co) ->
           (* PROJ *)
           let sigma, co' = lift_rec en sigma c co in
           (sigma, mkProj (pr, co'))
        | Construct _ ->
           smart_cache c tr tr; (sigma, tr)
        | _ ->
           (sigma, tr))
  in lift_rec [] env sigma c trm
              
(*
 * Run the core lifting algorithm on a term
 *)
let do_lift_term env sigma (l : lifting) trm opaques =
  let sigma, c = initialize_lift_config env l opaques sigma in
  let env = Global.env () in
  lift_core env c trm sigma

(*
 * Run the core lifting algorithm on a definition
 *)
let do_lift_defn env sigma (l : lifting) def =
  do_lift_term env sigma l def

(************************************************************************)
(*                           Inductive types                            *)
(************************************************************************)

let define_lifted_eliminator ?(suffix="_sigT") l ind0 ind sort =
  (* Do not lift eliminator into sort `Set` -- unnecessary and error-prone (TODO why) *)
  (*if not (Sorts.family_equal Sorts.InSet sort) then*)
  (* TODO fix test bugs *)
    let env = Global.env () in
    let (_, ind_body) as mind_specif = Inductive.lookup_mind_specif env ind in
    let ident =
      let ind_name = ind_body.mind_typename in
      let raw_ident = Indrec.make_elimination_ident ind_name sort in
      Nameops.add_suffix raw_ident suffix
    in
    let elim0 = Indrec.lookup_eliminator ind0 sort in
    let elim = Indrec.lookup_eliminator ind sort in
    let sigma, (eta_term, eta_type) =
      let sigma, term = Evarutil.new_global (Evd.from_env env) elim in
      let sigma, typ = Typing.type_of env sigma term in
      let typ = Reductionops.nf_betaiotazeta env sigma typ in
      let term, typ = EConstr.(to_constr sigma term, to_constr sigma typ) in
      sigma, Depelim.eta_guard_eliminator mind_specif term typ
    in
    let elim' = UnivGen.constr_of_global (Defutils.define_term ~typ:eta_type ident sigma eta_term true) in
    let elim0 = UnivGen.constr_of_global elim0 in
    save_lifting (lift_to l, lift_back l, elim0) elim';
    save_lifting (lift_back l, lift_to l, elim') elim0

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
let do_lift_ind env sigma l typename suffix ind ignores is_lift_module =
  let sigma, c = initialize_lift_config env l ignores sigma in
  let env = Global.env () in
  let sigma = Evd.from_env env in
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
    List.iter (define_lifted_eliminator l ind ind') ind_body.mind_kelim;
    declare_inductive_liftings l ind ind' (List.length constypes);
    (* Lift record projections *)
    try
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let open Recordops in
      let r = lookup_structure ind in
      Feedback.msg_info (Pp.str "Lifted a record");
      let pks = r.s_PROJKIND in
      let mod_path = Lib.current_mp () in
      let ps =
        List.map
          (Option.map
             (fun p -> Names.Constant.make2 mod_path (Names.Constant.label p)))
          r.s_PROJ
      in
      let _ =
        List.map
          (Option.map
             (fun p ->
               (* In modules, this may try to lift record projections twice *)
               let c = mkConst p in
               let sigma, p_lifted = do_lift_term env sigma l c ignores in
               let n = Names.Label.to_id (Names.Constant.label p) in
               let def = Defutils.define_term n sigma p_lifted true in
               Feedback.msg_info
                 (Pp.str (Printf.sprintf "DEVOID generated %s" (Names.Id.to_string n)));
               def))
          r.s_PROJ
      in
      (try
         declare_structure (ind', (ind', 1), pks, ps);
         ind'
       with _ ->
         Feedback.msg_warning
           (Pp.str "Failed to register projections for lifted record");
         ind')
    with Not_found ->
      ind'
