open Constr
open Liftconfig
open Indutils
open Caching
open Lifting
open Zooming
open Apputils
open Promotion
open Sigmautils
open Utilities
open Desugarprod
open Reducers
open Funutils
open Stateutils
open Hypotheses
open Envutils
open Indexing
open Evd
open Evarutil
open Evarconv
open Specialization
open Debruijn
open Names
open Equtils
open Environ
open Hofs

(*
 * This module takes in a Coq term that we are lifting and determines
 * the appropriate lifting rule to run
 *)

(* --- Datatypes --- *)

(*
 * When an optimization may be possible, we return one of these.
 * Sometimes, we need more information to determine if the optimization is
 * definitely possible. This just makes it very explicit in the code what
 * is an attempt at an optimization, as opposed to what is needed for
 * correctness only.
 *
 * Optimizations:
 * 1. GlobalCaching: When the constant is in the global lifting cache,
 *    we just return the cached lifted term. This carries the cached
 *    lifted term.
 *
 * 2. LocalCaching: When a term is in the local lifting cache,
 *    we just return the cached lifted term. This carries the cached
 *    lifted term.
 *
 * 3. OpaqueConstant: When a user uses the opaque option for DEVOID for a given
 *    constant, we do not delta-reduce that constant.
 *    Note that this is different from Coq's notion of "opaque"; we may
 *    delta-reduce constants marked as opaque to the rest of Coq, and we may
 *    consider a constant opaque when Coq does not. It depends only on the
 *    user setting this particular option for DEVOID.
 *
 * 4. SimplifyProjectId: When we see projections of lifted eta-expanded identity
 *    terms (for example, projT1 (existT ...)), we reduce eagerly rather than
 *    wait for Coq to reduce, since we can be smarter than Coq for this
 *    case. This simplifies very large lifted constants significantly.
 *    This carries a reducer that explains how to project, and a function
 *    and argument pair that corresponds to the application term broken up.
 *
 * 5. LazyEta: We eta expand lazily, only when needed for correctness.
 *    The optimization is really this rule _not always_ fiting; this rule
 *    fires when we determine it is actually time to eta expand a term.
 *    This carries the eta-expanded term.
 *
 * 6. AppLazyDelta: This optimization skips delta-reduction for some
 *    function applications. This also includes the normal function
 *    application rule, since determining whether or not this optimization
 *    is possible requires "looking ahead" at some lifted subterms.
 *    This carries the function and argument pair.
 *
 * 7. ConstLazyDelta: This optimization skips delta-reduction for some
 *    contants. It is similar to AppLazyDelta. This carries the constant.
 *
 * 8. SmartLiftConstr: For certain equivalences, we can configure a faster
 *    version of LiftConstr. This rule fires when we've determined a faster
 *    version to run in its place. This carries the cached lifted constructor
 *    and the arguments.
 *)
type lift_optimization =
| GlobalCaching of constr
| LocalCaching of constr
| OpaqueConstant
| SimplifyProjectId of reducer * (constr * constr array)
| LazyEta of constr
| AppLazyDelta of constr * constr array
| ConstLazyDelta of Names.Constant.t Univ.puniverses
| SmartLiftConstr of constr * constr list
                                     
(*
 * We compile Gallina to a language that matches our premises for the rules
 * in our lifting algorithm.
 *
 * 1. EQUIVALENCE runs when the term we are lifting is one of the types in
 *    the type equivalence we are lifting across. This carries the lifted type
 *    and the arguments to the lifted type.
 *
 * 2. LIFT-CONSTR runs when we lift constructors of the type in the equivalence.
 *    This carries the lifted constructor and the arguments, as well as a custom
 *    reduction function to apply the constructor to the arguments prior to
 *    lifting the result.
 *
 * 3. COHERENCE runs when we lift projections of the type in the equivalence
 *    (either at the term or type level). This carries the term we are
 *    the lifted projection and the arguments, as well as a custom reduction
 *    function to apply coherence to the lifted arguments (to neatly ensure
 *    termination while also maintaining correctness).
 *
 * 4. LIFT-ELIM runs when we lift applications of eliminators of the type
 *    in the equivalence. This carries the application of the eliminator,
 *    the lifted parameters, and the number of arguments it expects,
 *    as well as a flag for whether to treat the entire eliminated term
 *    as opaque.
 *
 * 5. SECTION runs when section applies.
 *
 * 6. RETRACTION runs when retraction applies.
 *
 * 7. INTERNALIZE runs when it is necessary to get rid of some application
 *    of the equivalence temporarily introduced by LIFT-CONSTR or LIFT-ELIM
 *    for the sake of creating intermediate terms that type check.
 *
 * 8. OPTIMIZATION runs when some optimization applies.
 *
 * 9. LIFT-IDENTITY runs when we lift the eta-expanded identity function.
 *    This exists to ensure that we preserve definitional equalities.
 *    The rule returns the lifted identity function and its arguments, as
 *    well as a custom reduction function to apply identity to the
 *    lifted arguments (for efficiency and to ensure termination).
 *
 * 10. CIC runs when no optimization applies and none of the other rules
 *    apply. It returns the kind of the Gallina term.
 *)
type lift_rule =
| Equivalence of constr * constr list
| LiftConstr of reducer * (constr * constr list)
| LiftIdentity of reducer * (constr * constr list)
| Coherence of reducer * (constr * constr list)
| LiftElim of elim_app * constr list * int * bool
| Section
| Retraction
| Internalize
| Optimization of lift_optimization
| CIC of (constr, types, Sorts.t, Univ.Instance.t) kind_of_term

(* --- Premises --- *)

(* Termination condition for EQUIVALENCE *)
let terminate_eqv c prev_rules args_o env =
  let l = get_lifting c in
  let args = Option.get args_o in
  List.exists
    (fun prev_rule ->
      match prev_rule with
      | Optimization (SmartLiftConstr _) ->
         (* TODO *)
         true
      | Equivalence (_, args') when List.length args = List.length args' ->
         List.for_all2 equal args args'
      | Coherence (_, (p, _)) when (not l.is_fwd) && l.orn.kind = UnpackSigma ->
         let p_body = zoom_term zoom_lambda_term env p in
         is_or_applies existT p_body
      | _ ->
         false)
    prev_rules

(* Premises for EQUIVALENCE *)
let is_equivalence c env trm prev_rules sigma =
  let sigma, args_o = is_from c env trm sigma in
  if Option.has_some args_o then
    let terminates = terminate_eqv c prev_rules args_o env in
    if not terminates then
      let (a_typ, b_typ) = get_types c in
      let typ = if (get_lifting c).is_fwd then b_typ else a_typ in
      sigma, Some (typ, Option.get args_o)
    else
      sigma, None
  else
    sigma, None
                                                   
(* Premises for LIFT-CONSTR *)
(* TODO use ID rules, and mvoe out id rules from constr if possible *)
let is_packed_constr c env sigma trm =
  let l = get_lifting c in
  let constrs = get_constrs c in
  let is_packed_inductive_constr unpack trm =
    try
      let unpacked = unpack trm in
      let f = first_fun unpacked in
      let args = unfold_args unpacked in
      match kind f with
      | Construct ((_, i), _) when i <= Array.length constrs ->
         let constr = constrs.(i - 1) in
         let constr_f = first_fun (unpack (zoom_term zoom_lambda_term env constr)) in
         if equal constr_f f && List.length args = arity constr then
           sigma, Some (i - 1, args)
         else
           sigma, None
      | _ ->
         sigma, None
    with _ ->
      sigma, None
  in
  if may_apply_id_eta c env trm then
    let sigma, i_and_args_o =
      match l.orn.kind with
      | Algebraic _ ->
         is_packed_inductive_constr (if l.is_fwd then id else last_arg) trm
      | SwapConstruct _ ->
         is_packed_inductive_constr id trm
      | CurryRecord ->
         if l.is_fwd then
           is_packed_inductive_constr id trm
         else
           (* we treat any pair of the right type as a constructor *)
           if applies (lift_back l) trm then
             sigma, None
           else
             let sigma_right, args_opt = type_is_from c env trm sigma in
             if Option.has_some args_opt then
               let sigma = sigma_right in
               let constr = constrs.(0) in
               let pms = Option.get args_opt in
               let args = pair_projections_eta_rec_n trm (arity constr - List.length pms) in
               sigma, Some (0, List.append pms args)
             else
               sigma, None
      | UnpackSigma ->
         if l.is_fwd then
           (* TODO add real constr here *)
           sigma, None
         else (* <-- TODO correct or not? needed? also, this is slow *)
           is_packed_inductive_constr id trm
    in
    if Option.has_some i_and_args_o then
      let i, args = Option.get i_and_args_o in
      sigma, Some (i, args, reduce_constr_app c)
    else
      sigma, None
  else
    sigma, None

(* Termination condition for COHERENCE *)
let terminate_coh prev_rules proj_o env trm sigma =
  let proj, args, _ = Option.get proj_o in
  exists_state
    (fun prev_rule sigma ->
      match prev_rule with
      | Optimization (SmartLiftConstr _) ->
         (* TODO *)
         sigma, true
      | Coherence (_, (proj', args')) when equal proj proj' ->
         if List.for_all2 equal args args' then
           sigma, true
         else
           let sigma, projected = reduce_term env sigma (mkAppl (proj', args')) in
           sigma, equal trm projected
      | _ ->
         sigma, false)
    prev_rules
    sigma
             
(* Premises for COHERENCE *)
let is_coh c env trm prev_rules sigma =
  let sigma, to_proj_o = is_proj c env trm sigma in
  if Option.has_some to_proj_o then
    let sigma, terminate = terminate_coh prev_rules to_proj_o env trm sigma in
    if not terminate then
      sigma, to_proj_o
    else
      sigma, None
  else
    sigma, None

(* Termination condition for LIFT-IDENTITY *)
let terminate_identity prev_rules args_o =
  let args = Option.get args_o in
  List.exists
    (fun prev_rule ->
      match prev_rule with
      | LiftIdentity (_, (_, args')) ->
         List.for_all2 equal args args'
      | _ ->
         false)
    prev_rules

(* Premises for LIFT-IDENTITY *)
let is_identity c env trm prev_rules sigma =
  let sigma, args_o = applies_id_eta c env trm sigma in
  if Option.has_some args_o then
    let terminate = terminate_identity prev_rules args_o in
    if not terminate then
      sigma, Some (get_lifted_id_eta c, Option.get args_o)
    else
      sigma, None
  else
    sigma, None

(* Premises for LIFT-ELIM (TODO move more to liftconfig) *)
let is_eliminator c env trm sigma =
  let l = get_lifting c in
  match kind (first_fun trm) with
  | Const (k, u) ->
     let maybe_ind = inductive_of_elim env (k, u) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       let is_elim = equal (mkInd (ind, 0)) (get_elim_type c) in
       if is_elim then
         let sigma, trm_eta = expand_eta env sigma trm in
         let env_elim, trm_b = zoom_lambda_term env trm_eta in
         let sigma, trm_elim = deconstruct_eliminator env_elim sigma trm_b in
         let (a_typ, _) = get_types c in
         let sigma, a_typ_eta = expand_eta env sigma a_typ in
         let a_arity = arity a_typ_eta in
         let nargs =
           match l.orn.kind with
           | Algebraic _ | SwapConstruct _ | UnpackSigma ->
              a_arity - (List.length trm_elim.pms) + 1
           | CurryRecord ->
              1
         in
         if (not l.is_fwd) && l.orn.kind = CurryRecord then
           let (final_args, post_args) = take_split 1 trm_elim.final_args in
           let sigma, is_from = type_is_from c env_elim (List.hd final_args) sigma in
           if Option.has_some is_from then
             sigma, Some (env_elim, trm_eta, trm_elim, Option.get is_from, nargs, false)
           else
             sigma, None
         else
           if l.orn.kind = CurryRecord then
             let typ_f = first_fun (zoom_term zoom_lambda_term env_elim (snd (get_types c))) in
             let sigma, to_typ_prod = specialize_delta_f env_elim typ_f trm_elim.pms sigma in
             let to_elim = dest_prod to_typ_prod in
             let pms = [to_elim.Produtils.typ1; to_elim.Produtils.typ2] in
             sigma, Some (env_elim, trm_eta, trm_elim, pms, nargs, false)
           else
             sigma, Some (env_elim, trm_eta, trm_elim, trm_elim.pms, nargs, l.orn.kind = UnpackSigma)
       else
         sigma, None
     else
       sigma, None
  | _ ->
     sigma, None

(*
 * Termination condition for SECTION / RETRACTION
 *)
let terminate_section_retraction c prev_rules =
  let l = get_lifting c in
  match l.orn.kind with
  | UnpackSigma when not l.is_fwd ->
     List.exists
       (fun prev_rule ->
         match prev_rule with
         | Optimization (SmartLiftConstr _) ->
            (* TODO remove *)
            true
         | LiftConstr _ ->
            true
         | _ ->
            false)
       prev_rules
  | _ ->
     false

(*
 * SECTION / RETRACTION
 *)
let is_section_retraction c prev_rules trm =
  let l = get_lifting c in
  if isApp trm && applies (lift_back l) trm then
    not (terminate_section_retraction c prev_rules)
  else
    false

(*
 * Given a term, determine the appropriate lift rule to run
 * TODO make prev_rules a hash
 *)
let determine_lift_rule c env trm prev_rules sigma =
  let l = get_lifting c in
  let lifted_opt = lookup_lifting (lift_to l, lift_back l, trm) in
  if Option.has_some lifted_opt then
    sigma, Optimization (GlobalCaching (Option.get lifted_opt))
  else if is_cached c trm then
    sigma, Optimization (LocalCaching (lookup_cache c trm))
  else if is_opaque c trm then
    sigma, Optimization OpaqueConstant
  else if is_section_retraction c prev_rules trm then
    sigma, if l.is_fwd then Retraction else Section
  else if isApp trm && applies (lift_to l) trm then
    sigma, Internalize
  else
    let sigma, args_o = is_equivalence c env trm prev_rules sigma in
    if Option.has_some args_o then
      let typ, args = Option.get args_o in
      sigma, Equivalence (typ, args)
    else
      let sigma, to_proj_o = is_coh c env trm prev_rules sigma in
      if Option.has_some to_proj_o then
        let proj, args, trm_eta = Option.get to_proj_o in
        if arity trm_eta > arity trm then
          sigma, Optimization (LazyEta trm_eta)
        else
          sigma, Coherence (reduce_coh c, (proj, args))
      else
        let sigma, packed_constr_o = is_packed_constr c env sigma trm in
        if Option.has_some packed_constr_o then
          let i, args, simplify = Option.get packed_constr_o in
          let lifted_constr = (get_lifted_constrs c).(i) in
          if List.length args > 0 then
            match l.orn.kind with
            | UnpackSigma ->
               if l.is_fwd then
                 sigma, LiftConstr (simplify, (lifted_constr, args))
               else
                 (* needed for termination (TODO remove) *)
                 sigma, Optimization (SmartLiftConstr (lifted_constr, args))
            | _ ->
               sigma, LiftConstr (simplify, (lifted_constr, args))
          else
            sigma, LiftConstr (simplify, (lifted_constr, args))
        else
          let sigma, is_identity_o = is_identity c env trm prev_rules sigma in
          if Option.has_some is_identity_o then
            let lifted_id, args = Option.get is_identity_o in
            sigma, LiftIdentity (reduce_lifted_id c, (lifted_id, args))
          else
            let sigma, is_elim_o = is_eliminator c env trm sigma in
            if Option.has_some is_elim_o then
              let env_elim, trm_eta, trm_elim, pms, nargs, opaque = Option.get is_elim_o in
              if new_rels2 env_elim env > 0 then
                sigma, Optimization (LazyEta trm_eta)
              else
                sigma, LiftElim (trm_elim, pms, nargs, opaque)
            else
              match kind trm with
              | App (f, args) ->
                 let how_reduce_o = can_reduce_now c env trm in
                 if Option.has_some how_reduce_o then
                   let how_reduce = Option.get how_reduce_o in
                   sigma, Optimization (SimplifyProjectId (how_reduce, (f, args)))
                 else
                   sigma, Optimization (AppLazyDelta (f, args))
              | Construct (((i, i_index), _), u) ->
                 let ind = mkInd (i, i_index) in
                 let (a_typ, b_typ) = get_types c in
                 let b_typ =
                   match l.orn.kind with
                   | Algebraic _ ->
                      let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_typ)).packer in
                      first_fun b_typ_packed
                   | _ ->
                      zoom_term zoom_lambda_term env b_typ
                 in
                 if equal ind (directional l a_typ b_typ) then
                   let sigma, trm_eta = expand_eta env sigma trm in
                   sigma, Optimization (LazyEta trm_eta)
                 else
                   sigma, CIC (kind trm)
              | Const (co, u) ->
                 sigma, Optimization (ConstLazyDelta (co, u))
              | _ ->
                 sigma, CIC (kind trm)

