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
open Convertibility
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

(*
 * This module takes in a Coq term that we are lifting and determines
 * the appropriate lifting rule to run
 *)

(* --- Convenient shorthand --- *)

let convertible env t1 t2 sigma =
  if equal t1 t2 then
    sigma, true
  else
    convertible env sigma t1 t2

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
 *    the type equivalence we are lifting across. This carries the arguments
 *    to the lifted type.
 *
 * 2. LIFT-CONSTR runs when we lift constructors of the type in the equivalence.
 *    This carries the lifted constructor and the arguments.
 *
 * 3. COHERENCE runs when we lift projections of the type in the equivalence.
 *    This carries the term we are projecting, the lifted projection, and the
 *    arguments.
 *
 * 4. LIFT-ELIM runs when we lift applications of eliminators of the type
 *    in the equivalence. This carries the application of the eliminator,
 *    as well as the lifted parameters.
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
 *    The rule returns the lifted identity function and its argument.
 *
 * 10. CIC runs when no optimization applies and none of the other rules
 *    apply. It returns the kind of the Gallina term.
 *)
type lift_rule =
| Equivalence of constr list
| LiftConstr of constr * constr list
| LiftIdentity of constr * constr list
| Coherence of constr * constr * constr list
| LiftElim of elim_app * constr list
| Section
| Retraction
| Internalize
| Optimization of lift_optimization
| CIC of (constr, types, Sorts.t, Univ.Instance.t) kind_of_term

(* --- Premises --- *)

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
         (* we treat any existential of the right type as a constructor *)
         let sigma_right, args_opt = type_is_from c env trm sigma in
         if Option.has_some args_opt then
           let typ_args = Option.get args_opt in
           let sigma, b_sig_eq =
             let b_sig_eq_typ = mkAppl (fst (get_types c), typ_args) in
             Util.on_snd dest_sigT (reduce_term env sigma_right b_sig_eq_typ)
           in
           let s, h_eq =
             let trm_ex = dest_existT trm in
             trm_ex.index, trm_ex.unpacked
           in
           let i_b, b =
             if is_or_applies existT s then
               let index_ex = dest_existT s in
               index_ex.index, index_ex.unpacked
             else
               projections (dest_sigT b_sig_eq.index_type) s
           in sigma, Some (0, List.append typ_args [i_b; b; h_eq])
         else
           sigma, None
       else (* <-- TODO correct or not? needed? also, this is slow *)
         let sigma_right, args_opt = type_is_from c env trm sigma in
         if Option.has_some args_opt then
           let typ_args = Option.get args_opt in
           if (is_or_applies eq_rect trm) then (* TODO better as elim rule. maybe want whole thing as elim rule and no constrs? *)
             let sigma, trm = expand_eta env sigma_right trm in
             let eq_args = Array.of_list (unfold_args trm) in
             let i_b = eq_args.(1) in
             let b = eq_args.(3) in
             let h_eq = eq_args.(5) in
             if is_or_applies eq_refl h_eq then
               sigma, None
             else
               sigma, Some (0, List.append typ_args [i_b; b; h_eq])
           else
             if isApp trm && isConstruct (first_fun trm) then (* TODO blehhh *)
               (* TODO get correct args; then return actual constr; then refold correctly *)
               let i_b = last typ_args in
               let sigma, i_b_typ = reduce_type env sigma_right i_b in
               let b = trm in
               let h_eq = apply_eq_refl { typ = i_b_typ; trm = i_b } in
               sigma, Some (0, List.append typ_args [i_b; b; h_eq])
             else
               sigma, None
         else
           sigma, None
  else
    sigma, None

(* Premises for LIFT-IDENTITY *)
let is_identity c env trm skip_id sigma =
  if skip_id then (* prevent infinite recursion *)
    sigma, None
  else
    match kind trm with
    | Rel _ ->
       applies_id_eta c env trm sigma
    | App _ ->
       (* TODO gradually combine back w/ rule, but need to phase out old code first *)
       (match (get_lifting c).orn.kind with
        | Algebraic _ when (not (get_lifting c).is_fwd) ->
           applies_id_eta c env trm sigma
        | _ ->
           sigma, None)
    | _ ->
       sigma, None

(* Auxiliary function for premise for LIFT-PROJ *)
let check_is_proj c env trm proj_is =
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
              let sigma, trm_eta = expand_eta env sigma trm in
              let env_b, b = zoom_lambda_term env trm_eta in
              let args = unfold_args b in
              if List.length args = 0 then
                check_is_proj_i (i + 1) tl sigma
              else
                (* attempt unification *)
                try
                  let sigma, eargs =
                    map_state
                      (fun _ sigma ->
                        let sigma, (earg_typ, _) = new_type_evar env_b sigma univ_flexible in
                        let sigma, earg = new_evar env_b sigma earg_typ in
                        sigma, EConstr.to_constr sigma earg)
                      (mk_n_rels (arity proj_i))
                      sigma
                  in
                  let sigma, proj_app = reduce_term env_b sigma (mkAppl (proj_i, eargs)) in
                  let sigma = the_conv_x env_b (EConstr.of_constr b) (EConstr.of_constr proj_app) sigma in
                  sigma, Some (last eargs, i, all_but_last eargs, trm_eta) 
                with _ ->
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
  let proj_rules = get_proj_map c in
  if List.length proj_rules = 0 then
    ret None
  else
    check_is_proj c env trm (List.map fst proj_rules)

(* Premises for LIFT-ELIM *)
let is_eliminator c env trm sigma =
  let l = get_lifting c in
  if l.orn.kind = UnpackSigma then
    sigma, None
  else
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
           if (not l.is_fwd) && l.orn.kind = CurryRecord then
             let (final_args, post_args) = take_split 1 trm_elim.final_args in
             let sigma, is_from = type_is_from c env_elim (List.hd final_args) sigma in
             if Option.has_some is_from then
               sigma, Some (env_elim, trm_eta, trm_elim, Option.get is_from)
             else
               sigma, None
           else
             if l.orn.kind = CurryRecord then
               let typ_f = first_fun (zoom_term zoom_lambda_term env_elim (snd (get_types c))) in
               let sigma, to_typ_prod = specialize_delta_f env_elim typ_f trm_elim.pms sigma in
               let to_elim = dest_prod to_typ_prod in
               let pms = [to_elim.Produtils.typ1; to_elim.Produtils.typ2] in
               sigma, Some (env_elim, trm_eta, trm_elim, pms)
             else
               sigma, Some (env_elim, trm_eta, trm_elim, trm_elim.pms)
         else
           sigma, None
       else
         sigma, None
    | _ ->
       sigma, None

(*
 * Given a term, determine the appropriate lift rule to run
 *)
let determine_lift_rule c env trm skip_id sigma =
  let l = get_lifting c in
  let lifted_opt = lookup_lifting (lift_to l, lift_back l, trm) in
  if Option.has_some lifted_opt then
    sigma, Optimization (GlobalCaching (Option.get lifted_opt))
  else if is_cached c trm then
    sigma, Optimization (LocalCaching (lookup_cache c trm))
  else if is_opaque c trm then
    sigma, Optimization OpaqueConstant
  else
    let sigma, args_o = is_from c env trm sigma in
    if Option.has_some args_o then
      sigma, Equivalence (Option.get args_o)
    else
      let sigma, to_proj_o = is_proj c env trm sigma in
      if Option.has_some to_proj_o then
        let to_proj, i, args, trm_eta = Option.get to_proj_o in
        if arity trm_eta > arity trm then
          sigma, Optimization (LazyEta trm_eta)
        else
          let (_, p) = List.nth (get_proj_map c) i in
          sigma, Coherence (to_proj, p, args)
      else
        let sigma, i_and_args_o = is_packed_constr c env sigma trm in
        if Option.has_some i_and_args_o then
          let i, args = Option.get i_and_args_o in
          let lifted_constr = (get_lifted_constrs c).(i) in
          if List.length args > 0 then
            match l.orn.kind with
            | SwapConstruct _ ->
               sigma, LiftConstr (lifted_constr, args)
            | UnpackSigma ->
               if l.is_fwd then
                 sigma, LiftConstr (lifted_constr, args)
               else
                 (* needed for termination *)
                 sigma, Optimization (SmartLiftConstr (lifted_constr, args))
            | _ ->
               if not l.is_fwd then
                 sigma, LiftConstr (lifted_constr, args)
               else
                 sigma, Optimization (SmartLiftConstr (lifted_constr, args))
          else
            sigma, LiftConstr (lifted_constr, args)
        else if isApp trm && applies (lift_back l) trm then
          sigma, if l.is_fwd then Retraction else Section
        else if isApp trm && applies (lift_to l) trm then
          sigma, Internalize
        else
          let sigma, is_identity_o = is_identity c env trm skip_id sigma in
          if Option.has_some is_identity_o then
            let typ_args = Option.get is_identity_o in
            let args = snoc trm typ_args in
            let lifted_id = get_lifted_id_eta c in
            sigma, LiftIdentity (lifted_id, args)
          else
            let sigma, is_elim_o = is_eliminator c env trm sigma in
            if Option.has_some is_elim_o then
              let env_elim, trm_eta, trm_elim, pms = Option.get is_elim_o in
              if new_rels2 env_elim env > 0 then
                sigma, Optimization (LazyEta trm_eta)
              else
                sigma, LiftElim (trm_elim, pms)
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
