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
open Typehofs
open Environ
open Indexing

(* TODO top-level comment *)

(* --- Convenient shorthand (TODO move/comment) --- *)

let dest_sigT_type = on_red_type_default (ignore_env dest_sigT)

(* TODO move/comment *)
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
 * 4. SimplifyProjectPacked: When we see projections of packed terms
 *    (for example, projT1 (existT ...)), we reduce eagerly rather than
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
| SimplifyProjectPacked of reducer * (constr * constr array)
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
 *    in the equivalence. This carries the application of the eliminator.
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
 * 9. LIFT-PACK runs when we must repack for non-primitive projections.
 *    I hope to understand when we need this at some point; I suspect
 *    it should be a part of other rules.
 *
 * 10. CIC runs when no optimization applies and none of the other rules
 *    apply. It returns the kind of the Gallina term.
 *)
type lift_rule =
| Equivalence of constr list
| LiftConstr of constr * constr list
| LiftPack
| Coherence of constr * constr * constr list
| LiftElim of elim_app
| Section
| Retraction
| Internalize
| Optimization of lift_optimization
| CIC of (constr, types, Sorts.t, Univ.Instance.t) kind_of_term

(* --- Premises --- *)

(* Premises for LIFT-CONSTR *)
let is_packed_constr c env sigma trm =
  let l = get_lifting c in
  let constrs = get_constrs c in
  let is_packed_inductive_constr is_packed unpack trm =
    if is_packed trm then
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
    else
      sigma, None
  in
  if isConstruct trm || (isApp trm && l.is_fwd) then
    is_packed_inductive_constr (fun _ -> true) id trm
  else
    match l.orn.kind with
    | Algebraic _ ->
       is_packed_inductive_constr (is_packed c) last_arg trm
    | CurryRecord ->
       if is_packed c trm then
          let sigma_right, args_opt = type_is_from c env trm sigma in
          if Option.has_some args_opt then
            let sigma = sigma_right in
            let constr = constrs.(0) in
            let pms = Option.get args_opt in
            let args = pair_projections_eta_rec_n trm (arity constr - List.length pms) in
            sigma, Some (0, List.append pms args)
          else
            sigma, None
       else
         sigma, None

(* Premises for LIFT-PACK *)
let is_pack c env sigma trm =
  let l = get_lifting c in
  let right_type trm = type_is_from c env trm sigma in
  if l.is_fwd then
    if isRel trm then
      (* pack *)
      Util.on_snd Option.has_some (right_type trm)
    else
      sigma, false
  else
    match l.orn.kind with
    | Algebraic (_, _) ->
       if is_packed c trm then
         (* unpack *)
         Util.on_snd Option.has_some (right_type trm)
       else
         sigma, false
    | CurryRecord ->
       (* taken care of by constructor rule *)
       sigma, false

(* Auxiliary function for premise for LIFT-PROJ (TODO clean/use unification where possible) *)
let check_is_proj c env trm proj_is =
  let l = get_lifting c in
  let right_type = type_is_from c in
  let num_projs = List.length proj_is in
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
                if l.orn.kind = CurryRecord && not l.is_fwd then
                  (* TODO hacky; clean/refactor common *)
                  let rec get_arg j args =
                    let a = last args in
                    if j = 0 then
                      a
                    else
                      get_arg (j - 1) (unfold_args a)
                  in
                  let j = if i = num_projs - 1 then i - 1 else i in
                  try
                    let a = get_arg j args in
                    let sigma_right, typ_args_o = right_type env_b a sigma in
                    if Option.has_some typ_args_o then
                      let typ_args = Option.get typ_args_o in
                      let p_app = mkAppl (proj_i, snoc a typ_args) in
                      branch_state (* TODO check w/ pms *)
                        (convertible env_b p_app)
                        (fun _ -> ret (Some (a, i, typ_args, trm_eta)))
                        (fun _ -> check_is_proj_i (i + 1) tl)
                        b
                        sigma_right
                    else
                      check_is_proj_i (i + 1) tl sigma       
                  with _ ->
                    check_is_proj_i (i + 1) tl sigma
                else
                  let a = last args in
                  let sigma_right, typ_args_o = right_type env_b a sigma in
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
  let proj_rules = get_proj_map c in
  if List.length proj_rules = 0 then
    ret None
  else
    check_is_proj c env trm (List.map fst proj_rules)

(*
 * Premises for LIFT-ELIM
 * For optimization, if true, return the eta-expanded term
 *
 * TODO clean
 *)
let is_eliminator c env trm sigma =
  let l = get_lifting c in
  let (a_typ, b_typ) = get_types c in
  let b_typ =
    if (not l.is_fwd) && l.orn.kind = CurryRecord then
      prod
    else if l.orn.kind = CurryRecord then
      zoom_term zoom_lambda_term env b_typ
    else
      let b_typ_packed = dummy_index env sigma (dest_sigT (zoom_term zoom_lambda_term env b_typ)).packer in
      first_fun b_typ_packed
  in
  let f = first_fun trm in
  match kind f with
  | Const (k, u) ->
     let maybe_ind = inductive_of_elim env (k, u) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       let is_elim = equal (mkInd (ind, 0)) (directional l a_typ b_typ) in
       if is_elim then
         let sigma, trm_eta = expand_eta env sigma trm in
         if (not l.is_fwd) && l.orn.kind = CurryRecord then
           let env_elim, trm_b = zoom_lambda_term env trm_eta in
           let sigma, trm_elim = deconstruct_eliminator env_elim sigma trm_b in
           let (final_args, post_args) = take_split 1 trm_elim.final_args in
           let sigma, is_from = type_is_from c env_elim (List.hd final_args) sigma in
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

(* TODO move/refactor/explain/finish *)
let determine_lift_rule c env trm sigma =
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
      let sigma, i_and_args_o = is_packed_constr c env sigma trm in
      if Option.has_some i_and_args_o then
        let i, args = Option.get i_and_args_o in
        let lifted_constr = (get_lifted_constrs c).(i) in
        if List.length args > 0 then
          if not l.is_fwd then
            sigma, LiftConstr (lifted_constr, args)
          else
            sigma, Optimization (SmartLiftConstr (lifted_constr, args))
        else
          sigma, LiftConstr (lifted_constr, args)
      else
        let sigma, is_pack = is_pack c env sigma trm in
        if is_pack then
          sigma, LiftPack
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
            let sigma, is_elim_o = is_eliminator c env trm sigma in
            if Option.has_some is_elim_o then
              let trm_eta = Option.get is_elim_o in
              if arity trm_eta > arity trm then
                sigma, Optimization (LazyEta trm_eta)
              else
                let sigma, trm_elim = deconstruct_eliminator env sigma trm in
                sigma, LiftElim trm_elim
            else
              match kind trm with
              | App (f, args) ->
                 if equal (lift_back l) f then
                   sigma, if l.is_fwd then Retraction else Section
                 else if equal (lift_to l) f then
                   sigma, Internalize
                 else
                   let how_reduce_o = can_reduce_now c trm in
                   if Option.has_some how_reduce_o then
                     (* optimize simplifying projections of packed terms, which are common (TODO move comment) *)
                     let how_reduce = Option.get how_reduce_o in
                     sigma, Optimization (SimplifyProjectPacked (how_reduce, (f, args)))
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
