open Constr
open Liftconfig
open Caching
open Lifting
open Zooming
open Apputils
open Promotion
open Sigmautils
open Reducers
open Funutils
open Stateutils
open Hypotheses
open Indexing

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
 *)
type lift_optimization =
| GlobalCaching of constr
| LocalCaching of constr
| OpaqueConstant
| SimplifyProjectId of reducer * (constr * constr array)
| LazyEta of constr
| AppLazyDelta of constr * constr array
| ConstLazyDelta of Names.Constant.t Univ.puniverses
                                     
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
 * 4. OPTIMIZATION runs when some optimization applies.
 *
 * 5. ETA runs when we lift eta expansion of constructors.
 *    The rule returns the lifted eta expansion function and its arguments, as
 *    well as a custom reduction function to apply it to the
 *    lifted arguments (for efficiency and to ensure termination).
 *
 * 6. IOTA runs when we lift iota reduction of eliminator cases.
 *
 * 7. CIC runs when no optimization applies and none of the other rules
 *    apply. It returns the kind of the Gallina term.
 *)
type lift_rule =
| Equivalence of constr * constr list
| LiftConstr of reducer * (constr * constr list)
| Eta of reducer * (constr * constr list)
| Iota of constr * constr list
| Coherence of reducer * (constr * constr list) (* TODO move to optimization? *)
| Optimization of lift_optimization
| CIC of (constr, types, Sorts.t, Univ.Instance.t) kind_of_term

(* --- Termination conditions --- *)

(*
 * DEVOID supports some equivalences where the the type B refers in some
 * way to the type A. Work support these equivalences is preliminary,
 * but the way that DEVOID currently handles this is by threading the
 * history of the lifting operation through each recursive call.
 * When appropriate, based on the history, for certain rules,
 * certain termination conditions fire. If those conditions fire, we
 * skip those rules and continue.
 *
 * This can also help us catch bugs in lifting by preventing infinite
 * recursion when we would otherwise accidentally recurse on the same subterm
 * over and over again.
 *)

(* Termination condition for EQUIVALENCE *)
let terminate_eqv prev_rules args_o =
  let args = Option.get args_o in
  List.exists
    (fun prev_rule ->
      match prev_rule with
      | Equivalence (_, args') when List.length args = List.length args' ->
         (* the lifted type refers to the unlifted type *)
         List.for_all2 equal args args'
      | _ ->
         false)
    prev_rules

(* Termination condition for LIFT-CONSTR *)
let terminate_constr prev_rules f args=
  List.exists
    (fun prev_rule ->
      match prev_rule with
      | LiftConstr (simplify, (f', args')) when equal f f' ->
         (* the lifted contructor refers to the unlifted constructor *)
         equal f f' && List.for_all2 equal args args'
      | _ ->
         false)
    prev_rules

 (* Termination condition for COHERENCE *)
let terminate_coh prev_rules proj_o env trm sigma =
  let f, args, _ = Option.get proj_o in
  exists_state
    (fun prev_rule sigma ->
      match prev_rule with
      | Coherence (_, (f', args')) when equal f f' ->
         (* the lifted applications refers to the unlifted application *)
         if List.for_all2 equal args args' then
           sigma, true
         else
           let sigma, projected = reduce_term env sigma (mkAppl (f', args')) in
           sigma, equal trm projected
      | _ ->
         sigma, false)
    prev_rules
    sigma

(* Termination condition for ETA *)
let terminate_eta prev_rules args_o =
  let args = Option.get args_o in
  List.exists
    (fun prev_rule ->
      match prev_rule with
      | Eta (_, (_, args')) ->
         (* The lifted eta refers to the unlifted eta *)
         List.for_all2 equal args args'
      | _ ->
         false)
    prev_rules

(* --- Premises --- *)

(* Premises for EQUIVALENCE *)
let is_equivalence c env trm prev_rules sigma =
  let sigma, args_o = is_from c env trm sigma in
  if Option.has_some args_o then
    if not (terminate_eqv prev_rules args_o) then
      let (a_typ, b_typ) = get_types c in
      let typ = if (get_lifting c).is_fwd then b_typ else a_typ in
      sigma, Some (typ, Option.get args_o)
    else
      sigma, None
  else
    sigma, None
             
(* Premises for LIFT-CONSTR *)
let is_constr c prev_rules env trm sigma =
  let sigma, app_o = applies_constr_eta c env trm sigma in
  if Option.has_some app_o then
    let i, args = Option.get app_o in
    let lifted_constr = (get_lifted_constrs c).(i) in
    if not (terminate_constr prev_rules lifted_constr args) then
      sigma, Some (lifted_constr, args, reduce_constr_app c)
    else
      sigma, None
  else
    sigma, None
             
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

(* Premises for ETA *)
let is_eta c env trm prev_rules sigma =
  let sigma, args_o = applies_eta c env trm sigma in
  if Option.has_some args_o then
    if not (terminate_eta prev_rules args_o) then
      sigma, Some (reduce_lifted_eta c, (get_lifted_eta c, Option.get args_o))
    else
      sigma, None
  else
    sigma, None

(* Premises for IOTA *)
let is_iota c env trm prev_rules sigma =
  let sigma, app_o = applies_iota c env trm sigma in
  if Option.has_some app_o then
    let i, args = Option.get app_o in
    sigma, Some ((get_lifted_iota c).(i), args)
  else
    sigma, None

(* Premises for LIFT-ELIM *)
let is_eliminator c env trm sigma =
  applies_elim c env trm sigma

(*
 * Given a term, determine the appropriate lift rule to run
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
        let sigma, constr_o = is_constr c prev_rules env trm sigma in
        if Option.has_some constr_o then
          let f, args, simplify = Option.get constr_o in
          sigma, LiftConstr (simplify, (f, args))
        else
          let sigma, is_eta_o = is_eta c env trm prev_rules sigma in
          if Option.has_some is_eta_o then
            let simplify, (f, args) = Option.get is_eta_o in
            sigma, Eta (simplify, (f, args))
          else
            let sigma, is_iota_o = is_iota c env trm prev_rules sigma in
            if Option.has_some is_iota_o then
              let (f, args) = Option.get is_iota_o in
              sigma, Iota (f, args)
            else
              let sigma, is_elim_o = is_eliminator c env trm sigma in
              if Option.has_some is_elim_o then
                let eta_o, args = Option.get is_elim_o in
                if Option.has_some eta_o then
                  sigma, Optimization (LazyEta (Option.get eta_o))
                else
                  let lifted_dep_elim = get_lifted_dep_elim c in
                  sigma, Optimization (AppLazyDelta (lifted_dep_elim, Array.of_list args))
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

