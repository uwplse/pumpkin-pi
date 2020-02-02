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
 *    we just return the cached lifted term.
 *
 * 2. LocalCaching: When a term is in the local lifting cache,
 *    we just return the cached lifted term.
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
 *
 * 5. LazyEta: We eta expand lazily, only when needed for correctness.
 *    The optimization is really this rule _not always_ fiting; this rule
 *    fires when we determine it is actually time to eta expand a term.
 *
 * 6. AppLazyDelta: This optimization skips delta-reduction for some
 *    function applications. This also includes the normal function
 *    application rule, since determining whether or not this optimization
 *    is possible requires "looking ahead" at some lifted subterms.
 *
 * 7. ConstLazyDelta: This optimization skips delta-reduction for some
 *    contants. It is similar to AppLazyDelta.
 *
 * 8. SmartLiftConstr: For certain equivalences, we can configure a faster
 *    version of LiftConstr. This rule fires when we've determined a faster
 *    version to run in its place.
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

(* TODO move/refactor/explain each/top comment/finish/simplify/move more optimizations up/clean/be consistent about how these recurse *)
type lift_rule =
| Equivalence of constr list
| LiftConstr of constr * constr list
| LiftPack
| Coherence of types * constr * constr list
| LiftElim of elim_app
| Section
| Retraction
| Internalize
| Optimization of lift_optimization
| CIC

(* --- Premises --- *)

(* Premises for LIFT-CONSTR *) (* TODO clean *)
let is_packed_constr c env sigma trm =
  let l = get_lifting c in
  let right_type trm sigma = type_is_from c env trm sigma in
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
     else if l.is_fwd then
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
       (match l.orn.kind with
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
               let (a_typ, _) = get_types c in
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

(* Premises for LIFT-PACK (TODO would returning args help optimize here?) *)
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

(* Auxiliary function for premise for LIFT-PROJ (TODO clean/use unification where possible) *)
let check_is_proj c env trm proj_is =
  let l = get_lifting c in
  let right_type = type_is_from c in
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
                  let j = if i = List.length proj_is then i - 1 else i in
                  (* ^ TODO why not length - 1? confused ... *)
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
        let lifted_constr = (get_lifted_constrs c).(i - 1) in
        if List.length args > 0 then
          if not l.is_fwd then
            sigma, LiftConstr (lifted_constr, args)
          else
            sigma, Optimization (SmartLiftConstr (lifted_constr, args))
        else
          sigma, LiftConstr (lifted_constr, args)
      else
        let sigma, run_lift_pack = is_pack c env sigma trm in
        if run_lift_pack then
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
                   sigma, CIC
              | Const (co, u) ->
                 sigma, Optimization (ConstLazyDelta (co, u))
              | _ ->
                 sigma, CIC
