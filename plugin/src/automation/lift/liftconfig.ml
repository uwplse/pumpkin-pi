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

(*
 * Lifting configuration
 *)

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
    proj_rules : types array;
    optimize_proj_packed_rules :
      (constr -> bool) * ((constr * (constr -> constr)) list);
    cache : temporary_cache;
    opaques : temporary_cache
  }

(* --- Auxiliary functions about configuration --- *)

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
let is_from =
  is_from_with_conv (fun env t1 t2 sigma -> convertible env sigma t1 t2)

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
