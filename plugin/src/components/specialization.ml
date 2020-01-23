(*
 * Specialization component
 *)

open Lifting
open Hofs
open Substitution
open Utilities
open Indexing
open Abstraction
open Constr
open Inference
open Typehofs
open Reducers
open Apputils
open Sigmautils
open Envutils
open Stateutils
open Desugarprod
open Funutils
open Zooming
open Hypotheses
open Debruijn
open Environ
open Ornerrors
open Promotion

(* --- Packing--- *)

(*
 * Pack inside of a sigT type
 *)
let pack env off unpacked sigma =
  let sigma, typ = reduce_type env sigma unpacked in
  let index = get_arg off typ in
  let sigma, index_type = infer_type env sigma index in
  let sigma, packer = abstract_arg env sigma off typ in
  sigma, pack_existT {index_type; packer; index; unpacked}

(*
 * Pack inside of a prod type
 *)
let pack_prod env unpacked sigma =
  let sigma, typ = infer_type env sigma unpacked in
  let typ_f = unwrap_definition env (first_fun typ) in
  let typ_args = unfold_args typ in
  let typ_red = mkAppl (typ_f, typ_args) in
  let sigma, typ_red = reduce_term env sigma typ_red in
  sigma, eta_prod_rec unpacked typ_red

(* --- Lifting --- *)

(*
 * Lift
 *)
let lift env l trm sigma =
  let f = lift_to l in
  let sigma, typ_args =
    match l.orn.kind with
    | Algebraic (_, off) ->
       non_index_typ_args off env sigma trm
    | CurryRecord ->
       on_red_type
         reduce_nf
         (fun env sigma typ ->
           if l.is_fwd then
             sigma, unfold_args typ
           else
             (* v TODO common functionality w/ search, move somewhere common *)
             (* TODO explain the reason we need this *)
             (* TODO try to work around by substituting with constant version earlier so as to avoid this *)
             let f = unwrap_definition env f in
             let env_f, f_bod = zoom_lambda_term env f in
             let sigma, typ_app = reduce_type env_f sigma (mkRel 1) in
             let typ_app_f = unwrap_definition env_f (first_fun typ_app) in
             let typ_app_args = unfold_args typ_app in
             let typ_app_red = mkAppl (typ_app_f, typ_app_args) in
             let sigma, typ_app_red = reduce_term env sigma typ_app_red in
             let abs_args = prod_typs_rec typ_app_red in
             let conc_args = prod_typs_rec (shift_by (new_rels2 env_f env) typ) in
             let subbed = (* TODO move some of this ... *) (* TODO may fail sometimes, do better? try to make it fail ... *)
               List.fold_right2
                 (fun abs conc -> all_eq_substs (abs, conc))
                 abs_args
                 conc_args
                 typ_app
             in
             let subbed = unshift_by (new_rels2 env_f env) subbed in
             sigma, unfold_args subbed)
         env
         sigma
         trm
  in sigma, mkAppl (f, snoc trm typ_args)
              
(*
 * Pack arguments and lift
 *)
let pack_lift env l arg sigma =
  let sigma, arg =
    match l.orn.kind with
    | Algebraic (_, off) ->
       map_backward
         (fun (sigma, t) -> pack env off t sigma)
         l
         (sigma, arg)
    | CurryRecord ->
       map_backward
         (fun (sigma, t) -> pack_prod env t sigma)
         l
         (sigma, arg)
  in lift env l arg sigma
       
(* --- Refolding --- *)

(* 
 * The implementation uses a refolding
 * algorithm to determine the constructor lifting rules, so that
 * they do not need to depend on ordering information. 
 *)

(*
 * Get all recursive constants
 *)
let rec all_recursive_constants env trm =
  let consts = all_const_subterms (fun _ _ -> true) (fun u -> u) () trm in
  let non_axioms =
    List.map
      Option.get
      (List.filter
         (Option.has_some)
         (List.map
            (fun c ->
              try
                let def = unwrap_definition env c in
                if not (equal def c || isInd def) then
                  Some (c, def)
                else
                  None
              with _ ->
                None)
            consts))
  in
  let non_axiom_consts = List.map fst non_axioms in
  let defs = List.map snd non_axioms in
  unique
    equal
    (List.append
       non_axiom_consts
       (List.flatten (List.map (all_recursive_constants env) defs)))

(*
 * Fold back constants after applying a function to the normalized form
 * Makes the produced lifted constructors dramatically nicer and faster
 * when they refer to functions
 *)
let fold_back_constants env f trm =
  bind
    (bind (fun sigma -> reduce_nf env sigma trm) f)
    (fun x ->
      fold_left_state
        (fun red lifted sigma ->
          all_conv_substs env sigma (lifted, lifted) red)
        x
        (all_recursive_constants env trm))
    
(*
 * Refolding an applied ornament in the forward direction, 
 * when the ornament application produces an existT term.
 *)
let refold_packed l orn env arg app_red sigma =
  match l.orn.kind with
  | Algebraic (_, off) ->
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let orn_app = mkAppl (orn, snoc arg typ_args) in
     let orn_app_red = reduce_stateless reduce_nf env sigma orn_app in
     let app_red_ex = dest_existT app_red in
     let orn_app_red_ex = dest_existT orn_app_red in
     let abstract env sigma = abstract_arg env sigma off in
     let sigma, packer = on_red_type_default abstract env sigma orn_app_red_ex.unpacked in
     let index_type = app_red_ex.index_type in
     let arg_sigT = { index_type ; packer } in
     let sigma, arg_indexer = Util.on_snd (project_index arg_sigT) (lift env l arg sigma) in
     let sigma, arg_value = Util.on_snd (project_value arg_sigT) (lift env l arg sigma) in
     let refold_index = all_eq_substs (orn_app_red_ex.index, arg_indexer) in
     let refold_value = all_eq_substs (orn_app_red_ex.unpacked, arg_value) in
     let refolded = refold_index (refold_value app_red_ex.unpacked) in
     pack env off refolded sigma
  | _ ->
     raise NotAlgebraic
       
(*
 * Refolding an applied ornament in the backwards direction,
 * when the ornament application eliminates over the projections.
 *)
let refold_projected l orn env arg app_red sigma =
  match l.orn.kind with
  | Algebraic (_, off) ->
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let orn_app = mkAppl (orn, snoc arg typ_args) in
     let orn_app_red = reduce_stateless reduce_nf env sigma orn_app in
     let sigma, lifted = lift env l arg sigma in
     sigma, all_eq_substs (orn_app_red, lifted) app_red
  | _ ->
     raise NotAlgebraic

(*
 * Top-level refolding
 *)
let refold l env orn trm args sigma =
  let refolder = if l.is_fwd then refold_packed else refold_projected in
  let refold_all = fold_right_state (refolder l orn env) args in
  fold_back_constants env refold_all trm sigma




             

