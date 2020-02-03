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

(* --- Specialization --- *)

let specialize_using reduce env f args sigma =
  reduce env sigma (mkAppl (f, args))

let specialize = specialize_using reduce_term

let specialize_delta_f env f args sigma =
  let f = unwrap_definition env f in
  specialize env f args sigma
                                  
(* --- Packing--- *)

(*
 * Pack inside of a sigT or prod type
 *)
let pack env l unpacked sigma =
  match l.orn.kind with
  | Algebraic (_, (_, off)) ->
     let sigma, typ = reduce_type env sigma unpacked in
     let index = get_arg off typ in
     let sigma, index_type = infer_type env sigma index in
     let sigma, packer = abstract_arg env sigma off typ in
     sigma, pack_existT {index_type; packer; index; unpacked}
  | CurryRecord ->
     let sigma, typ = infer_type env sigma unpacked in
     let sigma, typ_red = specialize_delta_f env (first_fun typ) (unfold_args typ) sigma in
     sigma, eta_prod_rec unpacked typ_red

(* --- Lifting --- *)

(*
 * Lift
 *)
let lift env l trm typ_args sigma =
  let f = lift_to l in
  sigma, mkAppl (f, snoc trm typ_args)
       
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
  | Algebraic (_, (_, off)) ->
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
     let app_red_ex = dest_existT app_red in
     let orn_app_red_ex = dest_existT orn_app_red in
     let abstract env sigma = abstract_arg env sigma off in
     let sigma, packer = on_red_type_default abstract env sigma orn_app_red_ex.unpacked in
     let index_type = app_red_ex.index_type in
     let arg_sigT = { index_type ; packer } in
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let sigma, arg_indexer = Util.on_snd (project_index arg_sigT) (lift env l arg typ_args sigma) in
     let sigma, arg_value = Util.on_snd (project_value arg_sigT) (lift env l arg typ_args sigma) in
     let refold_index = all_eq_substs (orn_app_red_ex.index, arg_indexer) in
     let refold_value = all_eq_substs (orn_app_red_ex.unpacked, arg_value) in
     let refolded = refold_index (refold_value app_red_ex.unpacked) in
     pack env l refolded sigma
  | _ ->
     raise NotAlgebraic
       
(*
 * Refolding an applied ornament in the backwards direction,
 * when the ornament application eliminates over the projections.
 *)
let refold_projected l orn env arg app_red sigma =
  match l.orn.kind with
  | Algebraic (_, (_, off)) ->
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
     let sigma, lifted = lift env l arg typ_args sigma in
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




             

