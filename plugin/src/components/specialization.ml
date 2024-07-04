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
open Promotion
open Evarutil
open Evarconv
open Zooming
open Equtils

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
  | Algebraic (_, off) ->
     let sigma, typ = reduce_type env sigma unpacked in
     let index = get_arg off typ in
     let sigma, index_type = infer_type env sigma index in
     let sigma, packer = abstract_arg env sigma off typ in
     sigma, pack_existT {index_type; packer; index; unpacked}
  | CurryRecord ->
     let sigma, typ = infer_type env sigma unpacked in
     let sigma, typ_red = specialize_delta_f env (first_fun typ) (unfold_args typ) sigma in
     sigma, eta_prod_rec unpacked typ_red
  | SwapConstruct _ | UnpackSigma ->
     sigma, unpacked
  | Custom _ ->
     failwith "unsupported"

(* --- Unpacking for unpack ornaments --- *)

let unpack_typ_args env_args b_sig_eq sigma =
  let eq_sig = dest_sigT b_sig_eq in
  let b_sig = dest_sigT eq_sig.index_type in
  let i_b_typ = b_sig.index_type in
  let b = b_sig.packer in
  let sigma, i_b =
    let env_eq_typ, eq_typ = zoom_lambda_term env_args eq_sig.packer in
    let sigma, eq_typ = reduce_nf env_eq_typ sigma eq_typ in
    sigma, Debruijn.unshift (dest_eq eq_typ).trm2
  in sigma, [i_b_typ; b; i_b]
              
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

(* Common refolding function with unification *)
let refold_econv env (abs_red, abs) trm sigma =
  map_term_env_if_lazy
    (fun _ sigma _ t ->
      sigma, isApp t && not (is_or_applies (first_fun abs) t))
    (fun env sigma (abs_red, abs) t ->
      try
        let sigma = unify_delay env sigma (EConstr.of_constr t) (EConstr.of_constr abs_red) in
        sigma, abs
      with _ ->
        sigma, t)
    (map_tuple Debruijn.shift)
    env
    sigma
    (abs_red, abs)
    trm
    
(*
 * Refolding an applied ornament in the forward direction
 *)
let refold_fwd l orn env arg app_red sigma =
  let sigma, arg_typ = reduce_type env sigma arg in
  let typ_args = unfold_args arg_typ in
  let earg_typ = EConstr.of_constr arg_typ in
  let sigma, earg = new_evar env sigma earg_typ in
  let earg = EConstr.to_constr ~abort_on_undefined_evars:false sigma earg in
  let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc earg typ_args) sigma in
  let sigma, orn_app_red_conc = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
  let sigma, arg_lift = lift env l earg typ_args sigma in
  let sigma, arg_lift_conc = lift env l arg typ_args sigma in
  match l.orn.kind with
  | Algebraic (_, off) ->
     let app_red_ex = dest_existT app_red in
     let orn_app_red_ex = dest_existT orn_app_red in
     let orn_app_red_conc_ex = dest_existT orn_app_red_conc in
     let abstract env sigma = abstract_arg env sigma off in
     let sigma, packer = on_red_type_default abstract env sigma orn_app_red_ex.unpacked in
     let index_type = app_red_ex.index_type in
     let arg_sigT = { index_type ; packer } in
     let arg_indexer = project_index arg_sigT arg_lift in
     let arg_indexer_conc = project_index arg_sigT arg_lift_conc in
     let arg_value = project_value arg_sigT arg_lift in
     let arg_value_conc = project_value arg_sigT arg_lift_conc in
     let refold_index_fast = all_eq_substs (orn_app_red_conc_ex.index, arg_indexer_conc) in
     let refold_value_fast = all_eq_substs (orn_app_red_conc_ex.unpacked, arg_value_conc) in
     let refold_index = refold_econv env (orn_app_red_ex.index, arg_indexer) in
     let refold_value = refold_econv env (orn_app_red_ex.unpacked, arg_value) in
     let sigma, refolded_value = refold_value (refold_value_fast app_red_ex.unpacked) sigma in
     let sigma, refolded_index = refold_index (refold_index_fast refolded_value)sigma in
     pack env l refolded_index sigma
  | _ ->
     let refold_value_fast = all_eq_substs (orn_app_red_conc, arg_lift_conc) in
     let refold_value = refold_econv env (orn_app_red, arg_lift) in
     refold_value (refold_value_fast app_red) sigma
       
(*
 * Refolding an applied ornament in the backwards direction
 *)
let refold_bwd l orn env arg app_red sigma =
  let sigma, arg_typ = reduce_type env sigma arg in
  let earg_typ = EConstr.of_constr arg_typ in
  let sigma, earg = new_evar env sigma earg_typ in
  let earg = EConstr.to_constr ~abort_on_undefined_evars:false sigma earg in
  let sigma, typ_args =
    match l.orn.kind with
    | Algebraic (_, off) ->
       non_index_typ_args off env sigma arg
    | _ ->
       sigma, unfold_args arg_typ
  in
  let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc earg typ_args) sigma in
  let sigma, orn_app_red_conc = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
  let sigma, arg_value = lift env l earg typ_args sigma in
  let sigma, arg_value_conc = lift env l arg typ_args sigma in
  let refold_value_fast = all_eq_substs (orn_app_red_conc, arg_value_conc) in
  let refold_value = refold_econv env (orn_app_red, arg_value) in
  refold_value (refold_value_fast app_red) sigma

(*
 * Top-level refolding
 *)
let refold l env orn trm args sigma =
  let refolder = if l.is_fwd then refold_fwd else refold_bwd in
  let refold_all = fold_right_state (refolder l orn env) args in
  fold_back_constants env refold_all trm sigma




             

