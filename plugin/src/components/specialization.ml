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
open Ornerrors
open Promotion
open Evarutil
open Evarconv

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
  | SwapConstruct _ ->
     sigma, unpacked

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
 *
 * TODO update comment, rename, refactor common code
 *)
let refold_packed l orn env arg app_red sigma =
  match l.orn.kind with
  | Algebraic (_, off) ->
     let sigma, typ_args = non_index_typ_args off env sigma arg in 
     let sigma, arg_typ = reduce_type env sigma arg in
     let earg_typ = EConstr.of_constr arg_typ in
     let sigma, earg = new_evar env sigma earg_typ in
     let earg = EConstr.to_constr sigma earg in
     let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc earg typ_args) sigma in
     let sigma, orn_app_red_conc = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
     let app_red_ex = dest_existT app_red in
     let orn_app_red_ex = dest_existT orn_app_red in
     let orn_app_red_conc_ex = dest_existT orn_app_red_conc in
     let abstract env sigma = abstract_arg env sigma off in
     let sigma, packer = on_red_type_default abstract env sigma orn_app_red_ex.unpacked in
     let index_type = app_red_ex.index_type in
     let arg_sigT = { index_type ; packer } in
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let sigma, arg_indexer = Util.on_snd (project_index arg_sigT) (lift env l earg typ_args sigma) in
     let sigma, arg_indexer_conc = Util.on_snd (project_index arg_sigT) (lift env l arg typ_args sigma) in
     let sigma, arg_value = Util.on_snd (project_value arg_sigT) (lift env l earg typ_args sigma) in
     let sigma, arg_value_conc = Util.on_snd (project_value arg_sigT) (lift env l arg typ_args sigma) in
     let refold_econv (abs_red, abs) trm =
       map_term_env_if_lazy
         (fun _ sigma _ t ->
           sigma, isApp t && not (is_or_applies (first_fun abs) t))
         (fun env sigma (abs_red, abs) t ->
           try
             let sigma = the_conv_x env (EConstr.of_constr t) (EConstr.of_constr abs_red) sigma in
             sigma, abs
           with _ ->
             sigma, t)
         (map_tuple Debruijn.shift)
         env
         sigma
         (abs_red, abs)
         trm
     in
     let refold_index_fast = all_eq_substs (orn_app_red_conc_ex.index, arg_indexer_conc) in
     let refold_value_fast = all_eq_substs (orn_app_red_conc_ex.unpacked, arg_value_conc) in
     let refold_index = refold_econv (orn_app_red_ex.index, arg_indexer) in
     let refold_value = refold_econv (orn_app_red_ex.unpacked, arg_value) in
     let sigma, refolded_value = refold_value (refold_value_fast app_red_ex.unpacked) in
     let sigma, refolded_index = refold_index (refold_index_fast refolded_value) in
     pack env l refolded_index sigma
  | SwapConstruct _ ->
     let sigma, arg_typ = reduce_type env sigma arg in
     let typ_args = unfold_args arg_typ in
     let earg_typ = EConstr.of_constr arg_typ in
     let sigma, earg = new_evar env sigma earg_typ in
     let earg = EConstr.to_constr sigma earg in
     let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc earg typ_args) sigma in
     let sigma, orn_app_red_conc = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
     let sigma, arg_value = lift env l earg typ_args sigma in
     let sigma, arg_value_conc = lift env l arg typ_args sigma in
     let refold_econv (abs_red, abs) trm =
       map_term_env_if_lazy
         (fun _ sigma _ t ->
           sigma, isApp t && not (is_or_applies (first_fun abs) t))
         (fun env sigma (abs_red, abs) t ->
           try
             let sigma = the_conv_x env (EConstr.of_constr t) (EConstr.of_constr abs_red) sigma in
             sigma, abs
           with _ ->
             sigma, t)
         (map_tuple Debruijn.shift)
         env
         sigma
         (abs_red, abs)
         trm
     in
     let refold_value_fast = all_eq_substs (orn_app_red_conc, arg_value_conc) in
     let refold_value = refold_econv (orn_app_red, arg_value) in
     refold_value (refold_value_fast app_red)
  | _ ->
     raise NotAlgebraic (* TODO better error *)
       
(*
 * Refolding an applied ornament in the backwards direction,
 * when the ornament application eliminates over the projections.
 *
 * TODO update comment, rename, refactor common code
 *)
let refold_projected l orn env arg app_red sigma =
  match l.orn.kind with
  | Algebraic (_, off) ->
     let sigma, typ_args = non_index_typ_args off env sigma arg in
     let sigma, arg_typ = reduce_type env sigma arg in
     let earg_typ = EConstr.of_constr arg_typ in
     let sigma, earg = new_evar env sigma earg_typ in
     let earg = EConstr.to_constr sigma earg in
     let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc earg typ_args) sigma in
     let sigma, orn_app_red_conc = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
     let sigma, arg_value = lift env l earg typ_args sigma in
     let sigma, arg_value_conc = lift env l arg typ_args sigma in
     let refold_econv (abs_red, abs) trm =
       map_term_env_if_lazy
         (fun _ sigma _ t ->
           sigma, isApp t && not (is_or_applies (first_fun abs) t))
         (fun env sigma (abs_red, abs) t ->
           try
             let sigma = the_conv_x env (EConstr.of_constr t) (EConstr.of_constr abs_red) sigma in
             sigma, abs
           with _ ->
             sigma, t)
         (map_tuple Debruijn.shift)
         env
         sigma
         (abs_red, abs)
         trm
     in
     let refold_value_fast = all_eq_substs (orn_app_red_conc, arg_value_conc) in
     let refold_value = refold_econv (orn_app_red, arg_value) in
     refold_value (refold_value_fast app_red)
  | SwapConstruct _ ->
     let sigma, arg_typ = reduce_type env sigma arg in
     let typ_args = unfold_args arg_typ in
     let earg_typ = EConstr.of_constr arg_typ in
     let sigma, earg = new_evar env sigma earg_typ in
     let earg = EConstr.to_constr sigma earg in
     let sigma, orn_app_red = specialize_using reduce_nf env orn (snoc earg typ_args) sigma in
     let sigma, orn_app_red_conc = specialize_using reduce_nf env orn (snoc arg typ_args) sigma in
     let sigma, arg_value = lift env l earg typ_args sigma in
     let sigma, arg_value_conc = lift env l arg typ_args sigma in
     let refold_econv (abs_red, abs) trm =
       map_term_env_if_lazy
         (fun _ sigma _ t ->
           sigma, isApp t && not (is_or_applies (first_fun abs) t))
         (fun env sigma (abs_red, abs) t ->
           try
             let sigma = the_conv_x env (EConstr.of_constr t) (EConstr.of_constr abs_red) sigma in
             sigma, abs
           with _ ->
             sigma, t)
         (map_tuple Debruijn.shift)
         env
         sigma
         (abs_red, abs)
         trm
     in
     let refold_value_fast = all_eq_substs (orn_app_red_conc, arg_value_conc) in
     let refold_value = refold_econv (orn_app_red, arg_value) in
     refold_value (refold_value_fast app_red)
  | _ ->
     raise NotAlgebraic (* TODO better error *)

(*
 * Top-level refolding
 *)
let refold l env orn trm args sigma =
  let refolder = if l.is_fwd then refold_packed else refold_projected in
  let refold_all = fold_right_state (refolder l orn env) args in
  fold_back_constants env refold_all trm sigma




             

