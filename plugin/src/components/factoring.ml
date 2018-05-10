(*
 * A generalized version of the factoring component from PUMPKIN PATCH
 *)

open Term
open Environ
open Printing
open Coqterms
open Evd
open Names
open Debruijn
open Zooming
open Hofs
open Lifting
open Utilities

(* --- Shared logic --- *)

(*
 * Check if the term is the assumption (last term in the environment)
 *)
let is_assumption (assum : types) (env : env) (trm : types) : bool =
  convertible env trm assum

(*
 * Assume a term of type typ in an environment
 *)
let assume (assum : types) (env : env) (n : name) (typ : types) : env =
  let assum_ind = destRel assum in
  let (env_pop, non_assums) = lookup_pop (assum_ind - 1) env in
  let env_assum = push_local (n, typ) (pop_rel_context 1 env_pop) in
  List.fold_right push_rel non_assums env_assum

(* --- Type-level factoring --- *)

(* Deconstruct a product type (A -> B -> ... -> D) into A, B, ..., D *)
let rec factor_product (trm : types) : types list =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     t :: factor_product (unshift b)
  | _ ->
     []
       
(* --- Non-dependent factoring --- *)

type factors = (env * types) list

(*
 * Apply the assumption (last term in the environment) in the term
 *)
let apply_assumption assum (fs : factors) (trm : types) : types =
  if List.length fs > 0 then
    assum
  else
    trm

(*
 * Auxiliary path-finding function, once we are zoomed into a lambda
 * and the hypothesis we care about is the assumption (nth term
 * in the environment).
 *
 * The type path is in reverse order for efficiency, and is really
 * a list of environments (assumptions) and terms. When we refer to
 * "the end" it is the head of the list.
 *
 * The algorithm is as follows:
 * 1. If a term is the assumption, return a single path with
 *    the environment and term, which is the identity path.
 * 2. Otherwise, if it is an application:
 *    a. Recursively get the type path for each argument.
 *    b. If there are multiple nonempty type paths, then we cannot abstract out
 *       the assumption in a single function, so return the identity path.
 *    c. Otherwise, get the only non-empty path, then:
 *       i. Zoom in on each argument with the current assumption
 *       ii. Assume the conclusion of the element at the end of the path
 *       ii. Apply the function to the zoomed arguments in the environment
 *            with the new assumption, and add that to the end of the path
 *       iv. If applying the assumption at any point fails, return the empty
 *           path
 *
 * In other words, this is going as deep into the term as possible and
 * finding some Y for which X -> Y. It is then assuming Y,
 * and asking if there is some path from Y to the conclusion.
 *
 * It does not yet handle when Y depends on X. The find_path_dep
 * function should be able to construct trees for those cases.
 *)
let rec find_path (assum : types) (env : env) evd (trm : types) : factors =
  if is_assumption assum env trm then
    [(env, trm)]
  else
    match kind_of_term trm with
    | App (f, args) ->
       let paths = Array.map (find_path assum env evd) args in
       let filter_nonempty = List.filter (fun l -> List.length l > 0) in
       let nonempty_paths = filter_nonempty (Array.to_list paths) in
       if List.length nonempty_paths > 1 then
	 [(env, trm)]
       else if List.length nonempty_paths = 1 then
	 let path = List.hd nonempty_paths in
	 let (env_arg, arg) = List.hd path in
         let assume_arg i a = apply_assumption assum (Array.get paths i) a in
         let args_assumed = Array.mapi assume_arg args in
	 try
           let assum_ind = destRel assum in
           let t = unshift_by assum_ind (reduce_type env_arg evd arg) in
           let (n, _, _) = CRD.to_tuple @@ lookup_rel assum_ind env in
	   (assume assum env n t, mkApp (f, args_assumed)) :: path
	 with _ ->
	   []
       else
	 []
    | _ -> (* other terms not yet implemented *)
       []

(*
 * Given a term trm, if the type of trm is a function type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *
 * First zoom in all the way, then use the auxiliary path-finding
 * function.
 *)
let factor_term (assum : types) (env : env) (evd : evar_map) (trm : types) : factors =
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (reduce_term env trm) in
  let path_body = find_path assum env_zoomed evd trm_zoomed in
  List.map
    (fun (env, body) ->
      if is_assumption assum env body then
	(env, body)
      else
	let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
	(pop_rel_context 1 env, mkLambda (n, t, body)))
    path_body

(*
 * Reconstruct factors as terms using hypotheses from the environment.
 *
 * This basically produces a friendly external form in the correct order,
 * and using functions instead of closures. Inversion doesn't use this
 * for efficiency, but top-level functions probably want to.
 *)
let reconstruct_factors (fs : factors) : types list =
  List.map
    (fun (en, t) -> reconstruct_lambda en t)
    (List.tl (List.rev fs))

(* Apply factors to reconstruct a single term *)
let apply_factors (fs : factors) : types =
  let (env, base) = List.hd fs in
  let body =
    List.fold_right
      (fun (_, t) t_app ->
        mkApp (shift t, Array.make 1 t_app))
      (List.tl fs)
      base
  in reconstruct_lambda env body

(* debugging *)
let debug_factors (fs : factors) (s : string) : unit =
  List.iter (fun (e, f) -> debug_term e f s) fs

(* --- Dependent factoring --- *)
                        
type factor_tree = Unit | Factor of (env * types) * factor_tree list

(*
 * Assume but don't replace
 *)
let assume_no_replace (assum : types) (env : env) (n : name) (typ : types) : env =
  let assum_ind = destRel assum in
  let (env_pop, non_assums) = lookup_pop (assum_ind - 1) env in
  let non_assums =
    List.map
      (fun rel ->
        let (n, _, t) = CRD.to_tuple rel in
        (n, shift t))
      non_assums
  in
  let env_assum = push_local (n, typ) env_pop in
  List.fold_right push_local non_assums env_assum

(* 
 * Update the assumptions to search recursively
 *)
let assume_args off trees assum_ind tree_i factors_left args =
  let rec assume_rec tree_i factors_left args =
    match args with
    | h :: tl ->
       let (h', factors_left') =
         (match Array.get trees tree_i with
          | Factor (_, _) ->
             (mkRel (factors_left + assum_ind - 1), factors_left - 1)
          | Unit ->
             (shift_local assum_ind off h, factors_left))
       in h' :: (assume_rec (tree_i + 1) factors_left' tl)
    | [] ->
       []
  in assume_rec tree_i factors_left args

(* Debug dependent factors *)
let debug_factors_dep (fs : factor_tree) (s : string) : unit =
  let rec as_string fs =
    match fs with
    | Factor ((en, t), cn) ->
       Printf.sprintf
         "Factor %s [%s]"
         (term_as_string en t)
         (String.concat "; " (List.map as_string cn))
    | Unit ->
       "Unit"
  in Printf.printf "%s: %s\n\n" s (as_string fs)
                
(*
 * Dependent version of the above
 *)
let rec find_path_dep (assum : types) (env : env) evd (trm : types) : factor_tree =
  if is_assumption assum env trm then
    Factor ((env, trm), [])
  else
    match kind_of_term trm with
    | App (f, args) ->
       let trees = Array.map (find_path_dep assum env evd) args in
       let filter_nonunit = List.filter (fun t -> not (t = Unit)) in
       let nonempty_trees = filter_nonunit (Array.to_list trees) in
       let num_trees = List.length nonempty_trees in
       let assum_ind = destRel assum in
       let args = Array.to_list args in
       let env_old = env in
       if num_trees > 0 then
         let (env, children) =
           List.fold_left
             (fun ((en, cn) : env * factor_tree list) (tr : factor_tree) ->
               let (Factor ((env_arg, arg), children)) = tr in
               if List.length cn > 0 then
                 let (Factor ((en_prev, prev), _)) = List.hd cn in
                 let off = offset2 en en_prev in
                 let assum_ind_sub = assum_ind - off in
                 let assum_sub = mkRel assum_ind_sub in
                 let sub_assum = all_conv_substs en_prev (prev, assum_sub) in
                 let t = on_type sub_assum env_arg evd arg in
                 let t_shift = shift_by (1 - assum_ind_sub) t in 
                 let en_t = assume_no_replace assum en Anonymous t_shift in
                 (en_t, ((Factor ((env_arg, arg), children)) :: cn))
               else
                 let arg_typ = reduce_type env_arg evd arg in
                 let off = offset2 env_arg en in
                 let arg_typ_en = unshift_by off arg_typ in
                 let t = unshift_by assum_ind arg_typ_en in
                 let (n, _, _) = CRD.to_tuple @@ lookup_rel assum_ind en in
                 let en_t = assume assum en n t in
                 (en_t, [((Factor ((env_arg, arg), children)))]))
             (env, [])
             nonempty_trees
         in
         let off = nb_rel env - nb_rel env_old in
         let assumed = assume_args off trees assum_ind 0 num_trees args in
         Factor ((env, mkAppl (f, assumed)), List.rev children)
       else
	 Unit
    | _ -> (* other terms not yet implemented *)
       Unit
         
(*
 * Dependent version
 *)
let factor_term_dep (assum : types) (env : env) (evd : evar_map) (trm : types) : factor_tree =
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (reduce_term env trm) in
  let tree_body = find_path_dep assum env_zoomed evd trm_zoomed in
  let assum_ind = destRel assum in
  let rec factor_dep t =
    match t with
    | Factor ((env, body), children) ->
       let children = List.map factor_dep children in
       if is_assumption assum env body then
         Factor ((env, body), children)
       else
         let num_old_rels = nb_rel env_zoomed in
         let num_new_rels = offset env num_old_rels in
         let lambda = reconstruct_lambda_n env body (num_old_rels - assum_ind) in
         let env_lambda = pop_rel_context (num_new_rels + assum_ind) env in
         Factor ((env_lambda, lambda), children)
    | Unit ->
       Unit
  in factor_dep tree_body

(* --- Factoring lifted but not reduced functions --- *)

(*
 * Find the assumption for factoring in an ornamented, but not
 * yet reduced function. This is dependent on how the function is written
 * for now, and so might fail for some inductive definitions;
 * we should test this a lot and generalize it.
 *)
let get_assum orn env evd trm =
  let c = ref None in
  let _ =
    map_unit_if
      (fun t ->
        match kind_of_term t with
        | App (_, _) ->
           let f = first_fun t in
           isConst f && not (eq_constr f orn.promote || eq_constr f orn.forget)
        | _ ->
           false)
      (fun t ->
        let c' =
          if applies (Option.get orn.indexer) t then
            (* indexer *)
            let last_a = last_arg (last_arg t) in
            Some (map_if last_arg (applies projT2 last_a) last_a)
          else
            (* function *)
            let unorn = unwrap_definition env (first_fun t) in
            let (_, unorn_typ) = zoom_product_type env (infer_type env evd unorn) in
            let last_a = last_arg unorn_typ in
            let assum_a = map_if last_arg (applies projT2 last_a) last_a in
            let assum_i = arity unorn - destRel assum_a in
            Some (last_arg (get_arg assum_i t))
        in c := c'; t)
      trm
  in Option.get !c

(*
 * Factor an ornamented, but not yet reduced function
 *)
let factor_ornamented (orn : promotion) (env : env) evd (trm : types) =
  let assum = get_assum orn env evd trm in
  (destRel assum, factor_term_dep assum env evd trm)
