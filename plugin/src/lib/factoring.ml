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
           let t = unshift_by (destRel assum) (reduce_type env_arg evd arg) in
	   (assume assum env Anonymous t, mkApp (f, args_assumed)) :: path
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
let rec assume_args off trees assum_ind tree_i factors_left args =
  match args with
  | h :: tl ->
     let (h', factors_left') =
       (match (Array.get trees tree_i) with
        | Factor (_, _) ->
           (mkRel (factors_left + assum_ind - 1), factors_left - 1)
        | Unit ->
           (shift_local assum_ind off h, factors_left))
     in h' :: (assume_args off trees assum_ind (tree_i + 1) factors_left' tl)
  | [] ->
     []

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
                 let off = nb_rel en - nb_rel en_prev in
                 let t = reduce_type env_arg evd arg in
                 let t = all_conv_substs en_prev (prev, mkRel (assum_ind - off)) t in
                 let en_t = assume_no_replace assum en Anonymous (shift_by (off - assum_ind + 1) t) in
                 (en_t, ((Factor ((env_arg, arg), children)) :: cn))
               else
                 let t = unshift_by assum_ind (reduce_type env_arg evd arg) in
                 let en_t = assume assum en Anonymous t in

                 (en_t, [((Factor ((env_arg, arg), children)))]))
             (env, [])
             nonempty_trees
         in
         let off = nb_rel env - nb_rel env_old in
         let assumed = Array.of_list (assume_args off trees assum_ind 0 num_trees args) in
         Factor ((env, mkApp (f, assumed)), List.rev children)
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
         let num_new_rels = nb_rel env - num_old_rels in
         let lambda = reconstruct_lambda_n env body (num_old_rels - assum_ind) in
         let env_lambda = pop_rel_context (num_new_rels + assum_ind) env in
         Factor ((env_lambda, lambda), children)
    | Unit ->
       Unit
  in factor_dep tree_body

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
