(*
 * Differencing for ornamenting inductive types
 *)

open Term
open Environ
open Coqterms
open Utilities
open Debruijn

(* --- Differencing terms --- *)

(* Check if two terms have the same type, ignoring universe inconsinstency *)
let same_type env evd o n =
  let (env_o, t_o) = o in
  let (env_n, t_n) = n in
  try
    convertible env (infer_type env_o evd t_o) (infer_type env_n evd t_n)
  with _ ->
    false

(*
 * Returns true if two applications contain have a different
 * argument at index i.
 *
 * For now, this uses precise equality, but we can loosen this
 * to convertibility if desirable.
 *)
let diff_arg i trm_o trm_n =
  try
    let arg_o = get_arg i trm_o in
    let arg_n = get_arg i trm_n in
    not (eq_constr arg_o arg_n)
  with _ ->
    true

(* --- Differencing inductive types --- *)

(* is_or_applies over two terms with a different check *)
let apply_old_new (o : types * types) (n : types * types) : bool =
  let (trm_o, trm_o') = o in
  let (trm_n, trm_n') = n in
  is_or_applies trm_o trm_o' && is_or_applies trm_n trm_n'

(* Check if two terms are the same modulo a change of an inductive type *)
let same_mod_change env o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  apply_old_new o n || convertible env t_o t_n

(* Check if two terms are the same modulo an indexing of an inductive type *)
let same_mod_indexing env p_index o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  are_or_apply p_index t_o t_n || same_mod_change env o n

(*
 * Returns true if the argument at the supplied index location of the 
 * inductive property (which should be at relative index 1 before calling
 * this function) is an index to some application of the induction principle
 * in the second term that was not an index to any application of the induction
 * principle in the first term.
 *
 * In other words, this looks for applications of the property
 * in the induction principle type, checks the argument at the location,
 * and determines whether they were equal. If they are ever not equal,
 * then the index is considered to be new. Since we are ornamenting,
 * we can assume that we maintain the same inductive structure, and so
 * we should encounter applications of the induction principle in both
 * terms in exactly the same order.
 *)
let new_index i trm_o trm_n =
  let rec is_new_index p trm_o trm_n =
    match map_tuple kind_of_term (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       if applies p t_o && not (applies p t_n) then
         is_new_index p_b (shift trm_o) b_n
       else
         is_new_index p t_o t_n || is_new_index p_b b_o b_n
    | (App (_, _), App (_, _)) when applies p trm_o && applies p trm_n ->
       let args_o = List.rev (List.tl (List.rev (unfold_args trm_o))) in
       let args_n = List.rev (List.tl (List.rev (unfold_args trm_n))) in
       diff_arg i (mkAppl (p, args_o)) (mkAppl (p, args_n))
    | _ ->
       false
  in is_new_index (mkRel 1) trm_o trm_n

(*
 * Assuming there is an indexing ornamental relationship between two 
 * eliminators, get the type and location of the new index.
 *
 * If indices depend on earlier types, the types may be dependent;
 * the client needs to shift by the appropriate offset.
 *)
let new_index_type env elim_t_o elim_t_n =
  let (_, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, b_n) = destProd elim_t_n in
  let rec poss_indices e p_o p_n =
    match map_tuple kind_of_term (p_o, p_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if isProd b_o && convertible e t_o t_n then
         let e_b = push_local (n_o, t_o) e in
         let same = poss_indices e_b b_o b_n in
         let different = (0, t_n) in
         different :: (List.map (fun (i, i_t) -> (shift_i i, i_t)) same)
       else
         [(0, t_n)]
    | _ ->
       failwith "could not find indexer property"
  in List.find (fun (i, _) -> new_index i b_o b_n) (poss_indices env p_o p_n)
