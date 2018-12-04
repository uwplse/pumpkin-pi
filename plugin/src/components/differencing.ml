(*
 * Differencing component
 *)

open Constr
open Environ
open Coqterms
open Utilities
open Debruijn
open Context
open Util

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
    not (equal (get_arg i trm_o) (get_arg i trm_n))
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

(* --- Finding the New Index --- *)

(* 
 * As described in "Finding the New Index" in Section 5.1.1,
 * search starts by identifying the new index and offset.
 * There are two algorithms for this (both described in that section):
 * the simple one cannot deal with ambiguity, but simply compares the types.
 * A more complex algorithm runs when there is ambiguity, and compares the
 * eliminators instead.
 *)

(*
 * Returns true if the argument at the supplied index location of the 
 * inductive motive (which should be at relative index 1 before calling
 * this function) is an index to some application of the induction principle
 * in the second term that was not an index to any application of the induction
 * principle in the first term.
 *
 * In other words, this looks for applications of the motive
 * in the induction principle type, checks the argument at the location,
 * and determines whether they were equal. If they are ever not equal,
 * then the index is considered to be new. Since we are ornamenting,
 * we can assume that we maintain the same inductive structure, and so
 * we should encounter applications of the induction principle in both
 * terms in exactly the same order.
 *)
let is_new_index i trm_o trm_n =
  let rec is_new p trm_o trm_n =
    match map_tuple kind (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       if applies p t_o && not (applies p t_n) then
         is_new (shift p) (shift trm_o) b_n
       else
         is_new p t_o t_n || is_new (shift p) b_o b_n
    | (App (_, _), App (_, _)) when applies p trm_o && applies p trm_n ->
       let args_o = all_but_last (unfold_args trm_o) in
       let args_n = all_but_last (unfold_args trm_n) in
       diff_arg i (mkAppl (p, args_o)) (mkAppl (p, args_n))
    | _ ->
       false
  in is_new (mkRel 1) trm_o trm_n

(*
 * Assuming there is an indexing ornamental relationship between two 
 * eliminators, get the type and location of the new index.
 * This starts by identifying candidate new indices, then filters
 * them to the ones that are truly different.
 *
 * If indices depend on earlier types, the types may be dependent;
 * the client needs to shift by the appropriate offset.
 *
 * This algorithm only runs when there is ambiguity, since Nate's
 * algorithm can take care of simpler cases where the types enough
 * are revealing. There are some examples of ambiguity in Test.v;
 * these should never break, and if they do, it means the code is incorrect.
 *)
let new_index_type env elim_t_o elim_t_n =
  let (_, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, b_n) = destProd elim_t_n in
  let rec candidates e p_o p_n =
    match map_tuple kind (p_o, p_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if isProd b_o && convertible e t_o t_n then
         let e_b = push_local (n_o, t_o) e in
         let same = candidates e_b b_o b_n in
         let different = (0, t_n) in
         different :: (List.map (fun (i, i_t) -> (shift_i i, i_t)) same)
       else
         [(0, t_n)]
    | _ ->
       failwith "could not find indexer motive"
  in List.find (fun (i, _) -> is_new_index i b_o b_n) (candidates env p_o p_n)
               
(*
 * This is Nate's simple search heuristic that works when there is no ambiguity
 *)
let diff_context_simple env decls_o decls_n =
  let nth_type n = Rel.Declaration.get_type (List.nth decls_n n) in
  let rec scan env pos diff (decls_o, decls_n) : int option =
    match (decls_o, decls_n) with
    | (decl_o :: decls_o_b), (decl_n :: decls_n_b) ->
      let type_o = Rel.Declaration.get_type decl_o in
      let type_n = Rel.Declaration.get_type decl_n in
      let env_b = push_rel decl_n env in
      let pos_b = pos + 1 in
      if convertible env type_o type_n then
        let diff_b = scan env_b pos_b diff (decls_o_b, decls_n_b) in
        if Option.has_some diff_b && Option.get diff_b = pos_b then
          let type_i = nth_type pos_b in
          if not (convertible env_b (shift type_o) type_i) then
            diff_b
          else
            None (* ambiguous, can't use this heuristic *)
        else
          diff_b
      else
        scan env_b pos_b (Some pos) (decls_o, decls_n_b) (* this index is new *)
    | [], (decl_n :: decls_n_b) ->
       if List.length decls_n_b > 0 then
         failwith "Please add just one new index at a time."
       else
         Some pos (* the last index is new *)
    | _ ->
       failwith "No new indices. Try switching directions."
  in
  let diff_pos = scan env 0 None (decls_o, decls_n) in
  if Option.has_some diff_pos then
    let pos = Option.get diff_pos in
    let typ = nth_type pos in
    Some (pos, typ)
  else
    None
               
(*
 * Top-level index finder for Nate's heuristic
 *)
let new_index_type_simple env npars ind_o ind_n =
  (* Applying each parameter increments the index for the next one. *)
  let pars = List.make npars (mkRel npars) in
  let pind_o = Univ.in_punivs ind_o in
  let pind_n = Univ.in_punivs ind_n in
  let indf_o = Inductiveops.make_ind_family (pind_o, pars) in
  let indf_n = Inductiveops.make_ind_family (pind_n, pars) in
  let (idcs_o, _) = Inductiveops.get_arity env indf_o in
  let (idcs_n, _) = Inductiveops.get_arity env indf_n in
  diff_context_simple env (List.rev idcs_o) (List.rev idcs_n)



