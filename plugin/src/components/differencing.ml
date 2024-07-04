(*
 * Differencing component
 *)

open Constr
open Environ
open Utilities
open Debruijn
open Context
open Util
open Convertibility
open Inference
open Apputils
open Envutils
open Stateutils

(* --- Differencing terms --- *)

(* Check if two terms have the same type *)
let same_type env sigma o n =
  let (env_o, t_o) = o in
  let (env_n, t_n) = n in
  let sigma, typ_o = infer_type env_o sigma t_o in
  let sigma, typ_n = infer_type env_o sigma t_n in
  convertible env sigma typ_o typ_n

(* --- Differencing inductive types --- *)

(* is_or_applies over two terms with a different check *)
let apply_old_new (o : types * types) (n : types * types) : bool =
  let (trm_o, trm_o') = o in
  let (trm_n, trm_n') = n in
  is_or_applies trm_o trm_o' && is_or_applies trm_n trm_n'

(* Check if two terms are the same modulo a change of an inductive type *)
let same_mod_change env sigma o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  if apply_old_new o n then
    sigma, true
  else
    convertible env sigma t_o t_n

(* Check if two terms are the same modulo an indexing of an inductive type *)
let same_mod_indexing env sigma p_index o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  if are_or_apply p_index t_o t_n then
    sigma,  true
  else
    same_mod_change env sigma o n

(* --- Finding the New Index --- *)

(* 
 * This determines IB and off
 *)

(*
 * Compute the difference between the applications of motives in the IHs
 * of eliminator types trm_o and trm_n, assuming there is some new index
 * in the type trm_n eliminates over that is not in trm_o.
 *
 * Return a list of offsets paired with pairs of old and new 
 * indices. 
 *)
let diff_motive_apps env trm_o trm_n =
  let rec diff off p trm_o trm_n =
    match map_tuple kind (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       if applies p t_o && not (applies p t_n) then
         diff (shift_i off) (shift env p) (shift env trm_o) b_n
       else
	 List.append (diff off p t_o t_n) (diff off (shift env p) b_o b_n)
    | (App (_, _), App (_, _)) when applies p trm_o && applies p trm_n ->
       let args_o = all_but_last (unfold_args trm_o) in
       let args_n = all_but_last (unfold_args trm_n) in
       [(off, (mkAppl (p, args_o), mkAppl (p, args_n)))]
    | _ ->
       []
  in List.rev (diff 0 (mkRel 1) trm_o trm_n)

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
 *
 * The implementation of this uses an offset list to adjust as it goes.
 *)
let is_new_index env i b_o b_n =
  let d = diff_motive_apps env b_o b_n in
  try
    let arg args = get_arg i args in
    let d_arg = List.map (fun (off, (o, n)) -> (off, (arg o, arg n))) d in
    let rec is_new d =
      match d with
      | (off, (o, n)) :: tl ->
	 if equal o n then
	   is_new tl
	 else
	   if off > 0 then
	     is_new (List.map (fun (off, (o, n)) -> (off - 1, (o, shift env n))) d)
	   else
	     true
      | [] ->
	 false
    in is_new d_arg
  with Invalid_argument s ->
    true (* we're on the last index *)

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
let new_index_type env sigma elim_t_o elim_t_n =
  let (_, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, b_n) = destProd elim_t_n in
  let rec candidates e sigma p_o p_n =
    match map_tuple kind (p_o, p_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if isProd b_o then
         branch_state
           (fun (t_o, t_n) sigma -> convertible e sigma t_o t_n)
           (fun (t_o, t_n) sigma ->
             let e_b = push_local (n_o.binder_name, t_o) e in
             let sigma, same = candidates e_b sigma b_o b_n in
             let diff = (0, t_n) in
             sigma, diff :: (List.map (fun (i, i_t) -> (shift_i i, i_t)) same))
           (fun (t_o, t_n) sigma -> sigma, [(0, t_n)])
           (t_o, t_n)
           sigma
       else
         sigma, [(0, t_n)]
    | _ ->
       failwith "could not find indexer motive"
  in
  Util.on_snd
    (List.find (fun (i, _) -> is_new_index env i b_o b_n))
    (candidates env sigma p_o p_n)
               
(*
 * This is Nate's simple search heuristic that works when there is no ambiguity
 *)
let diff_context_simple env sigma decls_o decls_n =
  let nth_type n = Rel.Declaration.get_type (List.nth decls_n n) in
  let rec scan env pos diff (decls_o, decls_n) sigma : (int option) state =
    match (decls_o, decls_n) with
    | (decl_o :: decls_o_b), (decl_n :: decls_n_b) ->
      let type_o = Rel.Declaration.get_type decl_o in
      let type_n = Rel.Declaration.get_type decl_n in
      let env_b = push_rel decl_n env in
      let pos_b = pos + 1 in
      branch_state
        (fun (type_o, type_n) sigma -> convertible env sigma type_o type_n)
        (fun (type_o, type_n) sigma ->
          let sigma_b, diff_b = scan env_b pos_b diff (decls_o_b, decls_n_b) sigma in
          if Option.has_some diff_b && Option.get diff_b = pos_b then
            let type_i = nth_type pos_b in
            branch_state
              (not_state
                 (fun (type_o, type_i) sigma_b ->
                   convertible env_b sigma_b (shift env type_o) type_i))
              (fun _  -> ret diff_b)
              (fun _ -> ret None) (* ambiguous, can't use this heuristic *)
              (type_o, type_i)
              sigma_b
          else
            sigma, diff_b)
        (fun _ -> scan env_b pos_b (Some pos) (decls_o, decls_n_b))
        (type_o, type_n)
        sigma
    | [], (decl_n :: decls_n_b) ->
       if List.length decls_n_b > 0 then
         failwith "Please add just one new index at a time."
       else
         sigma, Some pos (* the last index is new *)
    | _ ->
       failwith "No new indices. Try switching directions."
  in
  let sigma, diff_pos = scan env 0 None (decls_o, decls_n) sigma in
  if Option.has_some diff_pos then
    let pos = Option.get diff_pos in
    let typ = nth_type pos in
    Some (sigma, (pos, typ))
  else
    None
               
(*
 * Top-level index finder for Nate's heuristic
 *)
let new_index_type_simple env sigma ind_o ind_n =
  (* Applying each parameter increments the index for the next one. *)
  let npars = nb_rel env in
  let pars = List.make npars (mkRel npars) in
  let pind_o = Univ.in_punivs ind_o in
  let pind_n = Univ.in_punivs ind_n in
  let indf_o = Inductiveops.make_ind_family (pind_o, pars) in
  let indf_n = Inductiveops.make_ind_family (pind_n, pars) in
  let (idcs_o, _) = Inductiveops.get_arity env indf_o in
  let (idcs_n, _) = Inductiveops.get_arity env indf_n in
  diff_context_simple env sigma (List.rev idcs_o) (List.rev idcs_n)



