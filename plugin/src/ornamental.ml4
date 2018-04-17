DECLARE PLUGIN "ornamental"

open Term
open Names
open Environ
open Constrarg
open Format
open Univ
open Printer
open Declarations
open Utilities
open Coqterms
open Hofs
open Debruijn
open Zooming
open Printing
open Factoring
open Differencing (* TODO clean above once refactored *)

module CRD = Context.Rel.Declaration

(* --- Ornaments and promotions --- *)

(*
 * For now, an ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, a function from T2 -> T1. Later, it will also contain
 * patches and extra premises, and these will be present both in the top-level
 * type and as premises to the functions in both directions.
 *
 * We don't represent ornaments directly, yet, but this may also be useful.
 *)
type promotion =
  {
    index_i : int option;
    indexer : types option;
    promote : types;
    forget : types;
  }

(*
 * A lifting is an ornamental promotion between types, a direction,
 * a hint whether it corresponds to an indexing function for an outer lifting,
 * and an optional indexer for the promoted function.
 *
 * I may add more things here later. This is just a convenient configuration
 * for promoting functions.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
    is_indexer : bool;
    lifted_indexer : types option;
  }

(*
 * Initialize a lifting
 *)
let initialize_lifting orn is_fwd =
  let lifted_indexer = None in
  let is_indexer = false in
  { orn ; is_fwd ; lifted_indexer ; is_indexer }
    
(*
 * These two functions determine what function to use to go back to
 * an old type or get to a new type when lifting
 *)
let lift_back (l : lifting) = if l.is_fwd then l.orn.forget else l.orn.promote
let lift_to (l : lifting) = if l.is_fwd then l.orn.promote else l.orn.forget

(* Control structures *)
let map_if_else f g b x = if b then f x else g x
let map_if f b x = map_if_else f (fun a -> a) b x
let directional l a b = if l.is_fwd then a else b
let if_indexer l a b = if l.is_indexer then a else b
let map_directional f g l x = map_if_else f g l.is_fwd x
let map_indexer f g l x = map_if_else f g l.is_indexer x
let map_forward f l x = map_if f l.is_fwd x
let map_if_indexer f l x = map_if f l.is_indexer x

(*
 * A composition is a pair of functions and environments with
 * a corresponding lifting. It also contains a hint is_g, which says
 * whether lifting is applied to g or to f. This represents a single (factored)
 * applied but not simplified ornamentation.
 *)
type composition =
  {
    l : lifting;
    g : env * types;
    f : env * types;
    is_g : bool;
  }

(* --- Utilities that might not generalize outside of this tool --- *)

(*
 * Remove the binding at index i from the environment
 * TODO move this wherever you move pack/unpack
 *)
let remove_rel (i : int) (env : env) : env =
  let (env_pop, popped) = lookup_pop i env in
  let push =
    List.mapi
      (fun j rel ->
        let (n, _, t) = CRD.to_tuple rel in
        (n, unshift_local (i - j - 1) 1 t))
      (List.rev (List.tl (List.rev popped)))
  in List.fold_right push_local push env_pop

(* Apply an eliminator *)
let apply_eliminator elim pms p cs final_args =
  let args = Array.of_list (List.append pms (p :: cs)) in
  mkApp (mkApp (elim, args), final_args)

(* Apply an eliminator and reconstruct it from an environment *)
let apply_eliminator_recons env elim pms p cs final_args =
  reconstruct_lambda env (apply_eliminator elim pms p cs final_args)

(* Get the first function of an application *)
let rec first_fun t =
  match kind_of_term t with
  | App (f, args) ->
     first_fun f
  | _ ->
     t

(* Get the inductive types an ornament maps between, including their arguments *)
let rec ind_of_orn (orn_type : types) : types * types =
  match kind_of_term orn_type with
  | Prod (n, t, b) when isProd b ->
     ind_of_orn b
  | Prod (n, t, b) ->
     (t, b)
  | _ ->
     failwith "not an ornament"
              
(*
 * Get the argument to an application of a property at argument position i.
 * This unfolds all arguments first.
 *)
let get_arg i trm =
  match kind_of_term trm with
  | App (_, _) ->
     let args = Array.of_list (unfold_args trm) in
     Array.get args i
  | _ ->
     failwith "not an application"

(*
 * Deconstruct an eliminator application.
 *
 * Assumes the inductive type is not mutually inductive.
 *)
let deconstruct_eliminator env evd app =
  let ip = first_fun app in
  let ip_args = unfold_args app in
  let ip_typ = reduce_type env evd ip in
  let from_typ =  first_fun (fst (ind_of_orn ip_typ)) in
  let ((from_i, _), _) = destInd from_typ in
  let from_m = lookup_mind from_i env in
  let npms = from_m.mind_nparams in
  let from_arity = arity (type_of_inductive env 0 from_m) in
  let num_indices = from_arity - npms in
  let num_props = 1 in
  let num_constrs = arity ip_typ - npms - num_props - num_indices - 1 in
  let (pms, pmd_args) = take_split npms ip_args in
  let (p :: cs_and_args) = pmd_args in
  let (cs, args) = take_split num_constrs cs_and_args in
  (ip, pms, p, cs, Array.of_list args)

(* Find the offset of some environment from some number of parameters *)
let offset env npm = nb_rel env - npm

(*
 * Modify a case of an eliminator application to use
 * the new property p in its hypotheses
 *)
let with_new_p p c : types =
  let rec sub_p sub trm =
    let (p_o, p_n) = sub in
    match kind_of_term trm with
    | Prod (n, t, b) ->
       let sub_b = map_tuple shift sub in
       if applies p_o t then
         let (_, args) = destApp t in
         mkProd (n, mkApp (p_n, args), sub_p sub_b b)
       else
         mkProd (n, t, sub_p sub_b b)
    | _ ->
       trm
  in sub_p (mkRel 1, p) c

(*
 * Check recursively whether a term contains another term
 *)
let contains_term c trm =
  exists_subterm eq_constr shift c trm

(*
 * This function removes any terms from the hypothesis of a lambda
 * that are not referenced in the body, so that the term
 * has only hypotheses that are referenced.
 *
 * It's different from the version in PUMPKIN PATCH because it ignores
 * possible universe inconsistency.
 *)
let rec remove_unused_hypos (trm : types) : types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let b' = remove_unused_hypos b in
     if contains_term (mkRel 1) b' then
       mkLambda (n, t, b')
     else
       remove_unused_hypos (unshift b')
  | _ ->
     trm

(*
 * Get only the hypos that are used in the body,
 * but in the order they appear in the lambda
 *)
let get_used_hypos (trm : types) : types list =
  let rec get_used trm i =
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       let b' = remove_unused_hypos b in
       let bs = get_used b (unshift_i i) in
       if contains_term (mkRel 1) b' then
         mkRel i :: bs
       else
         bs
    | _ ->
       []
  in get_used trm (arity trm)

(*
 * Get the hypos that are used in the body, or that match
 * a certain predicate on the type
 *)
let get_used_or_p_hypos (p : types -> bool) (trm : types) : types list =
  let rec get_used trm i =
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       let bs = get_used b (unshift_i i) in
       if p t then
         mkRel i :: bs
       else
         let b' = remove_unused_hypos b in
         if contains_term (mkRel 1) b' then
           mkRel i :: bs
         else
           bs
    | _ ->
       []
  in get_used trm (arity trm)

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

(* Remove the final hypothesis of a lambda *)
let rec remove_final_hypo trm =
  match kind_of_term trm with
  | Lambda (n, t, b) when isLambda b ->
     mkLambda (n, t, remove_final_hypo b)
  | Lambda (n, t, b) ->
     unshift b
  | _ ->
     failwith "not a lambda"

(* --- Differencing and identifying indices --- *)

(*
 * Insert an index into a list of terms in the location index_i
 *)
let insert_index index_i index args =
  let (before, after) = take_split index_i args in
  List.append before (index :: after)

(*
 * Insert an index and shift the arguments before and after it by n
 *)
let insert_index_shift index_i index args n =
  let (before, after) = take_split index_i (shift_all_by n args) in
  List.append before (index :: after)

(*
 * Remove an index from a list of terms in the location index_i
 *)
let remove_index index_i args =
  let (before, after) = take_split index_i args in
  List.append before (List.tl after)

(*
 * Insert an index where an old index was
 *)
let reindex index_i index args =
  insert_index index_i index (remove_index index_i args)

(*
 * Insert an index where an old index was and shift after
 *)
let reindex_shift index_i index args n =
  insert_index_shift index_i index (remove_index index_i args) n

(*
 * Unshift arguments after index_i, since the index is no longer in
 * the hypotheses
 *)
let adjust_no_index index_i args =
  let (before, after) = take_split index_i args in
  List.append before (unshift_all after)
              
(* Given a type and the location of the argument, abstract by the argument *)
let abstract_arg env evd i typ =
  let arg = get_arg i typ in
  let arg_typ = reduce_type env evd arg in
  let args = reindex i (mkRel 1) (shift_all (unfold_args typ)) in
  mkLambda (Anonymous, arg_typ, mkAppl (first_fun typ, args))

(*
 * Returns true if the argument at index i to property p is
 * an index in trm_n that was not an index in trm_o.
 *
 * In other words, this looks for applications of the property p
 * in the induction principle type, checks the argument at index i,
 * and determines whether they were equal. If they are ever not equal,
 * then the index is considered to be new.
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
 * Returns the first inductive hypothesis in the eliminator type trm
 * for which the hypothesis h is used to compute the index at position index_i
 *)
let rec index_ih index_i p h trm i =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     let p_b = shift p in
     let i_b = shift h in
     if applies p t then
       if contains_term h (get_arg index_i t) then
         Some (mkRel i, t)
       else
         index_ih index_i p_b i_b b (i - 1)
     else
       index_ih index_i p_b i_b b (i - 1)
  | App (_, _) when applies p trm ->
     if contains_term h (get_arg index_i trm) then
       Some (mkRel i, trm)
     else
       None
  | _ ->
     None
                  
(*
 * Returns true if the hypothesis i is used to compute the index at position
 * index_i in any application of a property p in the eliminator type trm.
 *)
let rec computes_index index_i p i trm =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     let p_b = shift p in
     let i_b = shift i in
     if applies p t then
       contains_term i (get_arg index_i t) || computes_index index_i p_b i_b b
     else
       computes_index index_i p_b i_b b
  | App (_, _) when applies p trm ->
     contains_term i (get_arg index_i trm)
  | _ ->
     false

(*
 * Returns true if the hypothesis i is _only_ used to compute the index
 * at index_i, and is not used to compute any other indices
 *)
let computes_only_index env evd index_i p i trm =
  let indices = List.map unshift_i (from_one_to (arity (infer_type env evd p) - 1)) in
  if computes_index index_i p i trm then
    let indices_not_i = remove_index index_i indices in
    List.for_all (fun j -> not (computes_index j p i trm)) indices_not_i
  else
    false

(*
 * Get the index type and location (index of the index).
 * This doesn't yet handle adding multiple indices.
 *
 * If indices depend on earlier types, the types may be dependent;
 * the client needs to shift by the appropriate offset.
 *)
let index_type env elim_t_o elim_t_n =
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

(*
 * Given an old and new application of a property, find the new index.
 * This also assumes there is only one new index.
 *)
let get_new_index index_i p o n =
  match map_tuple kind_of_term (o, n) with
  | (App (f_o, _), App (f_n, _)) when are_or_apply p f_o f_n ->
     get_arg index_i n
  | _ ->
     failwith "not an application of a property"

(* --- Search --- *)

(* Search two inductive types for a parameterizing ornament *)
let search_orn_params env (ind_o : inductive) (ind_n : inductive) is_fwd : types =
  failwith "parameterization is not yet supported"

(*
 * Get a single case for the indexer, given:
 * 1. index_i, the location of the new index in the property
 * 2. index_t, the type of the new index in the property
 * 3. o, the old environment, inductive type, and constructor
 * 4. n, the new environment, inductive type, and constructor
 *
 * Eventually, it would be good to make this logic less ad-hoc,
 * though the terms we are looking at here are type signatures of
 * induction principles, and so should be very predictable.
 *)
let index_case evd index_i p o n : types =
  let get_index = get_new_index index_i in
  let rec diff_case p_i p subs o n =
    let (e_o, ind_o, trm_o) = o in
    let (e_n, ind_n, trm_n) = n in
    match map_tuple kind_of_term (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       (* premises *)
       let p_b = shift p in
       let diff_b = diff_case (shift p_i) p_b in
       let e_n_b = push_local (n_n, t_n) e_n in
       let n_b = (e_n_b, shift ind_n, b_n) in
       let same = same_mod_indexing e_o p in
       let same_arity = arity b_o = arity b_n in
       let false_lead b_n = not same_arity && (computes_only_index e_n_b evd index_i p_b (mkRel 1)) b_n in
       if (not (same (ind_o, t_o) (ind_n, t_n))) || false_lead b_n then
         (* index *)
         let e_o_b = push_local (n_n, t_n) e_o in
         let subs_b = shift_subs subs in
         let o_b = (e_o_b, shift ind_o, shift trm_o) in
         unshift (diff_b subs_b o_b n_b)
       else
         let e_o_b = push_local (n_o, t_o) e_o in
         let o_b = (e_o_b, shift ind_o, b_o) in
         if apply p t_o t_n then
           (* inductive hypothesis *)
           let sub_index = (shift (get_index p t_o t_n), mkRel 1) in
           let subs_b = sub_index :: shift_subs subs in
           mkLambda (n_o, mkAppl (p_i, unfold_args t_o), diff_b subs_b o_b n_b)
         else
           (* no change *)
           let subs_b = shift_subs subs in
           mkLambda (n_o, t_o, diff_b subs_b o_b n_b)
    | (App (f_o, _), App (f_n, _)) ->
       (* conclusion *)
       let index = get_index p trm_o trm_n in
       List.fold_right all_eq_substs subs index
    | _ ->
       failwith "unexpected case"
  in diff_case p (mkRel 1) [] o n

(* Get the cases for the indexer *)
let indexer_cases evd index_i p npm o n : types list =
  let (env_o, ind_o, arity_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elim_t_n) = n in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
  | (Prod (n_o, p_o, b_o), Prod (n_n, p_n, b_n)) ->
     let env_p_o = push_local (n_o, p_o) env_o in
     let env_p_n = push_local (n_n, p_n) env_n in
     let o c = (env_p_o, ind_o, c) in
     let n c = (env_p_n, ind_n, c) in
     List.map2
       (fun c_o c_n ->
         shift_by
           (arity_o - npm)
           (index_case evd index_i p (o c_o) (n c_n)))
       (take_except (arity_o - npm + 1) (factor_product b_o))
       (take_except (arity_n - npm + 1) (factor_product b_n))
  | _ ->
     failwith "not eliminators"

(* Search for an indexing function *)
let search_for_indexer evd index_i index_t npm elim_o o n is_fwd : types option =
  if is_fwd then
    let (env_o, _, arity_o, elim_t_o) = o in
    let (env_n, _, _, elim_t_n) = n in
    let index_t = shift_by npm index_t in
    match map_tuple kind_of_term (elim_t_o, elim_t_n) with
    | (Prod (_, p_o, b_o), Prod (_, p_n, b_n)) ->
       let env_ind = zoom_env zoom_product_type env_o p_o in
       let off = offset env_ind npm in
       let pms = shift_all_by (arity_o - npm + 1) (mk_n_rels npm) in
       let index_t_p = shift_by index_i index_t in
       let p = reconstruct_lambda_n env_ind index_t_p npm in
       let cs = indexer_cases evd index_i (shift p) npm o n in
       let final_args = Array.of_list (mk_n_rels off) in
       let p_elim = shift_by off p in
       Some (apply_eliminator_recons env_ind elim_o pms p_elim cs final_args)
    | _ ->
       failwith "not eliminators"
  else
    None

(* Find the property that the ornament proves *)
let ornament_p index_i env ind arity npm indexer_opt =
  let off = offset env npm in
  let off_args = off - (arity - npm) in
  let args = shift_all_by off_args (mk_n_rels arity) in
  let index_i_npm = npm + index_i in
  let concl =
    match indexer_opt with
    | Some indexer ->
       (* forward (indexing) direction *)
       let indexer = Option.get indexer_opt in
       let index = mkAppl (indexer, snoc (mkRel 1) args) in
       mkAppl (ind, insert_index index_i_npm index args)
    | None ->
       (* backward (deindexing) direction *)
       mkAppl (ind, adjust_no_index index_i_npm args)
  in shift_by off (reconstruct_lambda_n env concl npm)

(*
 * Stretch the old property type to match the new one
 * That is, add indices where they are missing in the old property
 * For now just supports one index
 *)
let rec stretch_property_type index_i env o n =
  let (ind_o, p_o) = o in
  let (ind_n, p_n) = n in
  match map_tuple kind_of_term (p_o, p_n) with
  | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
     let n_b = (shift ind_n, b_n) in
     if index_i = 0 then
       mkProd (n_n, t_n, shift p_o)
     else
       let env_b = push_local (n_o, t_o) env in
       let o_b = (shift ind_o, b_o) in
       mkProd (n_o, t_o, stretch_property_type (index_i - 1) env_b o_b n_b)
  | _ ->
     p_o

(*
 * Stretch the old property to match the new one at the term level
 *
 * Hilariously, this function is defined as an ornamented
 * version of stretch_property_type.
 *)
let stretch_property index_i env o n =
  let (ind_o, p_o) = o in
  let o = (ind_o, lambda_to_prod p_o) in
  prod_to_lambda (stretch_property_type index_i env o n)

(*
 * Stretch out the old eliminator type to match the new one
 * That is, add indexes to the old one to match new
 *)
let stretch index_i env indexer pms o n =
  let (ind_o, elim_t_o) = o in
  let (ind_n, elim_t_n) = n in
  let (n_exp, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, _) = destProd elim_t_n in
  let p_exp = stretch_property_type index_i env (ind_o, p_o) (ind_n, p_n) in
  let b_exp =
    map_term_if
      (fun (p, _) t -> applies p t)
      (fun (p, pms) t ->
        let non_pms = unfold_args t in
        let index = mkApp (indexer, Array.append pms (Array.of_list non_pms)) in
        mkAppl (p, insert_index index_i index non_pms))
      (fun (p, pms) -> (shift p, Array.map shift pms))
      (mkRel 1, pms)
      b_o
  in mkProd (n_exp, p_exp, b_exp)

(*
 * Given terms that apply properties, update the
 * substitution list to include the corresponding new index
 *
 * This may be wrong for dependent indices (may need some kind of fold,
 * or the order may be incorrect). We'll need to see when we test that case.
 *)
let sub_index evd f_indexer subs o n =
  let (env_o, app_o) = o in
  let (env_n, app_n) = n in
  let (args_o, args_n) = map_tuple unfold_args (app_o, app_n) in
  let args = List.combine args_o args_n in
  let new_subs =
    List.map
      (fun (a_o, a_n) ->
        if applies f_indexer a_o then
          (* substitute the inductive hypothesis *)
          (shift a_n, shift a_o)
        else
          (* substitute the index *)
          (shift a_n, mkRel 1))
      (List.filter
         (fun (a_o, a_n) ->
           applies f_indexer a_o || not (same_type env_o evd (env_o, a_o) (env_n, a_n)))
         args)
  in List.append new_subs subs

(* In the conclusion of each case, return c_n with c_o's indices *)
(* TODO clean again, see if any of these checks are redundant *)
let sub_indexes evd index_i is_fwd f_indexer p subs o n : types =
  let directional a b = if is_fwd then a else b in
  let rec sub p subs o n =
    let (env_o, ind_o, c_o) = o in
    let (env_n, ind_n, c_n) = n in
    match map_tuple kind_of_term (c_o, c_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       let same = same_mod_indexing env_o p (ind_o, t_o) (ind_n, t_n) in
       let env_o_b = push_local (n_o, t_o) env_o in
       let env_n_b = push_local (n_n, t_n) env_n in
       let false_lead_fwd _ b_n = computes_only_index env_n_b evd index_i p_b (mkRel 1) b_n in
       let false_lead_bwd b_o _ = computes_only_index env_o_b evd index_i p_b (mkRel 1) b_o in
       let same_arity b_o b_n = (arity b_o = arity b_n) in
       let false_lead b_o b_n = (not (same_arity b_o b_n)) && (directional false_lead_fwd false_lead_bwd) b_o b_n in
       if applies p t_n || (same && not (false_lead b_o b_n)) then
         let o_b = (env_o_b, shift ind_o, b_o) in
         let n_b = (env_n_b, shift ind_n, b_n) in
         let subs_b = shift_subs subs in
         if applies p t_n then
           (* inductive hypothesis, get the index *)
           let subs_b = sub_index evd f_indexer subs_b (env_o, t_o) (env_n, t_n) in
           mkProd (n_o, t_o, sub p_b subs_b o_b n_b)
         else
           (* no index, keep recursing *)
           mkProd (n_o, t_o, sub p_b subs_b o_b n_b)
       else
         (* new hypothesis from which the index is computed *)
         let subs_b = directional (shift_to subs) (shift_from subs) in
         let new_index = directional (n_n, t_n) (n_o, t_o) in
         let (b_o_b, b_n_b) = directional (shift c_o, b_n) (b_o, shift c_n) in
         let env_o_b = push_local new_index env_o in
         let env_n_b = push_local new_index env_n in
         let o_b = (env_o_b, shift ind_o, b_o_b) in
         let n_b = (env_n_b, shift ind_n, b_n_b) in
         let subbed_b = sub p_b subs_b o_b n_b in
         directional (unshift subbed_b) (mkProd (n_o, t_o, subbed_b))
    | (App (f_o, args_o), App (f_n, args_n)) ->
       let args_n = List.rev (unfold_args c_n) in
       List.fold_right all_eq_substs subs (List.hd args_n)
    | _ ->
       failwith "unexpected case substituting index"
  in sub p subs o n

(*
 * Get a case for an indexing ornament.
 *
 * This currently works in the following way:
 * 1. If it's forwards, then adjust the property to have the index
 * 2. Substitute in the property to the old case
 * 3. Substitute in the indexes (or lack thereof, if backwards)
 *
 * Eventually, we might want to think of this as (or rewrite this to)
 * abstracting the indexed type to take an indexing function, then
 * deriving the result through specialization.
 *)
let orn_index_case evd index_i is_fwd indexer_f orn_p o n : types =
  let when_forward f a = if is_fwd then f a else a in
  let (env_o, arity_o, ind_o, _, c_o) = o in
  let (env_n, arity_n, ind_n, p_n, c_n) = n in
  let d_arity = arity_n - arity_o in
  let adjust p = stretch_property index_i env_o (ind_o, p) (ind_n, p_n) in
  let p_o = when_forward (fun p -> adjust (unshift_by d_arity p)) orn_p in
  let c_o = with_new_p (shift_by d_arity p_o) c_o in
  let o = (env_o, ind_o, c_o) in
  let n = (env_n, ind_n, c_n) in
  prod_to_lambda (sub_indexes evd index_i is_fwd indexer_f (mkRel 1) [] o n)

(* Get the cases for the ornament *)
let orn_index_cases evd index_i npm is_fwd indexer_f orn_p o n : types list =
  let (env_o, pind_o, arity_o, elim_t_o) = o in
  let (env_n, pind_n, arity_n, elim_t_n) = n in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
  | (Prod (_, p_o, b_o), Prod (_, p_n, b_n)) ->
     let o c = (env_o, arity_o, pind_o, p_o, c) in
     let n c = (env_n, arity_n, pind_n, p_n, c) in
     let arity = if is_fwd then arity_o else arity_n in
     List.map2
       (fun c_o c_n ->
         shift_by
           (arity - npm)
           (orn_index_case evd index_i is_fwd indexer_f orn_p (o c_o) (n c_n)))
       (take_except (arity_o - npm + 1) (factor_product b_o))
       (take_except (arity_n - npm + 1) (factor_product b_n))
  | _ ->
     failwith "not an eliminator"
              
(*
 * This packs an ornamental promotion to/from an indexed type like Vector A n,
 * with n at index_i, into a sigma type. The theory of this is more elegant,
 * and the types are easier to reason about automatically. However,
 * the other version may be more desirable for users.
 *
 * It is simple to extract the unpacked version from this form;
 * later it might be useful to define both separately.
 * For now we have a metatheoretic guarantee about the indexer we return
 * corresponding to the projection of the sigma type.
 *
 * TODO later, refactor code common to both cases
 *)
let pack env evd index_typ f_indexer index_i npm ind ind_n arity is_fwd unpacked =
  let index_i = npm + index_i in
  if is_fwd then
    (* pack conclusion *)
    let off = arity - 1 in
    let unpacked_args = mk_n_rels off in
    let packed_args = insert_index_shift index_i (mkRel 1) unpacked_args 1 in
    let env_abs = push_local (Anonymous, index_typ) env in
    let packer = abstract_arg env_abs evd index_i (mkAppl (ind, packed_args)) in
    let index = mkAppl (f_indexer, mk_n_rels arity) in
    let index_typ = shift_by off index_typ in
    (env, mkAppl (existT, [index_typ; packer; index; unpacked]))
  else
    (* pack hypothesis *)
    let (from_n, _, unpacked_typ) = CRD.to_tuple @@ lookup_rel 1 env in
    let unpacked_args = unfold_args unpacked_typ in
    let packed_args = reindex_shift index_i (mkRel 1) unpacked_args 1 in
    let env_abs = push_local (Anonymous, shift index_typ) env in
    let packer = abstract_arg env_abs evd index_i (mkAppl (ind, packed_args)) in
    let packed_typ = mkAppl (sigT, [shift (shift index_typ); packer]) in
    let env_pop = pop_rel_context 1 env in
    let index_rel = nb_rel env_pop - index_i in
    let env_push = push_local (from_n, unshift packed_typ) env_pop in
    let packer_indexed = reduce_term env_push (mkAppl (packer, [mkRel (index_rel + 1)])) in
    let unpack_b_b = all_eq_substs (mkRel (4 - index_rel), mkRel 1) (shift_local index_rel 1 (shift unpacked)) in
    let unpack_b = mkLambda (Anonymous, shift_local 1 1 (all_eq_substs (mkRel (index_rel + 1), mkRel 1) packer_indexed), all_eq_substs (mkRel (index_rel + 3), mkRel 2) unpack_b_b) in
    let pack_unpacked = mkLambda (Anonymous, shift (shift index_typ), unpack_b) in
    let env_packed = remove_rel (index_rel + 1) env_push in
    let pack_off = unshift_local index_rel 1 pack_unpacked in
    let packer = unshift_local index_rel 1 packer in
    let elim_b = shift (mkAppl (ind_n, shift_all (mk_n_rels (arity - 1)))) in
    let elim_t = mkAppl (sigT, [shift index_typ; packer]) in
    let elim = mkLambda (Anonymous, elim_t, elim_b) in
    let packed = mkAppl (sigT_rect, [shift index_typ; packer; elim; pack_off; mkRel 1]) in
    (env_packed, packed)

(* 
 * Unpack
 * TODO only handles one of two directions for now
 *)
let unpack env orn =
  let (env_orn, body) = zoom_lambda_term env orn in
  reconstruct_lambda env_orn (last (unfold_args body))
              
(* Search two inductive types for an indexing ornament, using eliminators *)
let search_orn_index_elim evd npm idx_n elim_o o n is_fwd : (int option * types option * types) =
  let directional a b = if is_fwd then a else b in
  let call_directional f a b = if is_fwd then f a b else f b a in
  let (env_o, ind_o, arity_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elim_t_n) = n in
  let (index_i, index_t) = call_directional (index_type env_n) elim_t_o elim_t_n in
  let indexer = search_for_indexer evd index_i index_t npm elim_o o n is_fwd in
  let f_indexer = make_constant idx_n in
  let f_indexer_opt = directional (Some f_indexer) None in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
  | (Prod (n_o, p_o, b_o), Prod (n_n, p_n, b_n)) ->
     let env_ornament = zoom_env zoom_product_type env_o p_o in
     let env_o_b = push_local (n_o, p_o) env_o in
     let env_n_b = push_local (n_n, p_n) env_n in
     let off = offset env_ornament npm in
     let pms = shift_all_by off (mk_n_rels npm) in
     let (ind, arity) = directional (ind_n, arity_o) (ind_n, arity_n) in
     let align_pms = Array.of_list (List.map (unshift_by (arity - npm)) pms) in
     let align = stretch index_i env_o f_indexer align_pms in
     let elim_t = call_directional align (ind_o, elim_t_o) (ind_n, elim_t_n) in
     let elim_t_o = directional elim_t elim_t_o in
     let elim_t_n = directional elim_t_n elim_t in
     let o = (env_o_b, ind_o, arity_o, elim_t_o) in
     let n = (env_n_b, ind_n, arity_n, elim_t_n) in
     let off_b = offset env_ornament (nb_rel env_o_b) - (arity - npm) in
     let p = ornament_p index_i env_ornament ind arity npm f_indexer_opt in
     let p_cs = unshift_by (arity - npm) p in
     let cs = shift_all_by off_b (orn_index_cases evd index_i npm is_fwd f_indexer p_cs o n) in
     let final_args = Array.of_list (mk_n_rels off) in
     let index_i_o = directional (Some index_i) None in
     let unpacked = apply_eliminator elim_o pms p cs final_args in
     let packer ind ar = pack env_ornament evd index_t f_indexer index_i npm ind ind_n ar is_fwd unpacked in (* TODO clean args *)
     let packed = if is_fwd then (packer ind_n arity_n) else (packer ind_o arity_o) in
     (index_i_o, indexer, reconstruct_lambda (fst packed) (snd packed))
  | _ ->
     failwith "not eliminators"
              
(*
 * Search two inductive types for an indexing ornament
 *
 * TODO later: take sigma directly, so that we're told what the new index is, to simplify
 *)
let search_orn_index env evd npm idx_n o n is_fwd : (int option * types option * types) =
  let (pind_o, arity_o) = o in
  let (pind_n, arity_n) = n in
  let (ind_o, _) = destInd pind_o in
  let (ind_n, _) = destInd pind_n in
  let (elim_o, elim_n) = map_tuple (type_eliminator env) (ind_o, ind_n) in
  let (elim_t_o, elim_t_n) = map_tuple (infer_type env evd) (elim_o, elim_n) in
  let (env_o, elim_t_o') = zoom_n_prod env npm elim_t_o in
  let (env_n, elim_t_n') = zoom_n_prod env npm elim_t_n in
  let o = (env_o, pind_o, arity_o, elim_t_o') in
  let n = (env_n, pind_n, arity_n, elim_t_n') in
  search_orn_index_elim evd npm idx_n elim_o o n is_fwd
  

(* Search two inductive types for an ornament between them *)
let search_orn_inductive (env : env) evd (idx_n : Id.t) (trm_o : types) (trm_n : types) : promotion =
  match map_tuple kind_of_term (trm_o, trm_n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if not (npm_o = npm_n) then
       (* new parameter *)
       let search_params = twice (search_orn_params env) in
       let indexer = None in
       let index_i = None in
       if npm_o < npm_n then
         let (promote, forget) = search_params (i_o, ii_o) (i_n, ii_n) in
         { index_i; indexer; promote; forget }
       else
         let (promote, forget) = search_params (i_n, ii_n) (i_o, ii_o) in
         { index_i; indexer; promote; forget }
     else
       let npm = npm_o in
       let (typ_o, typ_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
       let (arity_o, arity_n) = map_tuple arity (typ_o, typ_n) in
       if not (arity_o = arity_n) then
         let o = (trm_o, arity_o) in
         let n = (trm_n, arity_n) in
         let (o, n) = map_if reverse (arity_n <= arity_o) (o, n) in
         let search_indices = twice (search_orn_index env evd npm idx_n) in
         let ((index_i, indexer, promote), (_, _, forget)) = search_indices o n in
         { index_i; indexer; promote; forget }
       else
         failwith "this kind of change is not yet supported"
  | _ ->
     failwith "this kind of change is not yet supported"

(* --- Application --- *)

(* TODO explain *)
let zoom_sig_outer is_fwd t =
  if is_fwd then
    t
  else
    try
      last (unfold_args (snd (zoom_lambda_term empty_env t)))
    with _ ->
      t
              
(* TODO explain *)
let zoom_sig is_fwd t =
  if is_fwd then
    t
  else
    try
      let lambda = zoom_sig_outer is_fwd t in
      first_fun (snd (zoom_lambda_term empty_env lambda))
    with _ ->
      t

(* zoom_sig if t actually applies sigT *)
let zoom_if_sig_outer t =
  if applies sigT t then
    zoom_sig_outer false t
  else
    t

(* Get the inductive type for t with no params, zooming if it's a sig *)
let inner_ind_type t =
  match kind_of_term (zoom_if_sig_outer t) with
  | Lambda (_, _, b) when isApp b ->
     first_fun b
  | App (_, _) ->
     first_fun t
  | _ ->
     failwith "failed to infer inductive type to match against"
              
(*
 * Substitute the ornamented type in the hypotheses.
 * Return both the term with ornamented hypotheses and the number
 * of substitutions that occurred.
 *)
let sub_in_hypos (l : lifting) (env : env) (index_lam : types) (from_ind : types) (to_ind : types) (hypos : types) =
  let is_fwd = l.is_fwd in
  let from_ind = zoom_sig is_fwd from_ind in
  map_unit_env_if_lazy
    (fun env trm ->
      match kind_of_term trm with
      | Lambda (_, t, _) ->
         is_or_applies from_ind (zoom_sig is_fwd (reduce_nf env t))
      | _ -> false)
    (fun env trm ->
      let (n, t, b) = destLambda trm in
      let t_args = unfold_args t in
      let t_ind = reduce_term env (mkAppl (to_ind, t_args)) in
      mkLambda (n, t_ind, b))
    env
    hypos

(*
 * Apply the ornament to the arguments
 * TODO clean this
 *)
let ornament_args env evd (from_ind, to_ind) (l : lifting) trm =
  let is_fwd = l.is_fwd in
  let orn_f = lift_back l in
  let typ = reduce_type env evd trm in
  let from_ind = zoom_sig is_fwd from_ind in
  let rec ornament_arg env i typ =
    match kind_of_term typ with
    | Prod (n, t, b) ->
       let ornament_b = ornament_arg (push_local (n, t) env) (unshift_i i) b in
       if is_or_applies from_ind (zoom_sig is_fwd (reduce_nf env t)) then
         let t_args = unfold_args (shift_by i t) in
         mkAppl (orn_f, snoc (mkRel i) t_args) :: ornament_b
       else
         mkRel i :: ornament_b
    | _ ->
       []
  in mkAppl (trm, ornament_arg env (arity typ) typ)

(* Ornament the hypotheses *)
let ornament_hypos env evd (l : lifting) (from_ind, to_ind) trm =
  let orn = l.orn in
  let indexer = Option.get orn.indexer in
  let indexer_type = reduce_type env evd indexer in
  let index_lam = remove_final_hypo (prod_to_lambda indexer_type) in
  let hypos = on_type prod_to_lambda env evd trm in
  let subbed_hypos = sub_in_hypos l env index_lam from_ind to_ind hypos in
  let env_hypos = zoom_env zoom_lambda_term env subbed_hypos in
  let concl = ornament_args env_hypos evd (from_ind, to_ind) l trm in
  reconstruct_lambda env_hypos concl

(* Ornament the conclusion *)
let ornament_concls concl_typ env evd (l : lifting) (from_ind, to_ind) trm =
  let is_fwd = l.is_fwd in
  let from_ind = zoom_sig is_fwd from_ind in
  if is_or_applies from_ind (zoom_sig is_fwd concl_typ) then
    let (env_zoom, trm_zoom) = zoom_lambda_term env trm in
    let concl_args =
      if is_fwd then
        unfold_args concl_typ
      else
        let concl_typ = snd (zoom_lambda_term empty_env (last (unfold_args concl_typ))) in
        let concl_args = unfold_args concl_typ in
        try
          remove_index
            (Option.get l.orn.index_i)
            (unshift_all concl_args)
        with _ ->
          concl_args
    in
    let args =
      List.map
        (fun a ->
          map_unit_env_if
            (fun env trm ->
              try
                on_type (is_or_applies to_ind) env evd trm
              with _ ->
                false)
            (fun env trm ->
              mkAppl (lift_back l, snoc trm (on_type unfold_args env evd trm)))
            env_zoom
            a)
        concl_args
    in
    let concl = mkAppl (lift_to l, snoc trm_zoom args) in
    reconstruct_lambda env_zoom concl
  else
    trm

(*
 * Determine if the direction is forwards or backwards
 * True if forwards, false if backwards
 *)
let direction (env : env) evd (orn : types) : bool =
  let rec wrapped (from_ind, to_ind) =
    if not (applies sigT from_ind) then
      true
    else
      if not (applies sigT to_ind) then
        false
      else
        let (from_args, to_args) = map_tuple unfold_args (from_ind, to_ind) in
        wrapped (map_tuple last (from_args, to_args))
  in wrapped (ind_of_orn (reduce_type env evd orn))

(*
 * Initialize an ornamentation
 * TODO move up
 *)
let initialize_orn env evd promote forget =
  let promote_unpacked = unpack env (unwrap_definition env promote) in
  let to_ind = snd (on_type ind_of_orn env evd promote_unpacked) in
  let to_args = unfold_args to_ind in
  let to_args_idx = List.mapi (fun i t -> (i, t)) to_args in
  let (index_i, index) = List.find (fun (_, t) -> contains_term (mkRel 1) t) to_args_idx in
  let index_i = Some index_i in
  let indexer = Some (first_fun index) in
  { index_i; indexer; promote; forget }
                                      
(*
 * Apply an ornament, but don't reduce the result.
 *
 * Assumes indexing ornament for now.
 * For a version that dealt with eliminating the sigma type, but was messier,
 * see code prior to 3/15. For now, we leave that step to later,
 * since it's much nicer that way.
 *)
let ornament_no_red (env : env) evd (orn_f : types) (orn_inv_f : types) (trm : types) =
  let is_fwd = direction env evd orn_f in
  let (promote, forget) = map_if reverse (not is_fwd) (orn_f, orn_inv_f) in
  let orn = initialize_orn env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let orn_type = reduce_type env evd orn.promote in
  let (from_with_args, to_with_args) = ind_of_orn orn_type in
  let env_to = pop_rel_context 1 (fst (zoom_product_type env orn_type)) in
  let from_ind = first_fun from_with_args in
  let to_ind = reconstruct_lambda env_to (unshift to_with_args) in
  let app_orn ornamenter = ornamenter env evd l (map_if reverse (not is_fwd) (from_ind, to_ind)) in
  let (env_concl, concl_typ) = zoom_product_type env (reduce_type env evd trm) in
  let concl_typ = reduce_nf env_concl concl_typ in
  app_orn (ornament_concls concl_typ) (app_orn ornament_hypos trm)

(* --- Reduction --- *)

(*
 * Compose two properties for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *)
let compose_p evd npms post_assums inner (comp : composition) =
  let l = comp.l in
  let index_i = Option.get l.orn.index_i in
  let (env_g, p_g) = comp.g in
  let (env_f, p_f) = comp.f in
  let (env_p_f, p_f_b_old) = zoom_lambda_term env_f p_f in
  let off = nb_rel env_p_f - nb_rel env_f in
  let orn_app =
    if not inner then
      shift_local off (off + List.length post_assums) (mkAppl (lift_back l, mk_n_rels (npms + 1)))
    else
      let inner = mkRel 1 in
      let typ = reduce_type env_p_f evd inner in
      let typ_args = unfold_args typ in
      let index = mkRel 2 in
      let index_typ = infer_type env_p_f evd index in
      let unpacked_args = unfold_args typ in
      let packer = abstract_arg env_p_f evd index_i typ in
      let unpacked = mkAppl (existT, [index_typ; packer; index; inner]) in
      mkAppl (lift_back l, snoc unpacked (remove_index index_i typ_args))
  in
  let (_, p_f_b) = zoom_lambda_term env_p_f (zoom_if_sig_outer p_f_b_old) in
  let p_f_b_args = map_if (remove_index index_i) (not (eq_constr p_f_b_old p_f_b)) (unfold_args p_f_b) in
  let (_, non_pms) = take_split npms p_f_b_args in
  let p_args = snoc orn_app non_pms in
  let f_g_off = nb_rel env_f - nb_rel env_g in
  let p_g = shift_by f_g_off p_g in
  let p_g = shift_by off p_g in
  let p_g =
    map_if
      (map_unit_if
         (is_or_applies existT)
         (fun trm ->
           (* TODO not sufficiently general, can break, try to *)
           let last_arg = last (unfold_args trm) in
           if contains_term last_arg (mkRel 1) then
             last_arg
           else
             trm))
           (* TODO will fail with cosntant existT like nilV, try *)
      (not l.is_fwd)
      p_g
  in
  let p =
    map_forward
      (fun p_g ->
        map_default
          (fun indexer ->(* TODO may not yet handle HOFs *)
            let (env_p_g, p_g_b_old) = zoom_lambda_term env_g p_g in
            let p_g_b_as = reindex index_i (mkRel 1) (unfold_args (shift p_g_b_old)) in
            let p_g_b = mkAppl (first_fun p_g_b_old, p_g_b_as) in
            let pack_index = mkRel 2 in
            let index_typ = infer_type env_p_f evd pack_index in
            let p_g_l = mkLambda (Anonymous, index_typ, p_g_b) in
            let p_g_packed = mkAppl (sigT, [index_typ; p_g_l]) in
            reconstruct_lambda_n env_p_g p_g_packed (nb_rel env_g))
          p_g
          l.lifted_indexer)
      l
      p_g
  in let app = reduce_term env_p_f (mkAppl (p, p_args)) in
  reconstruct_lambda_n env_p_f app (nb_rel env_f)

(*
 * Compose the IH for a constructor.
 * This simply uses the new property p.
 *)
let compose_ih env_g evd npms_g ip_g c_f p =
  let ip_g_typ = reduce_type env_g evd ip_g in
  let from_typ = first_fun (fst (ind_of_orn ip_g_typ)) in
  map_term_env_if
    (fun _ _ trm -> is_or_applies from_typ trm)
    (fun en p trm ->
      let orn_final = [mkRel 1] in
      let (_, _, orn_final_typ) = CRD.to_tuple @@ lookup_rel 1 en in
      let typ_args = shift_all (unfold_args orn_final_typ) in
      let (_, non_pms) = take_split npms_g typ_args in
      reduce_term en (mkAppl (mkAppl (p, non_pms), orn_final)))
    shift
    env_g
    p
    c_f

(*
 * TODO move
 * Only reduce until you have an application of an induction principle,
 * or reducing doesn't change the term
 * Then, do nothing
 *)
let rec reduce_to_ind env trm =
  match kind_of_term trm with
  | App (_, _) when is_elim env (first_fun trm) ->
     trm
  | _ ->
     let reduced = chain_reduce reduce_term delta env trm in
     map_if (reduce_to_ind env) (not (eq_constr reduced trm)) reduced

(*
 * TODO move
 *)
let project_index index_typ typ trm =
  mkAppl (projT1, [index_typ; typ; trm])

(*
 * TODO move
 *)
let project_value index_typ typ trm =
  mkAppl (projT2, [index_typ; typ; trm])

(* TODO move *)
let reindex_body index_i index trm =
  mkAppl (first_fun trm, reindex index_i index (unfold_args trm))
            
(*
 * TODO move
 * Delta-unfold, simplify, delta-unfold internally, simplify, and so on
 * until nothing changes
 *
 * for reducing ornaments
 * assumes promotion for now
 * also assumes assumption at index 1,
 * need to support IHs at other indices. (TODO)
 *)
let reduce_ornament_f l env evd index_i orn trm orn_args =
  let orn_arg_typs = List.map (fun a -> zoom_if_sig_outer (infer_type env evd a)) orn_args in
  let orn_arg_typs = List.map (map_if (fun t -> unshift (snd (zoom_lambda_term empty_env t))) (not l.is_fwd)) orn_arg_typs in
  (* TODO inefficient now *)
  List.fold_left2
    (fun trm orn_arg orn_arg_typ ->
       map_term_env_if
         (fun _ orn_arg_typ trm -> applies orn trm)
         (fun env orn_arg_typ trm ->
           try
             let (app, app_sub_body, app_sub) =
               let unfolded = chain_reduce reduce_term delta env trm in
               let typ_args = map_if (remove_index index_i) (not l.is_fwd) (unfold_args orn_arg_typ) in
               let orn_app = mkAppl (orn, snoc orn_arg typ_args) in
               let orn_app_ind = reduce_to_ind env orn_app in
               let orn_app_red = reduce_nf env orn_app in
               if l.is_fwd && not l.is_indexer then
                 let indexer = reduce_nf env (get_arg 2 unfolded) in
                 let app = reduce_nf env (get_arg 3 unfolded) in
                 let orn_app_app = get_arg 3 orn_app_ind in
                 let orn_app_app_arg = last (unfold_args orn_app_app) in
                 let packed_type_old = reduce_type env evd orn_app_app in
                 let index_type = reduce_type env evd (get_arg index_i packed_type_old) in
                 let packed_type = abstract_arg env evd index_i packed_type_old in
                 let orn_app_indexer = project_index index_type packed_type orn_app_app_arg in
                 let orn_app_app_arg = project_value index_type packed_type orn_app_app_arg in
                 let orn_app_red_app = get_arg 3 orn_app_red in
                 let orn_app_indexer_red = get_arg 2 orn_app_red in
                 let ind_sub = all_eq_substs (orn_app_indexer_red, orn_app_indexer) indexer in
                 let app_sub = all_eq_substs (orn_app_red_app, orn_app_app_arg) app in
                 let app_ind_sub = all_eq_substs (orn_app_indexer_red, orn_app_indexer) app_sub in
                 (app, app_ind_sub, mkAppl (existT, reindex 3 app_ind_sub (reindex 2 ind_sub (unfold_args unfolded))))
               else if not l.is_indexer then
                 let app = reduce_nf env unfolded in
                 let index_type = get_arg 0 (infer_type env evd orn_arg) in
                 let packed_body = reindex_body index_i (mkRel 1) (shift orn_arg_typ) in
                 let packed_type = mkLambda (Anonymous, index_type, packed_body) in
                 let app_projT1 = project_index index_type packed_type orn_arg in
                 let app_projT2 = project_value index_type packed_type orn_arg in
                 let orn_app_app = mkAppl (get_arg 3 orn_app_ind, [app_projT1; app_projT2]) in
                 let orn_app_app_red = reduce_nf env orn_app_app in
                 let app_sub = all_eq_substs (orn_app_app_red, orn_arg) app in
                 (* TODO is that sound? think more about other cases *)
                 (app, app_sub, app_sub)
               else
                 let app = reduce_nf env unfolded in
                 let app_sub = all_eq_substs (orn_app_red, orn_app) app in
                 (app, app_sub, app_sub)
             in if eq_constr app_sub_body app then trm else app_sub
           with _ ->
             trm)
         shift
         env
         orn_arg_typ
         trm)
    trm
    orn_args
    orn_arg_typs

(*
 * Get the (index arg index, IH) pairs for a constructor
 *)
let rec indexes env to_typ index_i f_hs g_hs trm i =
  let num_args = List.length g_hs in
  if List.length f_hs != num_args then
    match (g_hs, kind_of_term trm) with
    | (h :: tl, Prod (n, t, b)) ->
       let index_ih_opt = index_ih index_i to_typ (mkRel 1) b (num_args - (i + 1)) in
       map_if
         (fun tl -> (i, Option.get index_ih_opt) :: tl)
         (Option.has_some index_ih_opt)
         (indexes (push_local (n, t) env) to_typ index_i f_hs tl b (i + 1))
    | _ ->
       []
  else
    []
  
(*
 * Compose two constructors for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * For now, this does not handle nested induction.
 *
 * TODO clean, refactor orn/deorn, take fewer arguments, etc.
 * TODO can massively simplify with packed type, but will take work
 * to figure out exactly what can go
 *)
let compose_c evd npms_g ip_g p post_assums (comp : composition) =
  let l = comp.l in
  let index_i = Option.get l.orn.index_i in
  let (env_g, c_g) = comp.g in
  let (env_f, c_f) = comp.f in
  let (orn_f, orn_g) = (lift_back l, lift_to l) in
  let orn_f_typ = reduce_type env_f evd orn_f in
  let orn_g_typ = reduce_type env_g evd orn_g in
  let ind_f_typ = fst (ind_of_orn orn_f_typ) in
  let ind_g_typ = fst (ind_of_orn orn_g_typ) in
  let to_typ = inner_ind_type ind_f_typ in
  let from_typ = inner_ind_type ind_g_typ in
  let (to_typ, from_typ) = map_if reverse (not l.is_fwd) (to_typ, from_typ) in
  let is_deorn = is_or_applies (if l.is_fwd then to_typ else from_typ) in
  let c_f_used = get_used_or_p_hypos is_deorn c_f in
  let c_g_used = get_used_or_p_hypos always_true c_g in
  let (env_f_body_old, _) = zoom_lambda_term env_f c_f in
  let c_f = compose_ih env_g evd npms_g ip_g c_f p in
  let (env_f_body, f_body) = zoom_lambda_term env_f c_f in
  let (env_g_body, g_body) = zoom_lambda_term env_g c_g in
  let off_f = offset env_f_body (nb_rel env_f) in
  let off_g = offset env_g_body (nb_rel env_g) in
  let is_g = comp.is_g in
  let f_body =
    if not is_g then
      let num_assums = List.length post_assums in
      (* TODO f_f logic unclear *)
      let f_f = shift_local (if l.is_fwd then 0 else num_assums) (offset env_f (nb_rel env_g)) c_g in
      let f = shift_by off_f f_f in
      let c_used = c_g_used in
      let index_args = indexes env_g to_typ index_i c_f_used c_g_used (lambda_to_prod c_g) 0 in
      let args =
        List.mapi
          (fun i arg ->
            if (not l.is_fwd) && (List.mem_assoc i index_args) then
              let index_type = infer_type env_g_body evd arg in
              let (ih, _) = List.assoc i index_args in
              let ih_typ = reduce_type env_f_body evd ih in
              let indexer = Option.get l.orn.indexer in
              let typ_args = unfold_args (reduce_term env_f_body ih_typ) in
              let orn = mkAppl (lift_back l, snoc ih typ_args) in
              let orn_typ = reduce_type env_f_body evd orn in
              let packed_type = get_arg 1 orn_typ in
              project_index index_type packed_type orn
              (*let orn = mkAppl (indexer, snoc ih typ_args) in
              orn*)
            else
              map_unit_env_if
                (fun env trm -> on_type is_deorn env evd trm)
                (fun env trm ->
                  let typ = reduce_type env evd trm in
                  if l.is_fwd then
                    let index = get_arg index_i typ in
                    let index_typ = infer_type env evd index in
                    let unpacked_args = unfold_args typ in
                    let packer = abstract_arg env evd index_i typ in
                    let deindexed = remove_index index_i unpacked_args in
                    let packed = mkAppl (existT, [index_typ; packer; index; trm]) in
                    mkAppl (orn_f, snoc packed deindexed)
                  else
                    let typ_args = unfold_args typ in
                    let orn = mkAppl (orn_f, snoc trm typ_args) in
                    let orn_typ = reduce_type env evd orn in
                    let packed_type = get_arg 1 orn_typ in
                    (* line below sensitive to how we define ornaments *)
                    let (_, index_type, _) = destLambda packed_type in
                    project_value index_type packed_type orn)
              env_f_body
              arg)
          c_used
      in reduce_term env_f_body (mkAppl (f, args))
    else
      let c_f_all = get_used_or_p_hypos always_true c_f in
      let index_args = indexes env_g to_typ index_i c_f_all c_g_used (lambda_to_prod (if l.is_fwd then c_f else c_g)) 0 in
      let f = map_indexer (fun l -> Option.get l.orn.indexer) lift_to l l in
      
      let is_orn env trm =
        let typ = if l.is_fwd then from_typ else shift_by (nb_rel env_f_body - 1) ind_g_typ in
        is_or_applies typ trm || convertible env typ trm
      in
      (* Does this generalize, too? *)
      let f_body =
       map_unit_env_if
         (fun env trm ->
           on_type (is_orn env) env evd trm)
         (fun env trm ->
           let args = unfold_args trm in
           let ihs = List.map (fun (_, (ih, _)) -> ih) index_args in
           let typ_args =
             if l.is_fwd then
               on_type unfold_args env evd trm
             else
               let typ = reduce_type env evd trm in
               let packer = get_arg 1 typ in
               if isLambda packer then (* TODO hack with vector A *)
                 let packer_body = unshift (snd (zoom_lambda_term env packer)) in
                 remove_index index_i (unfold_args packer_body)
               else
                 unfold_args packer
           in
           let app_pre_red = mkAppl (f, snoc trm typ_args) in
           let orn_args = mk_n_rels (nb_rel env) in
           let orn_args = List.filter (on_type (is_orn env) env evd) orn_args in
           (* TODO reinspect condition below, may be bad sometimes *)
           let app =
             map_if
               (reduce_nf env)
               (List.length index_args = 0 && not l.is_indexer)
               (map_unit_if
                  (applies f)
                  (fun trm ->
                    let from = last (unfold_args trm) in 
                    if l.is_indexer then
                      if is_or_applies (lift_back l) from then
                        let last_arg = last (unfold_args from) in
                        let last_arg_typ = reduce_type env evd last_arg in
                        let index_type = get_arg 0 last_arg_typ in
                        let packed_type = get_arg 1 last_arg_typ in
                        let app_projT1 = project_index index_type packed_type last_arg in
                        reduce_ornament_f l env evd index_i f app_projT1 orn_args              
                      else
                        reduce_ornament_f l env evd index_i f trm orn_args
                    else if l.is_fwd then
                      if is_or_applies (lift_back l) from then
                        let existT_app = last (unfold_args from) in
                        reduce_ornament_f l env evd index_i f existT_app orn_args
                      else
                        reduce_ornament_f l env evd index_i f trm orn_args
                    else
                      if is_or_applies existT from then
                        let proj = last (unfold_args from) in
                        if is_or_applies projT2 proj then
                          let unpacked = last (unfold_args proj) in
                          let unpacked_from = last (unfold_args unpacked) in
                          reduce_ornament_f l env evd index_i f unpacked_from orn_args
                        else if is_or_applies (lift_to l) proj then
                          reduce_ornament_f l env evd index_i f (last (unfold_args proj)) orn_args
                        else
                          reduce_ornament_f l env evd index_i f trm orn_args
                      else if is_or_applies (lift_back l) from then
                        let last_arg = last (unfold_args from) in
                        reduce_ornament_f l env evd index_i f last_arg orn_args
                      else
                        reduce_ornament_f l env evd index_i f trm orn_args)
                  app_pre_red)
           in
           map_unit_if
             (fun trm ->
               isApp trm &&
               applies f trm &&
               List.exists (eq_constr (last (unfold_args trm))) ihs)
             (fun t -> last (unfold_args t))
             app)
         env_f_body_old
         f_body
      in map_if (map_unit_if (applies existT) (get_arg 3)) (not l.is_fwd) f_body
  in reconstruct_lambda_n env_f_body f_body (nb_rel env_f)

(* Map compose_c *)
let compose_cs evd npms ip p post_assums comp gs fs =
  let comp_cs =
    List.map2
      (fun c_g c_f -> { comp with g = (fst gs, c_g); f = (fst fs, c_f)})
      (snd gs)
      (snd fs)
  in List.map (compose_c evd npms ip p post_assums) comp_cs

(*
 * Compose two applications of an induction principle that are
 * structurally the same when one is an ornament.
 *
 * TODO clean
 *)
let rec compose_inductive evd idx_n post_assums assum_ind inner (comp : composition) =
  let l = comp.l in
  let index_i = Option.get l.orn.index_i in
  let (env_g, g) = comp.g in
  let (env_f, f) = comp.f in
  let (ip, pms, p_f, cs_f, args) = deconstruct_eliminator env_f evd f in
  let (ip_g, pms_g, p_g, cs_g, args_g) = deconstruct_eliminator env_g evd g in
  let npms = List.length pms_g in
  let (comp, indexer) =
    if l.is_fwd && comp.is_g && not l.is_indexer then
      (* Build the lifted indexer *)
      let indexer = Option.get l.orn.indexer in
      let (env_f_body, f_body) = zoom_lambda_term env_f f in
      let f_typ_args = on_type unfold_args env_f_body evd f_body in
      let index_args = snoc f_body f_typ_args in
      let indexer_unpacked_body = mkAppl (indexer, index_args) in
      let indexer_unpacked = reconstruct_lambda_n_skip env_f_body indexer_unpacked_body (nb_rel env_f_body - 2) (assum_ind - 1) in
      let env_packed = pop_rel_context (assum_ind + 2 - 1) env_f_body in
      let index_type = infer_type env_f_body evd (mkRel (2 + assum_ind - 1)) in
      let packer = infer_type env_packed evd (mkRel (1 + assum_ind - 1)) in
      let packed_type_b = shift index_type in
      let packed_type = mkLambda (Anonymous, packer, packed_type_b) in
      let indexer_body = mkAppl (sigT_rect, [index_type; packer; packed_type; indexer_unpacked; mkRel (1 + List.length post_assums)]) in
      let indexer = reconstruct_lambda env_packed indexer_body in
      let lifted_indexer = Some (make_constant idx_n) in
      let l = { l with lifted_indexer } in
      ({ comp with l }, Some indexer)
    else
      (comp, None)
  in
  let c_p = { comp with g = (env_g, p_g); f = (env_f, p_f) } in
  let p = compose_p evd npms post_assums inner c_p in
  let (cs, indexer) =
    if applies sigT_rect f then
      (* TODO factoring should handle *)
      (* bubble inside the sigT_rect (is this the best way?) *)
      let c = List.hd cs_f in
      let (env_c, c_body) = zoom_lambda_term env_f c in
      let c_cs = { comp with f = (env_c, c_body)} in
      let (c_comp, indexer) = compose_inductive evd idx_n post_assums assum_ind true c_cs in
      ([reconstruct_lambda_n env_c c_comp (nb_rel env_f)], indexer)
    else
      let (env_g, cs_g) =
        map_if
          (fun (env, cs) ->
            let (env_c, c) = zoom_lambda_term env (List.hd cs) in
            let (_, _, _, cs, _) = deconstruct_eliminator env_c evd c in
            (env_c, cs))
          (applies sigT_rect g)
          (env_g, cs_g)
      in
      let gs = (env_g, cs_g) in
      let fs = (env_f, cs_f) in
      (compose_cs evd npms ip_g p post_assums comp gs fs, indexer)
  in (apply_eliminator ip pms p cs args, indexer)
    

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
          if applies sigT_rect t then
            (* indexer *)
            Some (last (unfold_args t))
          else
            (* function *)
            let unorn = unwrap_definition env (first_fun t) in
            let (_, unorn_typ) = zoom_product_type env (infer_type env evd unorn) in
            let unorn_typ_args = unfold_args unorn_typ in
            let assum_i = arity unorn - destRel (last unorn_typ_args) in
            Some (last (unfold_args (get_arg assum_i t)))
        in c := c'; t)
      trm
  in Option.get !c

(*
 * Factor an ornamented, but not yet reduced function
 *)
let factor_ornamented (orn : promotion) (env : env) evd (trm : types) =
  let assum = get_assum orn env evd trm in
  (destRel assum, factor_term_dep assum env evd trm)

(*
 * Compose factors of an ornamented, but not yet reduced function
 *)
let rec compose_orn_factors evd (l : lifting) no_reduce assum_ind idx_n fs =
  let promote = l.orn.promote in
  let forget = l.orn.forget in
  let orn_indexer = Option.get l.orn.indexer in
  match fs with
  | Factor ((en, t), children) ->
     if List.length children > 0 then
       let post_assums = mk_n_rels (assum_ind - 1) in
       let child = List.hd (List.rev children) in
       let ((t_app, indexer), env, composed) = compose_orn_factors evd l no_reduce assum_ind idx_n child in
       let (e_body, t_body) = zoom_lambda_term en t in
       let body_uses f = is_or_applies f t_body in
       let uses f = (is_or_applies f t_app || body_uses f) && isApp t_app in
       let (env_promote, promote_exp) = zoom_lambda_term env (delta env promote) in
       let promote_inner = get_arg 3 promote_exp in
       let promote_inner_recons = reconstruct_lambda_n env_promote promote_inner (nb_rel env) in
       let t_app_typ = reduce_type env evd t_app in
       let t_app_args = unfold_args t_app_typ in
       let deindex = List.exists (applies orn_indexer) t_app_args in
       let promote_args = map_if (remove_index (Option.get l.orn.index_i)) deindex t_app_args in
       let promote_param = reduce_term env (mkAppl (promote_inner_recons, snoc (mkRel assum_ind) promote_args)) in
       let promotes = uses promote || uses promote_param in
       let forgets = uses forget in
       let is_indexer_inner =
         let body_is = is_or_applies sigT_rect t_body in
         let app_is = is_or_applies sigT_rect t_app in
         if app_is || body_is then
           let inner = get_arg 3 (if body_is then t_body else t_app) in
           let (_, inner_zoom) = zoom_lambda_term env inner in
           is_or_applies orn_indexer inner_zoom
         else
           false
       in
       let is_indexer = uses orn_indexer || is_indexer_inner in
       if promotes || forgets || is_indexer then
         let orn_f = if promotes then promote else if forgets then forget else orn_indexer in
         let is_g = applies orn_f t_body || is_or_applies promote_param t_body in
         let l = { l with is_indexer } in
         let g = (e_body, reduce_to_ind e_body t_body) in
         let f = (env, reduce_to_ind env t_app) in
         let comp = { l ; g ; f ; is_g } in
         if applies sigT_rect (snd g) && applies existT (snd f) then
           (* eliminate the existT [TODO move] *)
           let g_inner = get_arg 3 (snd g) in
           let cs_f = List.tl (List.tl (unfold_args (snd f))) in
           let inner = mkAppl (g_inner, cs_f) in
           let inner_factors = factor_term_dep (mkRel assum_ind) (fst f) evd inner in
           compose_orn_factors evd l true assum_ind idx_n inner_factors
         else if applies sigT_rect (snd f) && applies existT (snd g) then
           (* eliminate the existT [TODO move] *)
           let f_inner = get_arg 3 (snd f) in
           let (env_f_inner, f_inner_body) = zoom_lambda_term (fst f) f_inner in
           let c_g = last (unfold_args (snd g)) in
           let c_g_f = reconstruct_lambda (fst g) c_g in
           let c_f = reduce_term (fst g) (mkAppl (c_g_f, List.rev (List.tl (List.rev (unfold_args t_body))))) in
           let inner = mkAppl (shift_by 2 c_f, [f_inner_body]) in
           let inner_factors = factor_term_dep (mkRel assum_ind) env_f_inner evd inner in
           let ((t_app_inner, indexer_inner), env_inner, composed_inner) = compose_orn_factors evd l true assum_ind idx_n inner_factors in
           let app_lam = reconstruct_lambda_n_skip env_inner t_app_inner (nb_rel env_inner - 2) (assum_ind - 1) in
           let env_inner' = pop_rel_context (assum_ind + 2 - 1) env_inner in
           let f_p_old = get_arg 2 (snd f) in
           let (env_f_p, _) = zoom_lambda_term empty_env f_p_old in
           let f_p_body = unshift (reduce_type env_inner evd t_app_inner) in
           let f_p_new = reconstruct_lambda env_f_p (unshift_by (assum_ind - 1) f_p_body) in
           let f_args = unfold_args (snd f) in
           let args = reindex 3 app_lam (reindex 2 f_p_new f_args) in
           let app = mkAppl (sigT_rect, args) in
           ((app, indexer_inner), env_inner', composed_inner)
         else if applies sigT_rect (snd g) && is_indexer_inner then
           let inner = get_arg 3 (snd g) in
           let (env_inner, inner_body) = zoom_lambda_term (fst g) inner in
           let inner_factors = factor_term_dep (mkRel assum_ind) env_inner evd inner_body in
           let ((t_app_inner, indexer_inner), env_inner, composed_inner) = compose_orn_factors evd l true assum_ind idx_n inner_factors in
           let indexer_lam = reconstruct_lambda_n env_inner t_app_inner (nb_rel env_inner - 2) in
           let args = reindex 3 indexer_lam (unfold_args (snd g)) in
           let indexer = mkAppl (sigT_rect, args) in
           ((indexer, indexer_inner), pop_rel_context 2 env_inner, composed_inner)
         else
           let (app, indexer) = compose_inductive evd idx_n post_assums assum_ind false comp in
           ((app, indexer), env, true)
       else
         let t = shift_by assum_ind t in
         let t_args =
           if not composed then
             t_app :: post_assums
           else
             [t_app]
         in ((reduce_term env (mkAppl (t, t_args)), indexer), env, composed)
     else
       ((t, None), en, false)
  | Unit ->
     failwith "unexpected"
                  
(*
 * This takes a term (f o orn_inv) and reduces it to f' where orn_inv is
 * moved inside of the function.
 *
 * It assumes the term is in an easy-to-factor form (the form apply produces).
 * It also does not yet handle terms like append where the final result
 * is then ornamented. It also does not yet handle proofs like app_nil_r
 * where the type of the final result is no longer definable as-is.
 * It also does not yet handle any situations where f is not just an application
 * of the induction principle for the unornamented type. Basically,
 * this is a very preliminary attempt at solving this problem, which I
 * will build on.
 *)
let internalize (env : env) evd (idx_n : Id.t) (orn : types) (orn_inv : types) (trm : types) =
  let is_fwd = direction env evd orn in
  let (promote, forget) =  map_if reverse (not is_fwd) (orn, orn_inv) in
  let orn = initialize_orn env evd promote forget in                         
  let l = initialize_lifting orn is_fwd in
  let (assum_ind, factors) = factor_ornamented orn env evd trm in
  let ((internalized, indexer), env, _) = compose_orn_factors evd l false assum_ind idx_n factors in
  (reconstruct_lambda env internalized, indexer)


(* --- Top-level --- *)

(* Identify an ornament *)
let find_ornament n d_old d_new =
  let (evm, env) = Lemmas.get_current_context () in
  let trm_o = unwrap_definition env (intern env evm d_old) in
  let trm_n = unwrap_definition env (intern env evm d_new) in
  if isInd trm_o && isInd trm_n then
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env evm idx_n trm_o trm_n in
    let idx = orn.indexer in
    (if Option.has_some idx then
       let _ = define_term idx_n env evm (Option.get idx) in
       Printf.printf "Defined indexing function %s.\n\n" (string_of_id idx_n);
     else
       ());
    define_term n env evm orn.promote;
    Printf.printf "Defined promotion %s.\n\n" (string_of_id n);
    let inv_n = with_suffix n "inv" in
    define_term inv_n env evm orn.forget;
    Printf.printf "Defined forgetful function %s.\n\n" (string_of_id inv_n);
    ()
  else
    failwith "Only inductive types are supported"

(* Apply an ornament, but don't reduce *)
let apply_ornament n d_orn d_orn_inv d_old =
  let (evm, env) = Lemmas.get_current_context () in
  let c_orn = intern env evm d_orn in
  let c_orn_inv = intern env evm d_orn_inv in
  let c_o = intern env evm d_old in
  let trm_n = ornament_no_red env evm c_orn c_orn_inv c_o in
  define_term n env evm trm_n;
  Printf.printf "Defined ornamented fuction %s.\n\n" (string_of_id n);
  ()

(* Reduce an application of an ornament *)
let reduce_ornament n d_orn d_orn_inv d_old =
  let (evm, env) = Lemmas.get_current_context () in
  let c_orn = intern env evm d_orn in
  let c_orn_inv = intern env evm d_orn_inv in
  let c_o = intern env evm d_old in
  let trm_o = unwrap_definition env c_o in
  let idx_n = with_suffix n "index" in
  let (trm_n, indexer) = internalize env evm idx_n c_orn c_orn_inv trm_o in
  (if Option.has_some indexer then
     let indexer_o = Option.get indexer in
     let (indexer_n, _) = internalize env evm idx_n c_orn c_orn_inv indexer_o in
     define_term idx_n env evm indexer_n;
     Printf.printf "Defined indexer %s.\n\n" (string_of_id idx_n)
   else
     ());
  define_term n env evm trm_n;
  Printf.printf "Defined reduced ornamened function %s.\n\n" (string_of_id n);
  ()

(* --- Commands --- *)

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ find_ornament n d_old d_new ]
END

(*
 * Given an ornament and a function, derive the ornamented version that
 * doesn't internalize the ornament.
 *
 * This is equivalent to porting the hypotheses and conclusions we apply
 * the function to via the ornament, but not actually reducing the
 * result to get something of a useful type. It's the first step in
 * lifting functions, which will be chained eventually to lift
 * functions entirely.
 *)
VERNAC COMMAND EXTEND ApplyOrnament CLASSIFIED AS SIDEFF
| [ "Apply" "ornament" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ apply_ornament n d_orn d_orn_inv d_old ]
END

(*
 * Reduce an application of an ornament.
 *)
VERNAC COMMAND EXTEND ReduceOrnament CLASSIFIED AS SIDEFF
| [ "Reduce" "ornament" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ reduce_ornament n d_orn d_orn_inv d_old ]
END
