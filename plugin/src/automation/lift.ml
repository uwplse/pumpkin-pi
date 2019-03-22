(*
 * Core lifting algorithm
 *)

open Util
open Constr
open Environ
open Zooming
open Lifting
open Coqterms
open Debruijn
open Utilities
open Indexing
open Hypotheses
open Names
open Caching
open Declarations
open Specialization
open Printing

(* --- Internal lifting configuration --- *)

(*
 * Lifting configuration, along with a cache for constants encountered
 * as the algorithm traverses, and cache for the constructor rules
 * that refolding determines
 *)
type lift_config =
  {
    l : lifting;
    constr_rules : types array;
    cache : temporary_cache
  }

(* --- Recovering types from ornaments --- *)

(*
 * Get the types A, B, and IB from the ornament
 *)
let typs_from_orn l env evd =
  let (a_i_t, b_i_t) = on_type ind_of_promotion_type env evd l.orn.promote in
  let a_t = first_fun a_i_t in
  let b_t = zoom_sig b_i_t in
  let i_b_t = (dest_sigT b_i_t).index_type in
  (a_t, b_t, i_b_t)

(* --- Premises --- *)

(*
 * Determine whether a type is the type we are ornamenting from
 * That is, A when we are promoting, and B when we are forgetting
 *)
let is_from l env evd (a_typ, b_typ) typ =
  if l.is_fwd then
    is_or_applies a_typ typ
  else
    if is_or_applies sigT typ then
      equal b_typ (first_fun (dummy_index env (dest_sigT typ).packer))
    else
      false

(* 
 * Determine whether a term has the type we are ornamenting from
 *)
let type_is_from l env evd (a_typ, b_typ) trm =
  let typ = reduce_nf env (infer_type env evd trm) in
  is_from l env evd (a_typ, b_typ) typ

(*
 * Filter the arguments to only the ones that have the type we are
 * promoting/forgetting from.
 *)
let filter_orn l env evd (a_typ, b_typ) args =
  List.filter (type_is_from l env evd (a_typ, b_typ)) args

(* Premises for LIFT-CONSTR *)
let is_packed_constr l env evd (from_type, to_type) trm =
  let right_type = type_is_from l env evd (from_type, to_type) in
  match kind trm with
  | Construct _  when right_type trm ->
     true
  | App (f, args) ->
     if l.is_fwd then
       isConstruct f && right_type trm
     else
       if equal existT f && right_type trm then
         let last_arg = last (Array.to_list args) in
         isApp last_arg && isConstruct (first_fun last_arg)
       else
         false
  | _ ->
     false

(* Premises for LIFT-PACKED *)
let is_packed l env evd (from_type, to_type) trm =
  let right_type = type_is_from l env evd (from_type, to_type) in
  if l.is_fwd then
    isRel trm && right_type trm
  else
    match kind trm with
    | App (f, args) ->
       equal existT f && right_type trm
    | _ ->
       false

(* Premises for LIFT-PROJ *)
let is_proj l env evd (from_type, to_type) trm =
  let right_type = type_is_from l env evd (from_type, to_type) in
  match kind trm with
  | App _ ->
     let f = first_fun trm in
     let args = unfold_args trm in
     if l.is_fwd then
       equal l.orn.indexer f && right_type (last args)
     else
       (equal projT1 f || equal projT2 f) && right_type (last args)
  | _ ->
     false

(* Premises for LIFT-ELIM *)
let is_eliminator l env evd (from_type, to_type) trm =
  match kind trm with
  | App (f, args) when isConst f ->
     let maybe_ind = inductive_of_elim env (destConst f) in
     if Option.has_some maybe_ind then
       let ind = Option.get maybe_ind in
       equal (mkInd (ind, 0)) (directional l from_type to_type)
     else
       false
  | _ ->
     false

(* --- Configuring the constructor liftings --- *)

(*
 * For packing constructor aguments: Pack, but only if it's to_typ
 *)
let pack_to_typ env evd l (from_typ, to_typ) unpacked =
  if on_type (is_or_applies to_typ) env evd unpacked then
    pack env evd l.off unpacked
  else
    unpacked

(*
 * NORMALIZE (the result of this is cached)
 *)
let lift_constr env evd l (from_typ, to_typ) trm =
  let args = unfold_args (map_backward last_arg l trm) in
  let pack_args = List.map (pack_to_typ env evd l (from_typ, to_typ)) in
  let packed_args = map_backward pack_args l args in
  let rec_args = filter_orn l env evd (from_typ, to_typ) packed_args in
  if List.length rec_args = 0 then
    (* base case - don't bother refolding *)
    reduce_nf env (lift env evd l trm)
  else
    (* inductive case - refold *)
    refold l env evd (lift_to l) (lift env evd l trm) rec_args

(*
 * Wrapper around NORMALIZE
 *)
let initialize_constr_rule env evd l (from_typ, to_typ) constr =
  let (env_c_b, c_body) = zoom_lambda_term env (expand_eta env evd constr) in
  let c_body = reduce_term env_c_b c_body in
  let to_refold = map_backward (pack env_c_b evd l.off) l c_body in
  let refolded = lift_constr env_c_b evd l (from_typ, to_typ) to_refold in
  reconstruct_lambda_n env_c_b refolded (nb_rel env)

(*
 * Run NORMALIZE for all constructors, so we can cache the result
 *)
let initialize_constr_rules env evd l (from_typ, to_typ) =
  let orn_typ = if l.is_fwd then from_typ else to_typ in
  let ((i, i_index), u) = destInd orn_typ in
  let mutind_body = lookup_mind i env in
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = ind_bodies.(i_index) in
  Array.mapi
    (fun c_index _ ->
      let constr = mkConstructU (((i, i_index), c_index + 1), u) in
      initialize_constr_rule env evd l (from_typ, to_typ) constr)
    ind_body.mind_consnames

(* Initialize the lift_config *)
let initialize_lift_config env evd l (from_typ, to_typ) =
  let constr_rules = initialize_constr_rules env evd l (from_typ, to_typ) in
  let cache = initialize_local_cache () in
  { l ; constr_rules ; cache }

(* --- Lifting the induction principle --- *)

(*
 * This implements LIFT-ELIM. The one discrepency here is that,
 * as described in Section 5.2, Coq doesn't have primitive eliminators.
 * Because of this, we can't simply recursively lift the type we eliminate over;
 * we need to get the arguments to the induction principle by hand.
 * This is what the additional LIFT-ELIM-ARGS rule does.
 *)

(*
 * LIFT-ELIM-ARGS
 *)
let lift_elim_args env evd l off args =
  let arg = map_backward last_arg l (last args) in
  let typ_args = non_index_typ_args l.off env evd arg in
  let lifted_arg = mkAppl (lift_to l, snoc arg typ_args) in
  let value_i = List.length args - 1 in
  if l.is_fwd then
    let lifted_arg_sig = on_type dest_sigT env evd lifted_arg in
    let index = project_index lifted_arg_sig lifted_arg in
    let value = project_value lifted_arg_sig lifted_arg in
    insert_index off index (reindex value_i value args)
  else
    remove_index off (reindex value_i lifted_arg args)

(*
 * PROMOTE-MOTIVE and FORGET-MOTIVE
 *)
let lift_motive env evd l off parameterized_elim motive =
  let parameterized_elim_type = reduce_type env evd parameterized_elim in
  let (_, to_motive_typ, _) = destProd parameterized_elim_type in
  let env_to_motive = zoom_env zoom_product_type env to_motive_typ in
  let off2 = offset2 env_to_motive env in (* TODO rename *)
  let motive = shift_by off2 motive in
  let args = mk_n_rels off2 in
  let lifted_arg = pack_lift env_to_motive evd (flip_dir l) (last args) in
  let value_i = off2 - 1 in
  if l.is_fwd then
    (* PROMOTE-MOTIVE *)
    let args = remove_index off (reindex value_i lifted_arg args) in
    let motive_app = reduce_term env_to_motive (mkAppl (motive, args)) in
    reconstruct_lambda_n env_to_motive motive_app (nb_rel env)
  else
    (* FORGET-MOTIVE *)
    let lifted_arg_sig = on_type dest_sigT env_to_motive evd lifted_arg in
    let index = project_index lifted_arg_sig lifted_arg in
    let value = project_value lifted_arg_sig lifted_arg in
    let args = insert_index off index (reindex value_i value args) in
    let motive_app = reduce_term env_to_motive (mkAppl (motive, args)) in
    reconstruct_lambda_n env_to_motive motive_app (nb_rel env)

(* PROMOTE-CASE-ARGS, part of LIFT-CASE-ARGS *)
let promote_case_args env evd l (_, to_typ) args =
  let rec lift_args args index =
    match args with
    | h :: tl ->
       if equal h index then
         (* DROP-INDEX *)
         shift h :: (lift_args (shift_all tl) index)
       else
         let h_typ = reduce_type env evd h in
         if is_or_applies to_typ h_typ then
           (* FORGET-ARG *)
           let h_lifted = pack_lift env evd (flip_dir l) h in
           h_lifted :: lift_args tl (get_arg l.off h_typ)
         else
           (* ARG *)
           h :: lift_args tl index
    | _ -> []
  in lift_args args (mkRel 0)

(* PROMOTE-CASE-ARGS, part of LIFT-CASE-ARGS *)
let forget_case_args env_c_b env evd l (from_typ, _) args =
  let rec lift_args args (index, proj_index) =
    match args with
    | h :: tl ->
       if equal h index then
         (* ADD-INDEX *)
         proj_index :: (lift_args (unshift_all tl) (index, proj_index))
       else
         let h_typ = reduce_type env_c_b evd h in
         if is_or_applies from_typ h_typ then
           (* PROMOTE-ARG *)
           let h_lifted =  pack_lift env evd (flip_dir l) h in
           let h_lifted_typ = on_type dest_sigT env evd h_lifted in
           let proj_value = project_value h_lifted_typ h_lifted in
           let proj_index = project_index h_lifted_typ h_lifted in
           proj_value :: lift_args tl (get_arg l.off h_typ, proj_index)
         else
           (* ARG *)
           h :: lift_args tl (index, proj_index)
    | _ -> []
  in lift_args args (mkRel 0, mkRel 0)

(* LIFT-CASE-ARGS, an auxiliary function for LIFT-CASE *)
let lift_case_args env_c_b env evd l (from_typ, to_typ) args =
  let lifter =
    if l.is_fwd then
      promote_case_args
    else
      forget_case_args env_c_b
  in List.rev (lifter env evd l (from_typ, to_typ) (List.rev args))

(*
 * PROMOTE-CASE and FORGET-CASE
 *)
let lift_case env evd l (from_typ, to_typ) p c_elim c =
  let c_eta = expand_eta env evd c in
  let c_elim_type = reduce_type env evd c_elim in
  let (_, to_c_typ, _) = destProd c_elim_type in
  let nihs = num_ihs env to_typ to_c_typ in
  if nihs = 0 then
    (* CONCL in base case *)
    c (* base case, don't bother *)
  else
    let env_c = zoom_env zoom_product_type env to_c_typ in
    let off2 = offset2 env_c env in (* TODO rename *)
    let c_eta = shift_by off2 c_eta in
    let (env_c_b, c_body) = zoom_lambda_term env_c c_eta in
    let (c_f, c_args) = destApp c_body in
    let split_i = if l.is_fwd then off2 - nihs else off2 + nihs in
    let (c_args, b_args) = take_split split_i (Array.to_list c_args) in
    let c_args = unshift_all_by (List.length b_args) c_args in
    let lift_args = lift_case_args env_c_b env_c evd l (from_typ, to_typ) in
    let c_to_args = lift_args c_args in
    let c_to_f = unshift_by (offset2 env_c_b env_c) c_f in
    let c_to_body = reduce_term env_c (mkAppl (c_to_f, c_to_args)) in
    (* CONCL in inductive case *)
    reconstruct_lambda_n env_c c_to_body (nb_rel env)

(* Lift cases *)
let lift_cases env evd l (from_typ, to_typ) p p_elim cs =
  snd
    (List.fold_left
       (fun (p_elim, cs) c ->
         let c = lift_case env evd l (from_typ, to_typ) p p_elim c in
         let p_elim = mkAppl (p_elim, [c]) in
         (p_elim, snoc c cs))
       (p_elim, [])
       cs)

(*
 * LIFT-ELIM steps before recursing into the rest of the algorithm
 *)
let lift_elim env evd l trm_app =
  let (a_t, b_t, _) = typs_from_orn l env evd in
  let (from_typ, to_typ) = map_backward reverse l (a_t, b_t) in
  let off = l.off - (List.length trm_app.pms) in
  let elim = type_eliminator env (fst (destInd to_typ)) in
  let param_elim = mkAppl (elim, trm_app.pms) in
  let p = lift_motive env evd l off param_elim trm_app.p in
  let p_elim = mkAppl (param_elim, [p]) in
  let cs = lift_cases env evd l (from_typ, to_typ) p p_elim trm_app.cs in
  let final_args = lift_elim_args env evd l off trm_app.final_args in
  apply_eliminator {trm_app with elim; p; cs; final_args}

(* --- Core algorithm --- *)

(*
 * Core lifting algorithm.
 * A few extra rules to deal with real Coq terms as opposed to CIC.
 *)
let lift_core env evd c (a_typ, b_typ) index_type trm =
  let l = c.l in
  let rec lift_rec en ib_typ tr = (* ib_typ recurses to shift *)
    let lifted_opt = search_lifted_term en tr in
    if Option.has_some lifted_opt then
      (* GLOBAL CACHING *)
      Option.get lifted_opt
    else if is_locally_cached c.cache tr then
      (* LOCAL CACHING *)
      lookup_local_cache c.cache tr
    else if is_from l en evd (a_typ, b_typ) tr then
      (* EQUIVALENCE *)
      if l.is_fwd then
        let is = List.map (lift_rec en ib_typ) (unfold_args tr) in
        let app = mkAppl (b_typ, is) in
        let index = mkRel 1 in
        let indexed_is = insert_index l.off index in
        let abs_i = reindex_body (reindex_app indexed_is) in
        let packer = abs_i (mkLambda (Anonymous, ib_typ, shift app)) in
        pack_sigT { index_type = ib_typ; packer }
      else
        let packed = dummy_index en (dest_sigT tr).packer in
        let t_args = remove_index l.off (unfold_args packed) in
        mkAppl (a_typ, t_args)
    else if is_packed_constr l en evd (a_typ, b_typ) tr then
      (* LIFT-CONSTR *)
      (* The extra logic here is an optimization *)
      (* It also deals with the fact that we are lazy about eta *)
      let inner = map_backward last_arg l tr in
      let constr = first_fun inner in
      let args = unfold_args inner in
      let (((_, _), i), _) = destConstruct constr in
      let lifted_constr = c.constr_rules.(i - 1) in
      map_if
        (fun tr' ->
          let lifted_inner = map_forward last_arg l tr' in
          let (f', args') = destApp lifted_inner in
          let args'' = Array.map (lift_rec en ib_typ) args' in
          map_forward
            (fun unpacked ->
              (* pack the lifted term *)
              let ex = dest_existT tr' in
              let index = lift_rec en ib_typ ex.index in
              let packer = lift_rec en ib_typ ex.packer in
              pack_existT { ex with packer; index; unpacked })
            l
            (mkApp (f', args'')))
        (List.length args > 0)
        (reduce_term en (mkAppl (lifted_constr, args)))
    else if is_packed l en evd (a_typ, b_typ) tr then
      (* LIFT-PACK *)
      if l.is_fwd then
        (* repack variables, since projections aren't primitive *)
        let typ = reduce_type en evd tr in
        let lift_typ = dest_sigT (lift_rec en ib_typ typ) in
        let index = project_index lift_typ tr in
        let unpacked = project_value lift_typ tr in
        let packer = lift_typ.packer in
        pack_existT { index_type = ib_typ; packer; index; unpacked }
      else
        lift_rec en index_type (dest_existT tr).unpacked
    else if is_proj l en evd (a_typ, b_typ) tr then
      (* COHERENCE *)
      let arg = last_arg tr in
      let arg' = lift_rec en index_type arg in
      if l.is_fwd then
        let arg_typ' = dest_sigT (lift_rec en index_type (reduce_type en evd arg)) in
        project_index arg_typ' arg'
      else if equal projT1 (first_fun tr) then
        mkAppl (l.orn.indexer, snoc arg' (non_index_typ_args l.off en evd arg))
      else
        arg'
    else if is_eliminator l en evd (a_typ, b_typ) tr then
      (* LIFT-ELIM *)
      let tr_elim = deconstruct_eliminator en evd tr in
      let npms = List.length tr_elim.pms in
      let value_i = arity (expand_eta env evd a_typ) - npms in
      let (final_args, post_args) = take_split (value_i + 1) tr_elim.final_args in
      let tr' = lift_elim en evd l { tr_elim with final_args } in
      let tr'' = lift_rec en index_type tr' in
      let post_args' = List.map (lift_rec en index_type) post_args in
      mkAppl (tr'', post_args')
    else
      match kind tr with
      | App (f, args) ->
         if equal (lift_back l) f then
           (* SECTION-RETRACTION *)
           last_arg tr
         else if equal (lift_to l) f then
           (* INTERNALIZE *)
           lift_rec en index_type (last_arg tr)
         else
           (* APP *)
           let args' = List.map (lift_rec en index_type) (Array.to_list args) in
           let arg' = last args' in
           if (is_or_applies projT1 tr || is_or_applies projT2 tr) && is_or_applies existT arg' then
             (* optimize projections of existentials, which are common *)
             let ex' = dest_existT arg' in
             if equal projT1 f then
               ex'.index
             else
               ex'.unpacked
           else
             let f' = lift_rec en index_type f in
             mkAppl (f', args')
      | Cast (ca, k, t) ->
         (* CAST *)
         let ca' = lift_rec en index_type ca in
         let t' = lift_rec en index_type t in
         mkCast (ca', k, t')
      | Prod (n, t, b) ->
         (* PROD *)
         let t' = lift_rec en index_type t in
         let en_b = push_local (n, t) en in
         let b' = lift_rec en_b (shift index_type) b in
         mkProd (n, t', b')
      | Lambda (n, t, b) ->
         (* LAMBDA *)
         let t' = lift_rec en index_type t in
         let en_b = push_local (n, t) en in
         let b' = lift_rec en_b (shift index_type) b in
         mkLambda (n, t', b')
      | LetIn (n, trm, typ, e) ->
         (* LETIN *)
         let trm' = lift_rec en index_type trm in
         let typ' = lift_rec en index_type typ in
         let en_e = push_let_in (n, trm, typ) en in
         let e' = lift_rec en_e (shift index_type) e in
         mkLetIn (n, trm', typ', e')
      | Case (ci, ct, m, bs) ->
         (* CASE *)
         let ct' = lift_rec en index_type ct in
         let m' = lift_rec en index_type m in
         let bs' = Array.map (lift_rec en index_type) bs in
         mkCase (ci, ct', m', bs')
      | Fix ((is, i), (ns, ts, ds)) ->
         (* FIX *)
         let ts' = Array.map (lift_rec en index_type) ts in
         let ds' = Array.map (map_rec_env_fix lift_rec shift en index_type ns ts) ds in
         mkFix ((is, i), (ns, ts', ds'))
      | CoFix (i, (ns, ts, ds)) ->
         (* COFIX *)
         let ts' = Array.map (lift_rec en index_type) ts in
         let ds' = Array.map (map_rec_env_fix lift_rec shift en index_type ns ts) ds in
         mkCoFix (i, (ns, ts', ds'))
      | Proj (pr, co) ->
         (* PROJ *)
         let co' = lift_rec en index_type co in
         mkProj (pr, co')
      | Construct (((i, i_index), _), u) ->
         let ind = mkInd (i, i_index) in
         if equal ind (directional l a_typ b_typ) then
           (* lazy eta expansion *)
           lift_rec en index_type (expand_eta en evd tr)
         else
           tr
      | Const (co, u) ->
         let lifted =
           (try
              (* CONST *)
              let def = lookup_definition en tr in
              let try_lifted = lift_rec en index_type def in
              if equal def try_lifted then
                tr
              else
                reduce_term en try_lifted
            with _ ->
              (* AXIOM *)
              tr)
         in cache_local c.cache tr lifted; lifted
      | _ ->
         tr
  in lift_rec env index_type trm

(*
 * Run the core lifting algorithm on a term
 *)
let do_lift_term env evd (l : lifting) trm =
  let (a_t, b_t, i_b_t) = typs_from_orn l env evd in
  let c = initialize_lift_config env evd l (a_t, b_t) in
  lift_core env evd c (a_t, b_t) i_b_t trm

(*
 * Run the core lifting algorithm on a definition
 *)
let do_lift_defn env evd (l : lifting) def =
  let trm = unwrap_definition env def in
  do_lift_term env evd l trm

(************************************************************************)
(*                           Inductive types                            *)
(************************************************************************)

(*
 * TODO clean, move all of these side effects out... they should not be here
 *)
let define_lifted_eliminator ?(suffix="_sigT") ind0 ind sort =
  let env = Global.env () in
  let ident =
    let ind_name = (Inductive.lookup_mind_specif env ind |> snd).mind_typename in
    let raw_ident = Indrec.make_elimination_ident ind_name sort in
    Nameops.add_suffix raw_ident suffix
  in
  let elim0 = Indrec.lookup_eliminator ind0 sort in
  let elim = Indrec.lookup_eliminator ind sort in
  let env, term = open_constant env (Globnames.destConstRef elim) in
  let expr = Eta.eta_extern env (Evd.from_env env) Id.Set.empty term in
  ComDefinition.do_definition
    ~program_mode:false ident (Decl_kinds.Global, false, Decl_kinds.Scheme)
    None [] None expr None (Lemmas.mk_hook (fun _ -> declare_lifted elim0))

let declare_inductive_liftings ind ind' ncons =
  declare_lifted (Globnames.IndRef ind) (Globnames.IndRef ind');
  List.iter2
    declare_lifted
    (List.init ncons (fun i -> Globnames.ConstructRef (ind, i + 1)))
    (List.init ncons (fun i -> Globnames.ConstructRef (ind', i + 1)))

(*
 * Lift the inductive type using sigma-packing.
 *
 * This algorithm assumes that type parameters are left constant and will lift
 * every binding and every term of the base type to the sigma-packed ornamented
 * type. (IND and CONSTR via caching)
 *)
let do_lift_ind env evm typename suffix lift ind =
  let (mind_body, ind_body) as mind_specif = Inductive.lookup_mind_specif env ind in
  check_inductive_supported mind_body;
  let env, univs, arity, constypes = open_inductive ~global:true env mind_specif in
  let evm = Evd.update_sigma_env evm env in
  let nparam = mind_body.mind_nparams_rec in
  let arity' = do_lift_term env evm lift arity in
  let constypes' = List.map (do_lift_term env evm lift) constypes in
  let consnames =
    Array.map_to_list (fun id -> Nameops.add_suffix id suffix) ind_body.mind_consnames
  in
  let is_template = is_ind_body_template ind_body in
  let ind' =
    declare_inductive typename consnames is_template univs nparam arity' constypes'
  in
  List.iter (define_lifted_eliminator ind ind') [Sorts.InType; Sorts.InProp];
  declare_inductive_liftings ind ind' (List.length constypes);
  ind'
