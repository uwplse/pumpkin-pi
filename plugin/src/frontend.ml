open Constr
open Names
open Globnames
open Coqterms
open Lifting
open Caching
open Search
open Lift
open Desugar
open Unpack
open Utilities
open Pp
open Printer
open Ltac_plugin
open Zooming (* TODO remove when you move coh functionality *)
open Indexing (* TODO same *)
open Environ (* TODO same *)
open Hypotheses (* TODO same *)
open Printing (* TODO same *)
open Debruijn (* TODO same *)
open Hofs (* TODO same *)
open Factoring (* TODO same *)
open Specialization (* TODO same *)
       
(* --- Options --- *)

(*
 * Prove the coherence property of the algebraic promotion isomorphism
 *)
let opt_search_coh = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate a proof of coherence in search for DEVOID";
  Goptions.optkey = ["DEVOID"; "search"; "prove"; "coherence"];
  Goptions.optread = (fun () -> !opt_search_coh);
  Goptions.optwrite = (fun b -> opt_search_coh := b);
}

let is_search_coh () = !opt_search_coh

(*
 * Prove section and retraction
 *)
let opt_search_equiv = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate proof of equivalence in search for DEVOID";
  Goptions.optkey = ["DEVOID"; "search"; "prove"; "equivalence"];
  Goptions.optread = (fun () -> !opt_search_equiv);
  Goptions.optwrite = (fun b -> opt_search_equiv := b);
}

let is_search_equiv () = !opt_search_equiv

(* --- Commands --- *)

(* TODO refactor below, comment, fill in *)
(* TODO test on other types besides list/vect in file *)
let prove_coherence env evd orn =
  let env_coh = zoom_env zoom_lambda_term env orn.promote in
  let a = mkRel 1 in
  let is = on_type unfold_args env_coh evd a in
  let b_sig = mkAppl (orn.promote, snoc a is) in
  let b_sig_typ = reduce_type env_coh evd b_sig in
  let ib = mkAppl (orn.indexer, snoc a is) in
  let ib_typ = reduce_type env_coh evd ib in
  let packer = (dest_sigT b_sig_typ).packer in
  let proj_ib = project_index { index_type = ib_typ; packer} b_sig in
  let coh = reconstruct_lambda env_coh (mkAppl (eq_refl, [ib_typ; proj_ib])) in
  let coh_typ = reconstruct_product env_coh (mkAppl (eq, [ib_typ; ib; proj_ib])) in
  (coh, coh_typ)

(*
 * TODO move, explain, refactor common w/ refolding in search/lifting
 * mention c_body is the reduced body of a constructor, and env_c_b is the env
 *)
let get_rec_args typ env_c_b evd c_body =
  List.filter (on_type (is_or_applies typ) env_c_b evd) (unfold_args c_body)

(*
 * TODO move, explain
 *)
let eq_lemmas_env env evd recs l =
  fst
    (List.fold_left
       (fun (e, nargs) r ->
         let r1 = shift_by nargs r in (* original rec arg *)
         let r_t = reduce_type e evd r1 in (* rec arg type *)
         if l.is_fwd then (* TODO consolidate whatever is opossible *)
           let e_r = push_local (Anonymous, r_t) e in (* push new rec arg *)
           let r1 = shift r1 in (* shifted original rec arg *)
           let r2 = mkRel 1 in (* new rec arg *)
           let r_t  = shift r_t in (* new rec arg type *)
           let r_eq = apply_eq {at_type = r_t; trm1 = r1; trm2 = r2} in
           (push_local (Anonymous, r_eq) e_r, nargs + 2)
         else
           let ib = get_arg l.off r_t in (* rec arg index *)
           let ib_t = reduce_type e evd ib in (* rec arg index type *)
           let e_ib = push_local (Anonymous, ib_t) e in (* push new index *)
           let ib2 = mkRel 1 in (* new index *)
           let r2_t = reindex_app (reindex l.off ib2) (shift r_t) in (* new rec arg type *)
           let e_r = push_local (Anonymous, r2_t) e_ib in (* push new rec arg *)
           let r1_p = pack e_r evd l.off (shift_by 2 r1) in (* packed rec arg *)
           let r2_p = pack e_r evd l.off (mkRel 1) in (* packed new rec arg *)
           let r_p_t = reduce_type e_r evd r1_p in (* packed rec arg type *)
           let r_eq = apply_eq {at_type = r_p_t; trm1 = r1_p; trm2 = r2_p} in
           (push_local (Anonymous, r_eq) e_r, nargs + 3))
       (env, 0)
       recs)
  
(*
 * TODO move, explain
 *)
let eq_lemmas env evd typ l =
  (* TODO retraction direction: pack *)
  let ((i, i_index), u) = destInd typ in
  Array.mapi
    (fun c_index _ ->
      let c = mkConstructU (((i, i_index), c_index + 1), u) in
      let (env_c_b, c_body) = zoom_lambda_term env (expand_eta env evd c) in
      let c_body = reduce_term env_c_b c_body in
      let recs = get_rec_args typ env_c_b evd c_body in
      let env_lemma = eq_lemmas_env env_c_b evd recs l in
      let nargs = new_rels2 env_lemma env_c_b in
      let c_body = map_backward (pack env_lemma evd l.off) l (shift_by nargs c_body) in
      let c_body_type = reduce_type env_lemma evd c_body in
      let refl = apply_eq_refl { typ = c_body_type; trm = c_body } in
      let (body, _, _) =
        List.fold_right
          (fun _ (b, h_eq, c_app) ->
            let h_eq_r = destRel h_eq in
            let (_, _, h_eq_t) = CRD.to_tuple @@ lookup_rel h_eq_r env_lemma in
            let app = dest_eq (shift_by h_eq_r h_eq_t) in
            let at_type = app.at_type in
            let r1 = app.trm1 in
            let r2 = app.trm2 in
            if l.is_fwd then (* TODO consolidate *)
              let abs_c_app = all_eq_substs (shift r1, mkRel 1) (shift c_app) in
              let c_body_b = shift c_body in
              let typ_b = shift c_body_type in
              let p_b = { at_type = typ_b; trm1 = c_body_b; trm2 = abs_c_app } in
              let p = mkLambda (Anonymous, at_type, apply_eq p_b) in
              let c_app_trans = all_eq_substs (r1, r2) c_app in
              let eq_proof_app = {at_type; p; trm1 = r1; trm2 = r2; h = h_eq; b} in
              let eq_proof = apply_eq_ind eq_proof_app in
              (eq_proof, shift_by 2 h_eq, c_app_trans)
            else
              let r1_ex = dest_existT r1 in
              let r2_ex = dest_existT r2 in
              let r1_u = r1_ex.unpacked in
              let r2_u = r2_ex.unpacked in
              let r1_ib = r1_ex.index in
              let r2_ib = r2_ex.index in
              let b_sig_typ = dest_sigT (shift at_type) in
              let ib = project_index b_sig_typ (mkRel 1) in
              let bv = project_value b_sig_typ (mkRel 1) in
              let abs_c_app = all_eq_substs (shift r1_ib, ib) (all_eq_substs (shift r1_u, bv) (shift c_app)) in
              let c_body_b = shift c_body in
              let typ_b = shift c_body_type in
              let p_b = { at_type = typ_b; trm1 = c_body_b; trm2 = abs_c_app } in
              let p = mkLambda (Anonymous, at_type, apply_eq p_b) in
              let c_app_trans = all_eq_substs (r1_ib, r2_ib) (all_eq_substs (r1_u, r2_u) c_app) in
              let eq_proof_app = {at_type; p; trm1 = r1; trm2 = r2; h = h_eq; b} in
              let eq_proof = apply_eq_ind eq_proof_app in
              (eq_proof, shift_by 3 h_eq, c_app_trans)
          )
          recs
          (refl, mkRel 1, c_body)
      in reconstruct_lambda env_lemma body)
    ((lookup_mind i env).mind_packets.(i_index)).mind_consnames
    
(* TODO move out shifting? why there *)
(* TODO refactor packing w/ pack in specialization, or w/ lift pack *)
(* TODO refactor, clean, etc *)
(* TODO remove at_type or pass different arg for this *)
let retraction_motive env evd b at_type promote forget npm l =
  let b_typ = reduce_type env evd b in (* TODO redundant *)
  let b_sig = dest_sigT b_typ in (* TOOD redundant *)
  let i_b_t = b_sig.index_type in
  let env_i_b = push_local (Anonymous, i_b_t) (pop_rel_context 1 env) in
  debug_env env_i_b "env_i_b";
  let b_u = reduce_term env_i_b (mkAppl (b_sig.packer, [mkRel 1])) in
  debug_term env_i_b b_u "b_u";
  let env_u = push_local (Anonymous, b_u) env_i_b in
  let typ_args = remove_index l.off (unfold_args at_type) in (* TODO refactor this stuff, common w lift config *)
  let b_ex = pack env_u evd l.off b in
  let b_ex' = mkAppl (promote, snoc (mkAppl (forget, snoc b_ex typ_args)) typ_args) in
  let p_b = apply_eq { at_type = shift b_typ; trm1 = b_ex; trm2 = b_ex' } in
  shift_by (new_rels env npm) (reconstruct_lambda_n env_u p_b npm)

(* TODO move out shifting? why there *)
(* TODO refactor, clean, etc *)
(* TODO is a just always mkRel 1? *)
let section_motive env evd a at_type promote forget npm =
  let typ_args = unfold_args at_type in
  let a' = mkAppl (forget, snoc (mkAppl (promote, snoc a typ_args)) typ_args) in
  let p_b = apply_eq { at_type; trm1 = a; trm2 = a' } in
  shift_by (new_rels env npm) (reconstruct_lambda_n env p_b npm)

(* TODO refactor, clean, etc *)
let retraction_case env evd pms p eq_lemma c =
  let rec case e pms p_rel p args lemma_args c =
    match kind c with
      | App (_, _) ->
         (* conclusion: apply eq lemma and beta-reduce *)
         let all_args = List.append (List.rev args) (List.rev lemma_args) in
         debug_terms e pms "pms";
         debug_terms e all_args "all_args";
         reduce_term e (mkAppl (eq_lemma, List.append pms all_args))
      | Prod (n, t, b) ->
         let case_b = case (push_local (n, t) e) (shift_all pms) (shift p_rel) (shift p) in
         if applies p_rel t then
           (* IH *)
           let t' = reduce_term e (mkAppl (p, unfold_args t)) in
           debug_term e t "t";
           debug_term e t' "t'";
           let app = dest_eq t' in
           let b' = app.trm2 in
           debug_term e b' "b'";
           let b_sig_t' = dest_sigT (reduce_type e evd b') in
           let ib' = project_index b_sig_t' b' in
           debug_term e ib' "ib'";
           let bv' = project_value b_sig_t' b' in
           debug_term e bv' "bv'";
           let lemma_args_b = mkRel 1 :: shift_all (bv' :: ib' :: lemma_args) in
           mkLambda (n, t', case_b (shift_all args) lemma_args_b b)
         else
           (* Product *)
           let args_b = mkRel 1 :: shift_all args in
           mkLambda (n, t, case_b args_b (shift_all lemma_args) b)
      | _ ->
         failwith "unexpected case"
    in case env pms (mkRel 1) p [] [] c
           
(* TODO refactor, clean, etc *)
let section_case env pms p eq_lemma c =
  let rec case e pms p_rel p args lemma_args c =
    match kind c with
      | App (_, _) ->
         (* conclusion: apply eq lemma and beta-reduce *)
         let all_args = List.append (List.rev args) (List.rev lemma_args) in
         reduce_term e (mkAppl (eq_lemma, List.append pms all_args))
      | Prod (n, t, b) ->
         let case_b = case (push_local (n, t) e) (shift_all pms) (shift p_rel) (shift p) in
         if applies p_rel t then
           (* IH *)
           let t' = reduce_term e (mkAppl (p, unfold_args t)) in
           let app = dest_eq t' in
           let a' = app.trm2 in
           let lemma_args_b = mkRel 1 :: shift_all (a' :: lemma_args) in
           mkLambda (n, t', case_b (shift_all args) lemma_args_b b)
         else
           (* Product *)
           let args_b = mkRel 1 :: shift_all args in
           mkLambda (n, t, case_b args_b (shift_all lemma_args) b)
      | _ ->
         failwith "unexpected case"
    in case env pms (mkRel 1) p [] [] c

(* TODO refactor below, comment, fill in *)
(* TODO clean up too *)
(* TODO test on other types besides list/vect in file *)
let prove_section promote_n forget_n env evd l =
  let env_sec = zoom_env zoom_lambda_term env l.orn.promote in
  let a = mkRel 1 in
  let at_type = reduce_type env_sec evd a in
  let a_typ = first_fun at_type in
  let ((i, i_index), u) = destInd a_typ in
  let mutind_body = lookup_mind i env in
  let elim = type_eliminator env_sec (i, i_index) in
  let npm = mutind_body.mind_nparams in
  let nargs = new_rels env_sec npm in
  let p = section_motive env_sec evd a at_type (make_constant promote_n) (make_constant forget_n) npm in
  let (env_pms, elim_typ) = zoom_n_prod env npm (infer_type env evd elim) in
  let (n, p_t, b) = destProd elim_typ in
  let env_p = push_local (n, p_t) env_pms in
  let pms = shift_all (mk_n_rels npm) in (* TODO why shift *)
  let lemmas = eq_lemmas env evd a_typ l in
  let cs = List.mapi (fun j c -> section_case env_p pms (unshift_by (nargs - 1) p) lemmas.(j) c) (take_except nargs (factor_product b)) in
  let app =
       apply_eliminator
         {
           elim;
           pms = shift_all_by (nargs - 1) pms; (* TODO why *)
           p;
           cs = shift_all_by (nargs - 1) cs;
           final_args = mk_n_rels nargs;
         }
  in
  let eq_typ = dest_eq (reduce_type env_sec evd app) in
  let t1 = eq_typ.trm1 in
  let t2 = eq_typ.trm2 in
  reconstruct_lambda env_sec (mkAppl (eq_sym, [at_type; t1; t2; app]))

(* TODO refactor common w/ section, or call lift *)
(* TODO refactor below, comment, fill in *)
(* TODO clean up too *)
(* TODO test on other types besides list/vect in file *)
let prove_retraction promote_n forget_n env evd l =
  (* TODO should be env_retract *)
  let env_sec = zoom_env zoom_lambda_term env l.orn.forget in
  let b = mkRel 1 in
  let at_type_packed = reduce_type env_sec evd b in
  let at_type = snd (zoom_lambda_term env_sec (last_arg at_type_packed)) in
  let b_typ = first_fun at_type in
  let ((i, i_index), u) = destInd b_typ in
  let mutind_body = lookup_mind i env in
  let elim = type_eliminator env_sec (i, i_index) in
  let npm = mutind_body.mind_nparams in
  let nargs = new_rels env_sec npm in
  let p = retraction_motive env_sec evd b at_type (make_constant promote_n) (make_constant forget_n) npm l in
  let (env_pms, elim_typ) = zoom_n_prod env npm (infer_type env evd elim) in
  let (n, p_t, b) = destProd elim_typ in
  let env_p = push_local (n, p_t) env_pms in
  let pms = shift_all (mk_n_rels npm) in (* TODO why shift *)
  let lemmas = eq_lemmas env evd b_typ l in
  debug_term env_sec p "p";
  debug_env env_sec "env_sec";
  debug_term env_p (unshift_by (nargs - 1) p) "p unshifted in env_p";
  debug_env env_p "env_p";
  let cs = List.mapi (fun j c -> retraction_case env_p evd pms (unshift_by (nargs - 1) p) lemmas.(j) c) (take_except (nargs + 1) (factor_product b)) in
  debug_terms env_sec cs "cs";
  let args = mk_n_rels nargs in
  let b_sig = last args in
  let b_sig_typ = on_type dest_sigT env_sec evd b_sig in
  let i_b = project_index b_sig_typ b_sig in
  let b = project_value b_sig_typ b_sig in
  let final_args = insert_index (l.off - npm) i_b (reindex (nargs - 1) b args) in
  let app =
       apply_eliminator
         {
           elim;
           pms = shift_all_by (nargs - 1) pms; (* TODO why *)
           p;
           cs = shift_all_by (nargs - 1) cs;
           final_args;
         }
  in (* TODO use eta_sigT where relevant *)
  let eq_typ = dest_eq (reduce_type env_sec evd app) in
  let t1 = eq_typ.trm1 in
  let t2 = eq_typ.trm2 in
  let at_type = reduce_type env_sec evd t1 in (* TODO why can't just reuse *)
  let sym_app = mkAppl (eq_sym, [at_type; t1; t2; app]) in
  let to_elim = dest_sigT at_type in
  let t1_ex = dest_existT t1 in
  let trm2 = last_arg (t1_ex.unpacked) in
  let trm1 = all_eq_substs (t1, trm2) t2 in
  (* TODO why all the shifting here *)
  let packed_type = shift (reconstruct_lambda_n env_sec (apply_eq {at_type; trm1; trm2}) (nb_rel env_sec - 1)) in
  let ib_typ = (dest_sigT (shift at_type)).index_type in
  let b_typ = mkAppl ((dest_sigT (shift at_type)).packer, [mkRel 1]) in
  let sym_app_b = all_eq_substs (shift_by 2 i_b, mkRel 2) (all_eq_substs (shift_by 2 b, mkRel 1) (shift_by 2 sym_app)) in
  let unpacked = mkLambda (Anonymous, ib_typ, (mkLambda (Anonymous, b_typ, sym_app_b))) in (* TODO build by env instead *)
  let arg = mkRel 1 in
  let elim_app = elim_sigT { to_elim; packed_type; unpacked; arg } in
  reconstruct_lambda env_sec elim_app
                        
(*
 * Identify an algebraic ornament between two types
 * Define the components of the corresponding equivalence
 * (Don't prove section and retraction)
 *)
let find_ornament n_o d_old d_new =
  let (evd, env) = Pfedit.get_current_context () in
  let trm_o = unwrap_definition env (intern env evd d_old) in
  let trm_n = unwrap_definition env (intern env evd d_new) in
  match map_tuple kind (trm_o, trm_n) with
  | Ind ((m_o, _), _), Ind ((m_n, _), _) ->
    let (_, _, lab_o) = KerName.repr (MutInd.canonical m_o) in
    let (_, _, lab_n) = KerName.repr (MutInd.canonical m_n) in
    let name_o = Label.to_id lab_o in
    let name_n = Label.to_string lab_n in
    let auto_n = with_suffix (with_suffix name_o "to") name_n in
    let n = Option.default auto_n n_o in
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env evd idx_n trm_o trm_n in
    ignore (define_term idx_n evd orn.indexer true);
    (* TODO move all of these into msg_notice *)
    Printf.printf "Defined indexer %s\n\n" (Id.to_string idx_n);
    let promote = define_term n evd orn.promote true in
    Printf.printf "Defined promotion %s\n\n" (Id.to_string n);
    let inv_n = with_suffix n "inv" in
    let forget = define_term inv_n evd orn.forget true in
    Printf.printf "Defined forgetful function %s\n\n" (Id.to_string inv_n);
    (if is_search_coh () then (* TODO move these out, too *)
       let env = Global.env () in
       let coh, coh_typ = prove_coherence env evd orn in
       let coh_n = with_suffix n "coh" in
       let _ = define_term ~typ:coh_typ coh_n evd coh true in
       Printf.printf "Defined coherence proof %s\n\n" (Id.to_string coh_n)
     else
       ());
    (if is_search_equiv () then
       let env = Global.env () in
       let l = initialize_lifting env evd orn.promote orn.forget in
       (* TODO can we use promote/forget above instead of names? *)
       let section = prove_section n inv_n env evd l in
       let sec_n = with_suffix n "section" in
       let _ = define_term sec_n evd section true in
       Printf.printf "Defined section proof %s\n\n" (Id.to_string sec_n);
       let retraction = prove_retraction n inv_n env evd (flip_dir l) in
       let rec_n = with_suffix n "retraction" in
       let _ = define_term rec_n evd retraction true in
       Printf.printf "Defined retraction proof %s\n\n" (Id.to_string rec_n)
     else
       ());
    (try
       save_ornament (trm_o, trm_n) (promote, forget)
     with _ ->
       Printf.printf "WARNING: Failed to cache ornamental promotion.")
  |_ ->
    failwith "Only inductive types are supported"

(*
 * Lift a definition according to a lifting configuration, defining the lifted
 * definition and declaring it as a lifting of the original definition.
 *)
let lift_definition_by_ornament env evd n l c_old =
  let lifted = do_lift_defn env evd l c_old in
  ignore (define_term n evd lifted true);
  try
    let old_gref = global_of_constr c_old in
    let new_gref = ConstRef (Lib.make_kn n |> Constant.make1) in
    declare_lifted old_gref new_gref;
  with _ ->
    Printf.printf "WARNING: Failed to cache lifting."

(*
 * Lift an inductive type according to a lifting configuration, defining the
 * new lifted version and declaring type-to-type, constructor-to-constructor,
 * and eliminator-to-eliminator liftings.
 *)
let lift_inductive_by_ornament env evm n s l c_old =
  let ind, _ = destInd c_old in
  let ind' = do_lift_ind env evm n s l ind in
  let env' = Global.env () in
  Feedback.msg_notice (str "Defined lifted inductive type " ++ pr_inductive env' ind')

(*
 * Lift the supplied definition or inductive type along the supplied ornament
 * Define the lifted version
 *)
let lift_by_ornament ?(suffix=false) n d_orn d_orn_inv d_old =
  let (evd, env) = Pfedit.get_current_context () in
  let c_orn = intern env evd d_orn in
  let c_orn_inv = intern env evd d_orn_inv in
  let c_old = intern env evd d_old in
  let n_new = if suffix then suffix_term_name c_old n else n in
  let s = if suffix then Id.to_string n else "_" ^ Id.to_string n in
  let us = map_tuple (unwrap_definition env) (c_orn, c_orn_inv) in
  let are_inds = isInd (fst us) && isInd (snd us) in
  let lookup os = map_tuple Universes.constr_of_global (lookup_ornament os) in
  let (c_from, c_to) = if are_inds then lookup us else (c_orn, c_orn_inv) in
  let l = initialize_lifting env evd c_from c_to in
  let u_old = unwrap_definition env c_old in
  if isInd u_old then
    let from_typ = fst (on_type ind_of_promotion_type env evd l.orn.promote) in
    if not (equal u_old from_typ) then
      lift_inductive_by_ornament env evd n_new s l c_old
    else
      lift_definition_by_ornament env evd n_new l c_old
  else
    lift_definition_by_ornament env evd n_new l c_old

(*
 * Translate each fix or match subterm into an equivalent application of an
 * eliminator, defining the new term with the given name.
 *
 * Mutual fix or cofix subterms are not supported.
 *)
let do_desugar_constant ident const_ref =
  ignore
    begin
      qualid_of_reference const_ref |> Nametab.locate_constant |>
      Global.lookup_constant |> transform_constant ident desugar_constr
    end

(*
 * Translate fix and match expressions into eliminations, as in
 * do_desugar_constant, compositionally throughout a whole module.
 *
 * The optional argument is a list of constants outside the module to include
 * in the translated module as if they were components in the input module.
 *)
let do_desugar_module ?(incl=[]) ident mod_ref =
  let open Util in
  let consts = List.map (qualid_of_reference %> Nametab.locate_constant) incl in
  let include_constant subst const =
    let ident = Label.to_id (Constant.label const) in
    let tr_constr env evm = subst_globals subst %> desugar_constr env evm in
    let const' =
      Global.lookup_constant const |> transform_constant ident tr_constr
    in
    Globmap.add (ConstRef const) (ConstRef const') subst
  in
  let init () = List.fold_left include_constant Globmap.empty consts in
  ignore
    begin
      qualid_of_reference mod_ref |> Nametab.locate_module |>
      Global.lookup_module |> transform_module_structure ~init ident desugar_constr
    end

(*
 * Unpack sigma types in the functional signature of a constant.
 *
 * This transformation assumes that the input constant was generated by
 * ornamental lifting.
 *)
let do_unpack_constant ident const_ref =
  let env = Global.env () in
  let evm = ref (Evd.from_env env) in
  let term =
    qualid_of_reference const_ref |> Nametab.locate_constant |>
    unpack_constant env evm
  in
  ignore (define_term ident !evm term true)
