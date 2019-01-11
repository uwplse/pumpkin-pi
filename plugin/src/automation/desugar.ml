open Util
open Names
open Univ
open Context
open Term
open Constr
open Inductiveops
open CErrors
open Coqterms

let smash_prod_assum ctxt body =
  Rel.fold_inside
    (fun body decl ->
       match rel_value decl with
       | Some defn -> Vars.subst1 defn body
       | None -> mkProd (rel_name decl, rel_type decl, body))
    ~init:body
    ctxt

let smash_lam_assum ctxt body =
  Rel.fold_inside
    (fun body decl ->
       match rel_value decl with
       | Some defn -> Vars.subst1 defn body
       | None -> mkLambda (rel_name decl, rel_type decl, body))
    ~init:body
    ctxt

let contract_prod_assum term =
  let ctxt, body = decompose_prod_assum term in
  smash_prod_assum ctxt body

let contract_lam_assum term =
  let ctxt, body = decompose_lam_assum term in
  smash_lam_assum ctxt body

let define_rel_decl body decl =
  assert (is_rel_assum decl);
  rel_defin (rel_name decl, body, rel_type decl)

let decompose_ind ind_type =
  let pind, args = decompose_app ind_type |> on_fst destInd in
  let nparam = inductive_nparams (out_punivs pind) in
  let params, indices = List.chop nparam args in
  pind, params, indices

(* Drop the nth lambda binding, skipping over any let bindings *)
let drop_lam n term =
  (* TODO: Combine with function-izing type *)
  let (decl :: ctxt), body = decompose_lam_n_assum n term in
  assert (Vars.noccurn 1 body);
  recompose_lam_assum ctxt (Vars.lift (-1) body)

let freshen_name idset name =
  let name' = Namegen.next_name_away name !idset in
  idset := Id.Set.add name' !idset;
  name'

let split_functional env ind_fam body =
  let split_case cons_sum =
    let cons = build_dependent_constructor cons_sum in
    let env = Environ.push_rel_context cons_sum.cs_args env in
    let body = Vars.lift cons_sum.cs_nargs body in
    let args = Array.append cons_sum.cs_concl_realargs [|cons|] in
    (* NOTE: May want to avoid eager zeta reduction *)
    let case = reduce_term env (mkApp (body, args)) in
    cons_sum.cs_nargs, recompose_lam_assum cons_sum.cs_args case
  in
  Array.map split_case (get_constructors env ind_fam)

let premise_of_case env ind_fam motive (narg, term) =
  let beta = Reduction.beta_appvect in
  let open_lam_assum = decompose_lam_n_decls 1 %> on_fst List.hd in
  let fix_name = Environ.lookup_rel 1 env |> rel_name in
  let ind_head = dest_ind_family ind_fam |> on_fst mkIndU |> applist in
  let idset = ref (Id.Set.union (free_vars env term) (bound_vars term)) in
  let fixpoint_to_recurrence (ctxt, term) =
    let arg_decl, term = open_lam_assum term in
    let arg_type = Vars.lift 1 (rel_type arg_decl) in
    let ctxt = Rel.add arg_decl ctxt in
    let nbound = Rel.length ctxt in
    match eq_constr_head (Vars.lift nbound ind_head) arg_type with
    | Some indices ->
      let fix_args = Array.append indices [|mkRel 1|] in
      let fix_call = mkApp (mkRel (nbound + 1), fix_args) in
      let rec_name = freshen_name idset fix_name in
      let rec_type = beta (Vars.lift nbound motive) fix_args in
      let rec_decl = rel_assum (Name rec_name, rec_type) in
      Rel.add rec_decl ctxt, abstract_subterm fix_call term
    | None ->
      ctxt, term
  in
  let ctxt, body = iterate fixpoint_to_recurrence narg (Rel.empty, term) in
  let premise = recompose_lam_assum ctxt body in
  assert (Vars.noccurn 1 premise);
  premise

(* Assumes that the fixed-point has already been regularized *)
let eliminate_fixpoint env evm ind_fam ind_sort fun_type fun_term =
  (* TODO: Take the quantifier context separately (or just build here...) *)
  let (ind, _), params = dest_ind_family ind_fam |> on_snd Array.of_list in
  let sort = e_infer_sort env evm fun_type in
  let is_prop = Sorts.family_equal ind_sort Sorts.InProp in
  let nindex = inductive_nrealargs ind in
  let elim = Indrec.lookup_eliminator ind sort in
  let cases = split_functional env ind_fam fun_term in
  let motive = if is_prop then drop_lam (nindex + 1) fun_type else fun_type in
  let minors = Array.map (premise_of_case env ind_fam motive) cases in
  let premises = Array.cons motive minors in
  mkApp (e_new_global evm elim, Array.append params premises) |> Vars.lift (-1)

(* Convenient wrapper around eliminate_fixpoint *)
let eliminate_match env evm info pred discr cases =
  (* TODO: Should not need to pass though fixpoint translation *)
  let pind, (params, indices) =
    e_infer_type env evm discr |> Inductive.find_inductive env |>
    on_snd (List.chop info.ci_npar)
  in
  let ind_fam = make_ind_family (pind, params) in
  let ind_sort = get_arity env ind_fam |> snd in
  let nindex = List.length indices in
  let ctxt, fun_type = decompose_lam_n_assum (nindex + 1) pred in
  let fun_body =
    let lift = Vars.lift (nindex + 2) in
    mkCase (info, lift pred, mkRel 1, Array.map lift cases)
  in
  let fun_type = smash_lam_assum ctxt fun_type |> Vars.lift 1 in
  let fun_term = smash_lam_assum ctxt fun_body |> Vars.lift 1 in
  let fix_env = Environ.push_rel (rel_assum (Name.Anonymous, pred)) env in
  let fix_term =
    eliminate_fixpoint fix_env evm ind_fam ind_sort fun_type fun_term
  in
  let fix_args = Array.append (Array.of_list indices) [|discr|] in
  mkApp (fix_term, fix_args)

let regularize_fixpoint fix_pos ind_rels fun_type fun_term =
  let ind_len = List.length ind_rels in
  let fun_len = fix_pos + 1 in
  let fun_ctxt = lam_n_assum fun_len fun_term in
  let fun_type = Vars.lift ind_len fun_type |> strip_prod_n fun_len in
  let fun_term = Vars.lift ind_len fun_term |> strip_lam_n fun_len in
  let fix_wrap =
    let fix_args =
      let rec_args = List.rev_map ((+) 1) ind_rels in
      let is_dup rel = not (List.mem rel rec_args) in
      List.init fun_len ((-) fun_len) |> List.filter is_dup |>
      List.append rec_args |> Array.map_of_list mkRel
    in
    let fix_rel = fun_len + 1 in
    recompose_lam_assum fun_ctxt (mkApp (mkRel fix_rel, fix_args))
  in
  let fun_ctxt =
    let fun_ctxt = Array.of_list fun_ctxt in
    List.iteri
      (fun i rel ->
         let rel' = fun_len - rel + i + 1 in
         fun_ctxt.(rel) <- define_rel_decl (mkRel rel') fun_ctxt.(rel))
      ind_rels;
    Array.to_list fun_ctxt
  in
  let fun_type = smash_prod_assum fun_ctxt fun_type in
  let fun_term = smash_lam_assum fun_ctxt fun_term in
  let fun_term =
    Vars.liftn 1 (ind_len + 1) fun_term |> Vars.substnl [fix_wrap] ind_len
  in
  fun_type, fun_term

(* Translate each match expression into an equivalent eliminator application *)
let desugar_fix_match env evm term =
  let evm = ref evm in
  let rec aux env term =
    match kind term with
    | Lambda (name, param, body) ->
      let param' = aux env param in
      let body' = aux (push_local (name, param') env) body in
      mkLambda (name, param', body')
    | Prod (name, param, body) ->
      let param' = aux env param in
      let body' = aux (push_local (name, param') env) body in
      mkProd (name, param', body')
    | LetIn (name, local, annot, body) ->
      let local' = aux env local in
      let annot' = aux env annot in
      let body' = aux (push_let_in (name, local', annot') env) body in
      mkLetIn (name, local', annot', body')
    | Fix (([|fix_pos|], 0), ([|fix_name|], [|fun_type|], [|fun_term|])) ->
      (* TODO: Encapsulate the below into common regularization function *)
      let fun_type = contract_prod_assum fun_type |> Vars.lift 1 in
      let fun_term = contract_lam_assum fun_term in
      let ind_name, ind_type =
        let ind_decl = lam_n_assum (fix_pos + 1) fun_term |> List.hd in
        rel_name ind_decl, rel_type ind_decl
      in
      let pind, params, indices = decompose_ind ind_type in
      let ind_fam =
        assert (List.for_all (Vars.noccur_between 1 fix_pos) params);
        make_ind_family (pind, List.map (Vars.lift (-fix_pos)) params)
      in
      let ind_rels =
        let rels = 0 :: List.rev_map destRel indices in
        assert (List.for_all (fun i -> i <= fix_pos) rels);
        assert (List.distinct rels);
        rels
      in
      let fun_type, fun_term =
        (* TODO: Move most of the above into here and modularize *)
        regularize_fixpoint fix_pos ind_rels fun_type fun_term
      in
      let ind_ctxt, ind_sort =
        let ind_fam = lift_inductive_family (-1) ind_fam in
        let ind_type = build_dependent_inductive env ind_fam in
        let ind_decl = rel_assum (ind_name, ind_type) in
        get_arity env ind_fam |> on_fst (Rel.add ind_decl) |>
        on_fst (Termops.smash_rel_context) |> on_fst (Termops.lift_rel_context 1)
      in
      let fun_type = recompose_lam_assum ind_ctxt fun_type in
      let fun_term = recompose_lam_assum ind_ctxt fun_term in
      let fix_decl = rel_assum (fix_name, Vars.lift (-1) fun_type) in
      let fix_env = Environ.push_rel fix_decl env in
      (* Feedback.msg_info (Printer.pr_constr_env env' !evm fun_type); *)
      (* Feedback.msg_info (Printer.pr_constr_env env' !evm fun_term); *)
      eliminate_fixpoint fix_env evm ind_fam ind_sort fun_type fun_term |> aux env
    | Fix _ ->
      user_err ~hdr:"desugar" (Pp.str "mutual recursion not supported")
    | CoFix _ ->
      user_err ~hdr:"desugar" (Pp.str "co-recursion not supported")
    | Case (info, pred, discr, cases) ->
      eliminate_match env evm info pred discr cases |> aux env
    | _ ->
      Constr.map (aux env) term
  in
  let term' = aux env term in
  let type' = e_infer_type env evm term' in (* NOTE: Infers universe constraints *)
  let evm' = !evm in
  evm', term', type'
