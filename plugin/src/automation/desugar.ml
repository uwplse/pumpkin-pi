open Util
open Names
open Univ
open Context
open Term
open Constr
open Inductiveops
open CErrors
open Coqterms

(*
 * Give a "reasonable" name to each anonymous local declaration in the relative
 * context. Name generation is according to standard Coq policy (cf., Namegen)
 * and does not guarantee freshness, but term type-checking is only sensitive to
 * anonymity. (Names are freshened by subscription when printed.)
 *)
let deanonymize_context env evm ctxt =
  List.map EConstr.of_rel_decl ctxt |>
  Namegen.name_context env evm |>
  List.map (EConstr.to_rel_decl evm)

(*
 * Bind all local declarations in the relative context onto the body term as
 * products, substituting away (i.e., zeta-reducing) any local definitions.
 *)
let smash_prod_assum ctxt body =
  Rel.fold_inside
    (fun body decl ->
       match rel_value decl with
       | Some defn -> Vars.subst1 defn body
       | None -> mkProd (rel_name decl, rel_type decl, body))
    ~init:body
    ctxt

(*
 * Bind all local declarations in the relative context onto the body term as
 * lambdas, substituting away (i.e., zeta-reducing) any local definitions.
 *)
let smash_lam_assum ctxt body =
  Rel.fold_inside
    (fun body decl ->
       match rel_value decl with
       | Some defn -> Vars.subst1 defn body
       | None -> mkLambda (rel_name decl, rel_type decl, body))
    ~init:body
    ctxt

(*
 * Zeta-reduce any local definitions occurring in the leading prefix of product
 * and let bindings on the term. In other words, zeta-reduce all let expressions
 * above the first non-product, non-let expression.
 *)
let contract_prod_assum term =
  let ctxt, body = decompose_prod_assum term in
  smash_prod_assum ctxt body

(*
 * Zeta-reduce any local definitions occurring in the leading prefix of lambda
 * and let bindings on the term. In other words, zeta-reduce all let expressions
 * above the first non-lambda, non-let expression.
 *)
let contract_lam_assum term =
  let ctxt, body = decompose_lam_assum term in
  smash_lam_assum ctxt body

(*
 * Instantiate a local assumption as a local definition, using the provided term
 * as its definition.
 *
 * Raises an assertion error if the local declaration is not a local assumption.
 *)
let define_rel_decl body decl =
  assert (is_rel_assum decl);
  rel_defin (rel_name decl, body, rel_type decl)

(*
 * TODO
 *)
let factor_assums rels ctxt =
  let k = List.length rels in
  let len = Rel.length ctxt in
  let ctxt = Termops.lift_rel_context k ctxt |> Array.of_list in
  List.iteri
    (fun i rel ->
       let rel' = len - rel + i + 1 in
       assert (is_rel_assum (ctxt.(rel - 1)));
       ctxt.(rel - 1) <- define_rel_decl (mkRel rel') ctxt.(rel - 1))
    rels;
  Array.to_list ctxt

(*
 * Extract the components of an inductive type: the (universe-instantiated)
 * inductive name, the sequence of parameters, and the sequence of indices.
 *)
let decompose_indvect ind_type =
  let pind, args = decompose_appvect ind_type |> on_fst destInd in
  let nparam = inductive_nparams (out_punivs pind) in
  let params, indices = Array.chop nparam args in
  pind, params, indices

(*
 * Same as decompose_indvect but converts the result arrays into lists.
 *)
let decompose_ind ind_type =
  decompose_indvect ind_type |> on_pi2 Array.to_list |> on_pi3 Array.to_list

(*
 * TODO
 *)
let summarize_free_inductive nb ind_type =
  let pind, params, indices = decompose_ind ind_type in
  let ind_fam =
    assert (List.for_all (Vars.noccur_between 1 nb) params);
    make_ind_family (pind, params) |> lift_inductive_family (1 - nb)
  in
  let ind_rels =
    let rels = 0 :: List.rev_map destRel indices in
    assert (List.for_all ((>) nb) rels);
    assert (List.distinct rels);
    List.map ((+) 1) rels
  in
  ind_fam, ind_rels

(*
 * Construct a relative context, consisting of only local assumptions,
 * quantifying over instantiations of the inductive family.
 *
 * In other words, the output relative context assumes all indices (in canonical
 * order) and then a value of the inductive family instantiated with those
 * indices.
 *
 * Note that an inductive family is an inductive name with parameter terms.
 *)
let build_inductive_context env ind_fam ind_name =
  let ind_type = build_dependent_inductive env ind_fam in
  let ind_decl = rel_assum (ind_name, ind_type) in
  get_arity env ind_fam |> fst |> Rel.add ind_decl |> Termops.smash_rel_context

(*
 * TODO
 *)
let wrap_fixpoint fun_len ind_rels fun_ctxt =
  let fix_head = mkRel (fun_len + 1) in
  let fix_args =
    let ind_rels = Array.rev_of_list ind_rels in
    let arg_rels =
      let is_arg_rel rel = not (Array.mem rel ind_rels) in
      List.init fun_len ((-) fun_len) |> List.filter is_arg_rel |> Array.of_list
    in
    Array.append ind_rels arg_rels |> Array.map mkRel
  in
  recompose_lam_assum fun_ctxt (mkApp (fix_head, fix_args))

(*
 * TODO
 *)
let order_fixpoint ind_ctxt ind_rels fun_ctxt fun_type fun_term =
  (* TODO: Probably cleaner to factor+smash in one go *)
  let fun_ctxt = factor_assums ind_rels fun_ctxt in
  let lift = Vars.liftn (Rel.length ind_ctxt) (Rel.length fun_ctxt + 1) in
  let fun_type = fun_type |> lift |> smash_prod_assum fun_ctxt in
  let fun_term = fun_term |> lift |> smash_lam_assum fun_ctxt in
  Util.map_pair (recompose_lam_assum ind_ctxt) (fun_type, fun_term)

(*
 * TODO
 *)
let premise_of_case ind_fam rec_name motive (ctxt, body) =
  let nb = Rel.length ctxt in
  let ind_head = dest_ind_family ind_fam |> on_fst mkIndU |> applist in
  let fixpoint_to_recurrence i body decl =
    let k = nb - i in
    let body' =
      match eq_constr_head (Vars.lift k ind_head) (rel_type decl) with
      | Some indices when is_rel_assum decl ->
        let args = Array.append (Array.map (Vars.lift 1) indices) [|mkRel 1|] in
        let rec_type = Reduction.beta_appvect (Vars.lift (k + 1) motive) args in
        let fix_call = mkApp (mkRel (k + 2), args) in
        mkLambda (rec_name, rec_type, abstract_subterm fix_call body)
      | _ ->
        body
    in
    mkLambda_or_LetIn decl body'
  in
  List.fold_left_i fixpoint_to_recurrence 1 body ctxt

(*
 * TODO
 *)
let split_functional env fun_term cons_sum =
  let cons = build_dependent_constructor cons_sum in
  let env = Environ.push_rel_context cons_sum.cs_args env in
  let body =
    let head = Vars.lift cons_sum.cs_nargs fun_term in
    let args = Array.append cons_sum.cs_concl_realargs [|cons|] in
    mkApp (head, args) |> Reduction.nf_betaiota env
  in
  deanonymize_context env Evd.empty cons_sum.cs_args, body

(*
 * TODO
 *)
let motive_of_predicate env ind_fam pred =
  let ind = dest_ind_family ind_fam |> fst |> out_punivs in
  let ind_sort = get_arity env ind_fam |> snd in
  let ind_len = inductive_nrealargs ind + 1 in
  if Sorts.family_equal ind_sort Sorts.InProp then
    let ctxt, body = decompose_lam_n ind_len pred in
    assert (Vars.noccurn 1 body);
    compose_lam (List.tl ctxt) (Vars.lift (-1) body)
  else
    pred

(*
 * TODO
 *)
let eliminate_fixpoint env evm ind_fam fix_name fun_type fun_term =
  let fix_decl = rel_assum (fix_name, Vars.lift (-1) fun_type) in
  let env = Environ.push_rel fix_decl env in
  let (ind, _), params = dest_ind_family ind_fam |> on_snd Array.of_list in
  let sort = e_infer_sort env evm fun_type in
  let elim = Indrec.lookup_eliminator ind sort |> e_new_global evm in
  let motive = motive_of_predicate env ind_fam fun_type in
  let minors =
    get_constructors env ind_fam |> Array.map (split_functional env fun_term) |>
    Array.map (premise_of_case ind_fam fix_name fun_type)
  in
  let premises = Array.cons motive minors in
  mkApp (elim, Array.append params premises) |> Vars.lift (-1)

(*
 * TODO
 *)
let eliminate_match env evm info pred discr cases =
  let env = Environ.push_rel (rel_assum (Name.Anonymous, pred)) env in
  let pred, discr, cases =
    Vars.lift 1 pred, Vars.lift 1 discr, Array.map (Vars.lift 1) cases
  in
  let pind, params, indices = e_infer_type env evm discr |> decompose_indvect in
  let ind_fam = make_ind_family (pind, Array.to_list params) in
  let sort = e_infer_sort env evm pred in
  let elim = Indrec.lookup_eliminator info.ci_ind sort |> e_new_global evm in
  let motive = motive_of_predicate env ind_fam pred in
  let minors =
    Array.map2 decompose_lam_n_assum info.ci_cstr_nargs cases |>
    Array.map (premise_of_case ind_fam Name.Anonymous motive)
  in
  let premises = Array.cons motive minors in
  mkApp (elim, Array.concat [params; premises; indices; [|discr|]]) |>
  Vars.lift (-1)

(*
 * TODO
 *)
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
      let nb = fix_pos + 1 in
      let fun_type = contract_prod_assum fun_type |> Vars.lift 1 in
      let fun_term = contract_lam_assum fun_term in
      let fun_ctxt = lam_n_assum nb fun_term in
      let fun_type = strip_prod_n nb fun_type in
      let fun_term = strip_lam_n nb fun_term in
      let ind_name, ind_type =
        let ind_decl = Rel.lookup 1 fun_ctxt in
        rel_name ind_decl, rel_type ind_decl
      in
      let ind_fam, ind_rels = summarize_free_inductive nb ind_type in
      let fix_wrap = wrap_fixpoint nb ind_rels fun_ctxt in
      (* NOTE: Could push all the above into order_fixpoint, nbd regardless *)
      let fun_type, fun_term =
        let ind_ctxt = build_inductive_context env ind_fam ind_name in
        order_fixpoint ind_ctxt ind_rels fun_ctxt fun_type fun_term |>
        on_snd (Vars.liftn 1 2 %> Vars.subst1 fix_wrap)
      in
      let fix_elim = eliminate_fixpoint env evm ind_fam fix_name fun_type fun_term in
      Vars.subst1 fix_elim fix_wrap |> aux env
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
