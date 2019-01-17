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
 * For each relative index rel_i in the list rels, transform the local
 * assumption at rel into a local definition with body Rel(i), lifted from
 * outside the relative context. The relative context is lifted by length(rels)
 * to allocate fresh binding indices for each rel_i, prior to defining any local
 * assumption.
 *
 * E.g., factor_assums [3; 1] [x:A; y:B; z:C] =
 * [x:=Rel(4):lift(2,2,A); y:lift(1,2,B); z:=Rel(1):lift(0,2,C)].
 *
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
 * Summarize the recursively uniform and non-uniform components of an inductive
 * type quantified (for recursion) by nb levels of relative (deBruijn) binding.
 *
 * The recursively uniform components, which constitute the inductive name and
 * parameter terms, are summarized by an inductive family (cf., Inductiveops),
 * lifted outside the preceding nb-1 binding levels. An assertion checks that
 * each paremeter term is independent of those nb-1 preceding levels of binding
 * (i.e., that each parameter is uniform w.r.t. recursion).
 *
 * The recursively non-uniform components, which constitute the index terms and
 * inductive value, are summarized by a list of their relative (deBruijn)
 * indices in standard order, lifted inside the last binding level (whence the
 * input inductive type). Assertions check that all such relative indices are
 * distinct and within the nb binding levels quantifying the inductive type.
 *
 * The "free" in this function's name refers to how an inductive type
 * appropriately quantified for recursion should not constrain any index value,
 * at least defininitionally. In some edge cases, fixed points can avoid such
 * full quantification, but eliminators can never do so, at least directly.
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
 * In other words, the output relative context assumes all indices (in standard
 * order) and then a value of the inductive type (at those indices).
 *
 * Note that an inductive family is an inductive name with parameter terms.
 *)
let build_inductive_context env ind_fam ind_name =
  let ind_type = build_dependent_inductive env ind_fam in
  let ind_decl = rel_assum (ind_name, ind_type) in
  get_arity env ind_fam |> fst |> Rel.add ind_decl |> Termops.smash_rel_context

(*
 * Build a wrapper term for a fixed point that internally reorders arguments
 * from the functional's original order to the quantification-initial order
 * as in an eliminator. The output term is at the same binding level as fun_ctxt
 * (the original parameter context of the functional) and assumes that the very
 * next outside relative (deBruijn) binding refers to the transformed recursive
 * function (possibly due to the fixed point's self reference).
 *
 * Note that fun_len is literally just Rel.length fun_ctxt, and ind_rels is the
 * list of relative indices that quantify the inductive type's index values (in
 * standard order).
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
 * Build a re-ordered parameter context for a fixed point's functional in which
 * the inductive type for recursion is quantified (in standard order) before all
 * other parameters.
 *)
let order_fixpoint ind_ctxt ind_rels fun_ctxt fun_type fun_term =
  (* TODO: Maybe cleaner to factor+smash in one go *)
  let fun_ctxt = factor_assums ind_rels fun_ctxt in
  let lift = Vars.liftn (Rel.length ind_ctxt) (Rel.length fun_ctxt + 1) in
  let fun_type = fun_type |> lift |> smash_prod_assum fun_ctxt in
  let fun_term = fun_term |> lift |> smash_lam_assum fun_ctxt in
  Util.map_pair (recompose_lam_assum ind_ctxt) (fun_type, fun_term)

(*
 * Build the minor premise for elimination at a constructor from the
 * corresponding case branch of a fixed point.
 *
 * In particular, insert recurrence bindings (for inductive hypotheses) in the
 * appropriate positions, substituting recursive calls with the recurrence
 * binding its value.
 *
 * The last argument provides the parameter context quantifying the constructor
 * value as well as the body of the case branch for the same constructor.
 *)
let premise_of_case ind_fam rec_name motive (ctxt, body) =
  let nb = Rel.length ctxt in
  let ind_head = dest_ind_family ind_fam |> on_fst mkIndU |> applist in
  let insert_recurrence i body decl =
    let k = nb - i in
    let body' =
      match eq_constr_head (Vars.lift k ind_head) (rel_type decl) with
      | Some indices ->
        assert (is_rel_assum decl);
        let args = Array.append (Array.map (Vars.lift 1) indices) [|mkRel 1|] in
        let rec_type = Reduction.beta_appvect (Vars.lift (k + 1) motive) args in
        let fix_call = mkApp (mkRel (k + 2), args) in
        mkLambda (rec_name, rec_type, abstract_subterm fix_call body)
      | _ ->
        body
    in
    mkLambda_or_LetIn decl body'
  in
  List.fold_left_i insert_recurrence 1 body ctxt

(*
 * Given a constructor summary (cf., Inductiveops), build a parameter context
 * to quantify over constructor arguments (and thus values of that constructor)
 * and partially evaluate the functional applied to the constructed value's type
 * indices and to the constructed value itself.
 *
 * Partial evaluation reduces to beta/iota-normal form. Exclusion of delta
 * reduction is intentional (rarely necessary, usually disadvantageous).
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
 * Build a proper motive from a type predicate (that quantifies an inductive
 * type with lambdas).
 *
 * This basically comes down to dropping the quantifier for a value of the
 * inductive type (but keeping the quantifiers for type indices) if the
 * inductive definition is Prop-sorted.
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
 * Select the right eliminator for an inductive type, based on the result sort
 * (deduced from the type predicate).
 *)
let eliminator_for_predicate env evm ind pred =
  let ctxt, body = decompose_lam_assum pred in (* lambdas are never types *)
  let env = Environ.push_rel_context ctxt env in
  let sort = e_infer_sort env evm body in
  Indrec.lookup_eliminator ind sort |> e_new_global evm

(*
 * Given the pre-processed components of a fix expression, build a
 * computationally equivalent elimination expression.
 *
 * Pre-processing must transform the functional to abstract over the inductive
 * family's indices and discriminee (which guards structural recursion) in
 * standard order and without any interleaving local definitions (or extraneous
 * local assumptions). Pre-processing must also transform the functional's type
 * to abstract those bindings (which quantify over the inductive type) using
 * lambdas rather than products. Lastly, pre-processing must lift both the
 * inductive family and the functional's type under the implicitly assumed
 * fixed-point reference, not yet present in the environment.
 *
 * Note that the resulting term will not satisfy definitional equality with the
 * original term but should satisfy definitional equality whenever the
 * discriminee term is in canonical form (i.e., a value). This is unlikely to be
 * a major problem, since CiC's consistency+independence of functional
 * extensionality means that the type system has little ability to distinguish
 * equivalent functions. _However_, the set of definitional equalities satsified
 * by a specific realization of a function affects the necessity and sufficiency
 * of rewritings (e.g., left- vs. right-recursive addition); this can affect the
 * well-typedness of inductive proof terms, particularly when rewriting by an
 * inductive hypothesis.
 *)
let eliminate_fixpoint env evm ind_fam fix_name fun_type fun_term =
  let fix_decl = rel_assum (fix_name, Vars.lift (-1) fun_type) in
  let env = Environ.push_rel fix_decl env in
  let (ind, _), params = dest_ind_family ind_fam |> on_snd Array.of_list in
  let elim = eliminator_for_predicate env evm ind fun_type in
  let motive = motive_of_predicate env ind_fam fun_type in
  let minors =
    get_constructors env ind_fam |> Array.map (split_functional env fun_term) |>
    Array.map (premise_of_case ind_fam fix_name fun_type)
  in
  let premises = Array.cons motive minors in
  mkApp (elim, Array.append params premises) |> Vars.lift (-1)

(*
 * Given the components of a match expression, build a computationally
 * equivalent elimination expression. The resulting term will not use any
 * recurrence binding (i.e., inductive hypothesis) in its minor premises (i.e.,
 * case functions).
 *
 * Note that the resulting term will not satisfy definitional equality with the
 * original term, as Coq lacks eta-conversion between a non-recursive function
 * and its fixed point (i.e., f /= fix[f], even when f is non-recursive). The
 * two terms should satisfy definitional equality whenever the discriminee term
 * is in a head-canonical form.
 *)
let eliminate_match env evm info pred discr cases =
  let elim = eliminator_for_predicate env evm info.ci_ind pred in
  let fix_decl = rel_assum (Name.Anonymous, pred) in
  let env = Environ.push_rel fix_decl env in
  let pred, discr, cases =
    Vars.lift 1 pred, Vars.lift 1 discr, Array.map (Vars.lift 1) cases
  in
  let pind, params, indices = e_infer_type env evm discr |> decompose_indvect in
  let ind_fam = make_ind_family (pind, Array.to_list params) in
  let motive = motive_of_predicate env ind_fam pred in
  let minors =
    Array.map2 decompose_lam_n_assum info.ci_cstr_nargs cases |>
    Array.map (premise_of_case ind_fam Name.Anonymous pred)
  in
  let premises = Array.cons motive minors in
  mkApp (elim, Array.concat [params; premises; indices; [|discr|]]) |>
  Vars.lift (-1)

(*
 * Translate the given term into a computationally equivalent version using
 * eliminators instead of match and/or fix expressions. The output term will
 * closely simulate the input term but may satisfy a different set of
 * definitional equalities. (Consider how left- and right-recursive
 * implementations of addition often require different proof terms for the same
 * theorem, though the differences here are actually much simpler.)
 *
 * TODO: Investigate the impact of this translation on inductive proof terms
 * proving facts about a recursive fixed-point function. There are likely cases
 * in which this translation necessitates additional rewritings for an inductive
 * proof to hold with the recursive function post-translation.
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
