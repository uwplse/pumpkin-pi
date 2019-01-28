open Util
open Names
open Univ
open Context
open Term
open Constr
open Inductiveops
open CErrors
open Coqterms
open Abstraction

(*
 * Pair the outputs of two functions on the same input.
 *)
let pair f g =
  fun x -> f x, g x

(*
 * Convenient wrapper around Vars.liftn shift (skip + 1) term.
 *)
let lift_rels ?(skip=0) shift term =
  Vars.liftn shift (skip + 1) term

(*
 * Same as lift_rels ~skip:0 1.
 *)
let lift_rel = lift_rels 1

(*
 * Convenient wrapper around Vars.liftn (-shift) (skip + 1) term.
 *)
let drop_rels ?(skip=0) shift term =
  assert (Vars.noccur_between (skip + 1) (skip + shift) term);
  Vars.liftn (-shift) (skip + 1) term

(*
 * Same as drop_rels ~skip:0 1.
 *)
let drop_rel = drop_rels 1

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
 * E.g., abstract_assums [3; 1] [x:A; y:B; z:C] =
 * [x:=Rel(4):lift(2,2,A); y:lift(1,2,B); z:=Rel(1):lift(0,2,C)].
 *
 *)
let abstract_assums rels ctxt =
  let k = List.length rels in
  let len = Rel.length ctxt in
  let ctxt = Termops.lift_rel_context k ctxt |> Array.of_list in
  List.iteri
    (fun i rel ->
       let rel' = len - rel + i + 1 in
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
    assert (List.for_all (Vars.noccur_between 0 nb) params);
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
  let fun_ctxt = Termops.lift_rel_context 1 fun_ctxt in
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
 * Reorder the fixed point's parameters to quantify the inductive type like an
 * eliminator (i.e., indices in standard order followed by the inductive type).
 * Also return the inductive family structurally guarding recursion and a
 * conversion function wrapping its first free relative index.
 *)
let init_fixpoint env fix_pos fun_type fun_term =
  let nb = fix_pos + 1 in (* number of parameter bindings guarding recursion *)
  (* Pull off parameter bindings and reduce any interleaved local definitions *)
  let fun_ctxt, fun_type = decompose_prod_n_zeta nb fun_type in
  let _, fun_term = decompose_lam_n_zeta nb fun_term in
  (* Figure out what inductive type guards recursion and how it's quantified *)
  let ind_name, ind_type = Rel.lookup 1 fun_ctxt |> pair rel_name rel_type in
  let ind_fam, ind_rels = summarize_free_inductive nb ind_type in
  (* Build a standard parameter context to quantify the inductive type *)
  let ind_ctxt = build_inductive_context env ind_fam ind_name in
  let k = Rel.length ind_ctxt in
  (* Build a wrapper to convert from the original parameter order *)
  let fix_wrap = wrap_fixpoint nb ind_rels fun_ctxt in
  (* Prepend the standard parameter context, overriding shared parameters *)
  let fun_ctxt = (abstract_assums ind_rels fun_ctxt) @ ind_ctxt in
  let fun_type = smash_prod_assum fun_ctxt (lift_rels ~skip:nb k fun_type) in
  let fun_ctxt = Termops.lift_rel_context 1 fun_ctxt in
  let fun_term = smash_lam_assum fun_ctxt (lift_rels ~skip:nb k fun_term) in
  (* Reorder arguments to fixed-point calls in the functional *)
  let fun_term = Vars.subst1 fix_wrap (lift_rels ~skip:1 1 fun_term) in
  ind_fam, fun_type, fun_term, fix_wrap

(*
 * Build the minor premise for elimination at a constructor from the
 * corresponding fixed-point case.
 *
 * In particular, insert recurrence bindings (for inductive hypotheses) in the
 * appropriate positions, substituting recursive calls with the recurrence
 * binding its value.
 *
 * The last argument provides the case's parameter context (quantifying
 * constructor arguments) with the case's body term.
 *)
let premise_of_case env ind_fam (ctxt, body) =
  let nb = Rel.length ctxt in
  let ind_head = dest_ind_family ind_fam |> on_fst mkIndU |> applist in
  let fix_name, fix_type = Environ.lookup_rel 1 env |> pair rel_name rel_type in
  let insert_recurrence i body decl =
    let k = nb - i in
    let body' =
      match eq_constr_head (lift_rels k ind_head) (rel_type decl) with
      | Some indices ->
        assert (is_rel_assum decl);
        let args = Array.append (Array.map lift_rel indices) [|mkRel 1|] in
        let rec_type = prod_appvect (lift_rels (k + 1) fix_type) args in
        let fix_call = mkApp (mkRel (k + 1), args) in
        mkLambda (fix_name, rec_type, abstract_subterm fix_call body)
      | _ ->
        body
    in
    mkLambda_or_LetIn decl body'
  in
  List.fold_left_i insert_recurrence 0 body ctxt

(*
 * Given a constructor summary (cf., Inductiveops), build a parameter context
 * to quantify over constructor arguments (and thus values of that constructor)
 * and partially evaluate the functional applied to the constructed value's type
 * indices and (subsequently) to the constructed value itself.
 *
 * Partial evaluation reduces to beta/iota-normal form. Exclusion of delta
 * reduction is intentional (rarely beneficial, usually detrimental).
 *)
let split_case env evm fun_term cons_sum =
  let cons = build_dependent_constructor cons_sum in
  let env = Environ.push_rel_context cons_sum.cs_args env in
  let body =
    let head = lift_rels cons_sum.cs_nargs fun_term in
    let args = Array.append cons_sum.cs_concl_realargs [|cons|] in
    mkApp (head, args) |> Reduction.nf_betaiota env
  in
  deanonymize_context env evm cons_sum.cs_args, body

(*
 * Build an elimination head (partially applied eliminator) including the
 * parameters and (sort-adjusted) motive for the given inductive family and
 * (dependent) elimination type.
 *
 * The sorts of the inductive family and of the elimination type are considered,
 * respectively, when adjusting the elimination type into a motive (by removing
 * dependency for Prop-sorted inductive families) and when selecting one of the
 * inductive family's eliminators.
 *
 * NOTE: Motive adjustment might be too overzealous; under some particular
 * conditions, Coq does allow dependency in the elimination motive for a Prop-
 * sorted inductive family.
 *)
let configure_eliminator env evm ind_fam typ =
  let ind, params = dest_ind_family ind_fam |> on_fst out_punivs in
  let nb = inductive_nrealargs ind + 1 in
  let typ_ctxt, typ_body =
    let typ_ctxt, typ_body = decompose_prod_n_assum nb typ in
    let ind_sort = get_arity env ind_fam |> snd in
    if Sorts.family_equal ind_sort Sorts.InProp then
      List.tl typ_ctxt, drop_rel typ_body
    else
      typ_ctxt, typ_body
  in
  let elim =
    let typ_env = Environ.push_rel_context typ_ctxt env in
    let typ_sort = e_infer_sort typ_env evm typ_body in
    Indrec.lookup_eliminator ind typ_sort |> e_new_global evm
  in
  let motive = recompose_lam_assum typ_ctxt typ_body in
  mkApp (elim, Array.append (Array.of_list params) [|motive|])

(*
 * Given the components of a fixed-point expression, build an equivalent,
 * bisimulative (i.e., algorithmically identical) elimination expression.
 *
 * Note that the resulting term will not satisfy definitional equality with the
 * original term but should satisfy most (all?) definitional equalities when
 * applied to all indices and a head-canonical discriminee. Still, this could
 * impact the well-typedness of inductive proof terms, particularly when
 * rewriting the unrolled recursive function by an inductive hypothesis. We will
 * know more after testing compositional translation of a complete module, which
 * will avoid incidental mixtures of the old version (by named constant) and the
 * new version (by expanded definition). (Such incidental mixtures arise, for
 * example, in some of the List module's proofs regarding the In predicate.)
 *)
let eliminate_fixpoint env evm fix_pos fix_name fun_type fun_term =
  let ind_fam, fun_type, fun_term, fix_wrap =
    init_fixpoint env fix_pos fun_type fun_term
  in
  (* Build the elimination head (eliminator with parameters and motive) *)
  let elim_head = configure_eliminator env evm ind_fam fun_type in
  (* Build the minor premises *)
  let premises =
    let fix_env = Environ.push_rel (rel_assum (fix_name, fun_type)) env in
    let build_premise cons_sum =
      lift_constructor 1 cons_sum |> split_case fix_env !evm fun_term |>
      premise_of_case fix_env ind_fam |> drop_rel
    in
    get_constructors env ind_fam |> Array.map build_premise
  in
  (* Wrap the elimination expression to match the original parameter order *)
  Vars.subst1 (mkApp (elim_head, premises)) fix_wrap

(*
 * Given the components of a match expression, build an equivalent elimination
 * expression. The resulting term will not use any recurrence (i.e., inductive
 * hypothesis) bound in the minor elimination premises (i.e., case functions),
 * since the original term was non-recursive.
 *
 * Note that the resulting term may not satisfy definitional equality with the
 * original term, as Coq lacks eta-conversion between a non-recursive function
 * and its fixed point (i.e., f =\= fix[_.f]). Definitional equality should hold
 * (at least) when the discriminee term is head-canonical.
 *)
let eliminate_match env evm info pred discr cases =
  let typ = lambda_to_prod pred in
  let pind, params, indices = decompose_indvect (e_infer_type env evm discr) in
  let ind_fam = make_ind_family (pind, Array.to_list params) in
  let elim_head = configure_eliminator env evm ind_fam typ in
  let premises =
    let fix_env = Environ.push_rel (rel_assum (Name.Anonymous, typ)) env in
    let build_premise cons_narg cons_case =
      lift_rel cons_case |> decompose_lam_n_assum cons_narg |>
      premise_of_case fix_env ind_fam |> drop_rel
    in
    Array.map2 build_premise info.ci_cstr_nargs cases
  in
  mkApp (elim_head, Array.concat [premises; indices; [|discr|]])

(*
 * Translate the given term into an equivalent, bisimulative (i.e., homomorpic
 * reduction behavior) version using eliminators instead of match or fix
 * expressions.
 *
 * Mutual recursion and co-recursion are not supported.
 *)
let desugar_term env evm term =
  let evm = ref evm in
  let rec aux env term =
    match Constr.kind term with
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
      eliminate_fixpoint env evm fix_pos fix_name fun_type fun_term |> aux env
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
