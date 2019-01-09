open Util
open Names
open Univ
open Context
open Term
open Constr
open Inductiveops
open CErrors
open Coqterms

let both p q =
  fun x -> p x && q x

let define_rel_decl body decl =
  assert (is_rel_assum decl);
  rel_defin (rel_name decl, body, rel_type decl)

let assign_rel_decl len ctxt rel term =
  Rel.lookup rel ctxt |>
  define_rel_decl (Vars.lift (len - rel) term) |>
  List.assign ctxt (rel - 1)

let find_inductive_quantification pos ctxt =
  (* Collapse all local definitions, to align declarations and arguments *)
  let ctxt = Termops.smash_rel_context ctxt in
  (* Extract the quantified inductive type *)
  let ind_name, ind_type =
    let ind_decl = Rel.lookup (Rel.length ctxt - pos) ctxt in
    rel_name ind_decl, rel_type ind_decl
  in
  (* Decompose the quantified inductive type *)
  let pind, (params, indices) =
    let pind, args = decompose_app ind_type |> on_fst destInd in
    pind, List.chop (inductive_nparams (out_punivs pind)) args
  in
  (* Construct the inductive family outside the local context *)
  let ind_fam =
    assert (List.for_all (Vars.noccur_between 1 pos) params);
    make_ind_family (pind, List.map (Vars.lift (-pos)) params)
  in
  (* Determine the argument position(s) for the inductive quantifier(s) *)
  let ind_pos =
    assert (List.for_all (both isRel (Vars.closedn pos)) indices);
    let ind_rels = 0 :: List.rev_map destRel indices in
    assert (List.distinct ind_rels);
    List.map ((-) pos) ind_rels
  in
  ind_fam, ind_pos, ind_name

let make_inductive_quantification env ind_fam ind_name =
  (* Build a local context quantifying the inductive family's indices  *)
  let ind_ctxt = get_arity env ind_fam |> fst in
  (* Instantiate the inductive family with indices from above local context *)
  let ind_type = build_dependent_inductive env ind_fam in
  let ind_decl = rel_assum (ind_name, ind_type) in
  (* Append local assumption for freshly instantiated inductive type *)
  Rel.add ind_decl ind_ctxt

let wrap_inductive_quantification ind_ctxt ind_pos ctxt =
  let narg = Rel.nhyps ctxt in
  List.fold_left2
    (assign_rel_decl (Rel.length ctxt))
    ctxt
    (List.map ((-) narg %> Vars.adjust_rel_to_rel_context ctxt) ind_pos)
    (Rel.to_extended_list mkRel 0 ind_ctxt)

let regularize_fixpoint ind_ctxt ind_pos fun_type fun_term =
  let ind_len = Rel.length ind_ctxt in
  (* NOTE: This is closer to a motive... *)
  let fun_type =
    let ctxt, body = fun_type |> Vars.lift ind_len |> decompose_prod_assum in
    let ctxt = wrap_inductive_quantification ind_ctxt ind_pos ctxt in
    body |> recompose_prod_assum ctxt |> recompose_lam_assum ind_ctxt
  in
  let fun_term =
    let ctxt, body = fun_term |> Vars.lift ind_len |> decompose_lam_assum in
    let ctxt = wrap_inductive_quantification ind_ctxt ind_pos ctxt in
    body |> recompose_lam_assum ctxt |> recompose_lam_assum ind_ctxt
  in
  fun_type, fun_term

(* Drop the nth lambda binding, skipping over any let bindings *)
let drop_lam n term =
  (* TODO: Combine with function-izing type *)
  let (decl :: ctxt), body = decompose_lam_n_assum n term in
  assert (Vars.noccurn 1 body);
  recompose_lam_assum ctxt (Vars.lift (-1) body)

(* Does the inductive type have sort Prop? *)
let inductive_is_proposition env ind_fam =
  get_arity env ind_fam |> snd |> Sorts.family_equal Sorts.InProp

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
let eliminate_fixpoint env evm ind_fam fix_name fun_type fun_term =
  let env = push_local (fix_name, Vars.lift (-1) fun_type) env in
  let (ind, _), params = dest_ind_family ind_fam |> on_snd Array.of_list in
  let sort = e_infer_sort env evm fun_type in
  let is_prop = inductive_is_proposition env ind_fam in
  let nindex = inductive_nrealargs ind in
  let elim = Indrec.lookup_eliminator ind sort in
  let cases = split_functional env ind_fam fun_term in
  let motive = if is_prop then drop_lam (nindex + 1) fun_type else fun_type in
  let minors = Array.map (premise_of_case env ind_fam motive) cases in
  let premises = Array.cons motive minors in
  mkApp (e_new_global evm elim, Array.append params premises) |> Vars.lift (-1)

(* Convenient wrapper around eliminate_fixpoint *)
let eliminate_match env evm info pred discr cases =
  let pind, (params, indices) =
    e_infer_type env evm discr |> Inductive.find_inductive env |>
    on_snd (List.chop info.ci_npar)
  in
  let ind_fam = make_ind_family (pind, params) in
  let nindex = List.length indices in
  let ctxt, return = decompose_lam_n_assum (nindex + 1) pred in
  let fun_body =
    let lift = Vars.lift (nindex + 2) in
    mkCase (info, lift pred, mkRel 1, Array.map lift cases)
  in
  let fun_term = recompose_lam_assum ctxt fun_body in
  let fun_type = recompose_prod_assum ctxt return in
  let fix_term = eliminate_fixpoint env evm ind_fam Anonymous fun_type fun_term in
  let fix_args = Array.append (Array.of_list indices) [|discr|] in
  mkApp (fix_term, fix_args)

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
      let fun_type = Vars.lift 1 fun_type in
      let ind_fam, ind_pos, ind_name =
        find_inductive_quantification fix_pos (lam_assum fun_term)
      in
      let fun_type, fun_term =
        let ind_ctxt = make_inductive_quantification env ind_fam ind_name in
        regularize_fixpoint ind_ctxt ind_pos fun_type fun_term
      in
      let env' = push_local (fix_name, Vars.lift (-1) fun_type) env in
      (* Feedback.msg_info (Printer.pr_constr_env env' !evm fun_type); *)
      (* Feedback.msg_info (Printer.pr_constr_env env' !evm fun_term); *)
      eliminate_fixpoint env evm ind_fam fix_name fun_type fun_term |> aux env
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
