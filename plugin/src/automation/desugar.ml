open Util
open Utilities
open Names
open Univ
open Context
open Term
open Constr
open Inductiveops
open Declarations
open CErrors
open Coqterms

let nf_betaiotazeta env evm term =
  (* Reduction.nf_betaiota *)
  let open Reductionops in
  EConstr.of_constr term |> nf_betaiotazeta env evm |> EConstr.to_constr evm

let freshen_name idset name =
  let name' = Namegen.next_name_away name !idset in
  idset := Id.Set.add name' !idset;
  name'

let split_functional env evm ind_fam body =
  let split_case cons_sum =
    let cons = build_dependent_constructor cons_sum in
    let env = Environ.push_rel_context cons_sum.cs_args env in
    let body = Vars.lift cons_sum.cs_nargs body in
    let args = Array.append cons_sum.cs_concl_realargs [|cons|] in
    let case = nf_betaiotazeta env evm (mkApp (body, args)) in
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
let elimination_for_fixpoint env evm ind_fam fix_name fun_type fun_term =
  let fix_decl = rel_assum (fix_name, fun_type) in
  let (ind, _), params = dest_ind_family ind_fam |> on_snd Array.of_list in
  let sort = e_infer_sort env evm fun_type in
  let fix_env = Environ.push_rel fix_decl env in
  let ind_fam = lift_inductive_family 1 ind_fam in
  let nindex = inductive_nrealargs ind in
  let elim = Indrec.lookup_eliminator ind sort in
  let cases = split_functional fix_env !evm ind_fam fun_term in
  let motive = Vars.lift 1 fun_type |> to_lambda (nindex + 1) in
  let minors = Array.map (premise_of_case fix_env ind_fam motive) cases in
  let premises = Array.cons motive minors |> Array.map (Vars.lift (-1)) in
  mkApp (e_new_global evm elim, Array.append params premises)

let regularize_fixpoint fix_size fun_type fun_term =
  let fix_ctxt, fun_body = decompose_lam_n_assum fix_size fun_term in
  let fix_type = Rel.lookup 1 fix_ctxt |> rel_type in
  let pind, args = destApp fix_type |> on_fst destInd in
  let nparam = inductive_nparams (out_punivs pind) in
  let params, indices = Array.chop nparam args in
  let nindex = Array.length indices in
  (* Are the parameters bound externally? *)
  assert (Array.for_all (Vars.noccur_between 1 fix_size) params);
  (* Are the indices bound internally and in order? *)
  assert (Array.for_all_i (fun i -> isRelN (fix_size - i)) 1 indices);
  (* Is anything else bound between the indices and the inductive term? *)
  assert (Int.equal (nindex + 1) fix_size);
  (* TODO: Shuffle parameters and indices by rebinding and substituting *)
  let ind_fam =
    make_ind_family (pind, List.map_of_array (Vars.lift (-fix_size)) params)
  in
  ind_fam, fun_type, fun_term

(* Does the inductive type have sort Prop? *)
let inductive_is_proposition env ind =
  Inductive.lookup_mind_specif env ind |> snd |>
  Inductive.mind_arity |> snd |>
  Sorts.family_equal Sorts.InProp

let predicate_of_motive nidx is_prop motive =
  if is_prop then
    (* Induction principles for propositional types are non-dependent. *)
    let decls, motive_body = decompose_lam_n_assum (nidx + 1) motive in
    Vars.lift (-1) motive_body |> recompose_lam_assum (List.tl decls)
  else
    motive

(* Return an array of boolean lists indicating recursive constructor parameters *)
let inductive_recurrence_mask env ind npar =
  let mind_body, ind_body = Inductive.lookup_mind_specif env ind in
  let make_mask ndecl typ =
    let aux n typ = n - 1, not (Vars.closedn n typ) in
    decompose_prod_assum typ |> fst |> List.firstn ndecl |>
    List.map CRD.get_type |> List.fold_left_map aux (npar + ndecl - 1) |> snd
  in
  Array.map2 make_mask ind_body.mind_consnrealdecls ind_body.mind_user_lc

(* Translate a case from a match expression to anonymously bind recursive results *)
let insert_recurrences env npar is_prop motive ndecl rec_mask branch =
  let decls, branch_body = decompose_lam_n_assum ndecl branch in
  let env = Environ.push_rel_context decls env in
  let fresh _ =
    let open Namegen in
    Name.Name (Termops.vars_of_env env |> next_ident_away default_dependent_ident)
  in
  let aux (idecl, case) is_rec decl =
    let env' = Environ.pop_rel_context idecl env in
    let case' =
      if is_rec then
        let is_anon = CRD.get_name decl |> Name.is_anonymous in
        let decl' = if is_anon then CRD.set_name (fresh ()) decl else decl in
        let idcs =
          CRD.get_type decl' |> Inductive.find_inductive env' |> snd |>
          List.skipn npar |> List.map (Vars.lift 1)
        in
        let args = if is_prop then idcs else snoc (mkRel 1) idcs in
        let recur = applistc (Vars.lift (ndecl - idecl + 1) motive) args in
        mkLambda (Name.Anonymous, recur, Vars.lift 1 case) |>
        recompose_lam_assum [decl']
      else
        recompose_lam_assum [decl] case
    in
    idecl + 1, case'
  in
  List.fold_left2 aux (1, branch_body) rec_mask decls |> snd

(* Translate each match expression into a definitionally equal eliminator application *)
let desugar_matches env evm term =
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
    | Fix (([|fix_size|], 0), ([|fix_name|], [|fun_type|], [|fun_body|])) ->
      let ind_fam, fun_type, fun_body =
        regularize_fixpoint (fix_size + 1) fun_type fun_body
      in
      (* TODO: Proposition-sorted inductive types *)
      elimination_for_fixpoint env evm ind_fam fix_name fun_type fun_body |>
      aux env
    | Fix _ ->
      user_err ~hdr:"desugar" (Pp.str "mutual recursion not supported")
    | CoFix _ ->
      user_err ~hdr:"desugar" (Pp.str "co-recursion not supported")
    | Case (info, pred, discr, branches) ->
      let ind = info.ci_ind in
      let npar = info.ci_npar in
      (* let pind, args = e_infer_type env evm discr |> EConstr.of_constr |> find_inductive env !evm in *)
      (* elimination_for_fixpoint env evm (make_ind_family (pind, ??)) ?? motive (Vars.lift 1 term) *)
      let nidx = inductive_nrealargs ind in
      let elim = e_infer_sort env evm term |> Indrec.lookup_eliminator ind in
      let is_prop = inductive_is_proposition env ind in
      let pred = predicate_of_motive nidx is_prop pred in
      let cases =
        let rec_mask = inductive_recurrence_mask env ind npar in
        let ins_rec = insert_recurrences env npar is_prop pred in
        Array.map3 ins_rec info.ci_cstr_ndecls rec_mask branches
      in
      let pars, idcs =
        e_infer_type env evm discr |> decompose_appvect |> snd |> Array.chop npar
      in
      let term' =
        mkApp
          (Evarutil.e_new_global evm elim |> EConstr.to_constr !evm,
           Array.concat [pars; [|pred|]; cases; idcs; [|discr|]])
      in
      aux env term'
    | _ ->
      Constr.map (aux env) term
  in
  let term' = aux env term in
  let type' = e_infer_type env evm term' in (* NOTE: Infers universe constraints *)
  let evm' = !evm in
  evm', term'
