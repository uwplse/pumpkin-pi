open Util
open Utilities
open Names
open Context
open Constr
open Declarations
open Coqterms

(* Safely infer the WHNF type of a term, updating the evar map *)
let e_infer_type env evm term =
  EConstr.of_constr term |> Typing.e_type_of ~refresh:true env evm |>
  Reductionops.whd_all env !evm |> EConstr.to_constr !evm

(* Does the inductive type have sort Prop? *)
let inductive_is_proposition env ind =
  Inductive.lookup_mind_specif env ind |> snd |> Inductive.mind_arity |> snd |>
  Sorts.family_equal Sorts.InProp

(* Return an array of boolean lists indicating recursive constructor parameters *)
let inductive_recurrence_mask env ind =
  let mind_body, ind_body = Inductive.lookup_mind_specif env ind in
  let npar = mind_body.mind_nparams in
  let make_mask ndecl typ =
    let aux n typ = n - 1, not (Vars.closedn n typ) in
    Term.decompose_prod_assum typ |> fst |> List.firstn ndecl |>
    List.map CRD.get_type |> List.fold_left_map aux (npar + ndecl - 1) |> snd
  in
  Array.map2 make_mask ind_body.mind_consnrealdecls ind_body.mind_user_lc

(* Translate a case from a match expression to anonymously bind recursive results *)
let insert_recurrences env npar is_prop motive ndecl rec_mask case =
  let decls, case_body = Term.decompose_lam_n_assum ndecl case in
  let env = Environ.push_rel_context decls env in
  let fresh _ =
    let open Namegen in
    Name.Name (Termops.vars_of_env env |> next_ident_away default_dependent_ident)
  in
  let aux (idecl, case') is_rec decl =
    let env' = Environ.pop_rel_context idecl env in
    let case'' =
      if is_rec then
        let is_anon = CRD.get_name decl |> Name.is_anonymous in
        let decl' = if is_anon then CRD.set_name (fresh ()) decl else decl in
        let idcs =
          CRD.get_type decl' |> Inductive.find_inductive env' |> snd |>
          List.skipn npar |> List.map (Vars.lift 1)
        in
        let args = if is_prop then idcs else snoc (mkRel 1) idcs in
        let recur = Term.applistc (Vars.lift (ndecl - idecl + 1) motive) args in
        mkLambda (Name.Anonymous, recur, Vars.lift 1 case') |>
        recompose_lam_assum [decl']
      else
        recompose_lam_assum [decl] case'
    in
    idecl + 1, case''
  in
  List.fold_left2 aux (1, case_body) rec_mask decls |> snd

(* Translate each match expression into a definitionally equal eliminator application *)
let desugar_matches env evm term =
  let evm = ref evm in
  let with_evar_map (evm', x) = evm := evm'; x in
  let rec aux env term =
    match kind term with
    | Case (info, motive, discr, cases) ->
      let ind = info.ci_ind in
      let npar = info.ci_npar in
      let elim =
        EConstr.of_constr term |> Typing.e_type_of ~refresh:true env evm |>
        Typing.e_sort_of env evm |> Sorts.family |> Indrec.lookup_eliminator ind |>
        Evd.fresh_global env !evm |> with_evar_map
      in
      let is_prop = inductive_is_proposition env ind in
      let typ = e_infer_type env evm discr in
      let pars, idcs = decompose_appvect typ |> snd |> Array.chop npar in
      let nidx = Array.length idcs in
      let motive' =
        if is_prop then
          let decls, motive_body = Term.decompose_lam_n_assum (nidx + 1) motive in
          Vars.lift (-1) motive_body |> recompose_lam_assum (List.tl decls)
        else
          motive
      in
      let cases' =
        let rec_mask = inductive_recurrence_mask env ind in
        let ins_rec = insert_recurrences env npar is_prop motive in
        Array.map3 ins_rec info.ci_cstr_ndecls rec_mask cases
      in
      let term' = mkApp (elim, Array.concat [pars; [|motive'|]; cases'; idcs; [|discr|]]) in
      aux env term'
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
    | Fix _ | CoFix _ ->
      failwith "Raw (co-)fixed points are not supported"
    | _ ->
      Constr.map (aux env) term
  in
  let term' = aux env term in
  let type' = e_infer_type env evm term' in (* NOTE: Infers universe constraints *)
  let evm' = !evm in
  evm', term'
