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

(* Delete or "zap" the nth lambda binding, skipping over any let bindings *)
let zap_lam n term =
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
    (* NOTE: May want to try beta+iota+zeta reduction *)
    let case = Reduction.nf_betaiota env (mkApp (body, args)) in
    cons_sum.cs_nargs, recompose_lam_assum cons_sum.cs_args case
  in
  Array.map split_case (get_constructors env ind_fam)

(* TODO: Must configure for propositional sorts *)
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
  let fix_decl = rel_assum (fix_name, fun_type) in
  let (ind, _), params = dest_ind_family ind_fam |> on_snd Array.of_list in
  let sort = e_infer_sort env evm fun_type in
  let is_prop = inductive_is_proposition env ind_fam in
  let fix_env = Environ.push_rel fix_decl env in
  let ind_fam = lift_inductive_family 1 ind_fam in
  let nindex = inductive_nrealargs ind in
  let elim = Indrec.lookup_eliminator ind sort in
  let cases = split_functional fix_env ind_fam fun_term in
  let motive = Vars.lift 1 fun_type |> to_lambda (nindex + 1) in
  let minors = Array.map (premise_of_case fix_env ind_fam motive) cases in
  let motive = if is_prop then zap_lam (nindex + 1) motive else motive in
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

let predicate_of_motive nidx is_prop motive =
  if is_prop then
    (* Induction principles for propositional types are non-dependent. *)
    let decls, motive_body = decompose_lam_n_assum (nidx + 1) motive in
    Vars.lift (-1) motive_body |> recompose_lam_assum (List.tl decls)
  else
    motive

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
    | Fix (([|fix_size|], 0), ([|fix_name|], [|fun_type|], [|fun_body|])) ->
      let ind_fam, fun_type, fun_body =
        regularize_fixpoint (fix_size + 1) fun_type fun_body
      in
      (* TODO: Proposition-sorted inductive types *)
      eliminate_fixpoint env evm ind_fam fix_name fun_type fun_body |> aux env
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
