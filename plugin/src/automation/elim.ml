open Util
open Misctypes
open Decl_kinds
open Names
open Globnames
open Context
open Environ
open Term
open Constr
open Constrexpr
open Constrexpr_ops
open Constrextern

open Coqterms

let freshen_name idset name =
  let id = Namegen.next_name_away name idset in
  Name id, Id.Set.add id idset

let freshen_context idset ctxt =
  Rel.fold_outside
    (fun decl (ctxt, idset) ->
       let name, idset' = rel_name decl |> freshen_name idset in
       let decl' = Rel.Declaration.set_name name decl in
       Rel.add decl' ctxt, idset')
    ctxt
    ~init:(Rel.empty, idset)

let eta_extern_pattern idset npar head ctxt =
  let extern_ref = Constrextern.extern_reference idset in
  let skip_pat = CAst.make (CPatAtom None) in
  let bind_pat =
    let sigT_pat =
      let existT_ref = Lazy.force Coqlib.coq_existT_ref |> extern_ref in
      CAst.make (CPatCstr (existT_ref, Some (List.make 4 skip_pat), []))
    in
    fun decl ->
      if applies sigT (rel_type decl) then
        CAst.make (CPatAlias (sigT_pat, CAst.make (rel_name decl)))
      else
        CAst.make (CPatAtom (reference_of_name (rel_name decl)))
  in
  CAst.make
    (CPatCstr
       (extern_ref head,
        Some (List.rev_map bind_pat ctxt |> List.addn npar skip_pat),
        []))

let rec eta_extern env evm idset term =
  let raw_extern = EConstr.of_constr %> extern_constr ~lax:true false env evm in
  match kind term with
  | Rel i ->
    let decl = lookup_rel i env in
    let typ, val_opt = rel_type decl, rel_value decl in
    if applies sigT typ && not (Option.cata (applies existT) false val_opt) then
      raw_extern (eta_sigT term typ)
    else
      raw_extern term
  | Var id ->
    let decl = lookup_named id env in
    let typ, val_opt = named_type decl, named_value decl in
    if applies sigT typ && not (Option.cata (applies existT) false val_opt) then
      raw_extern (eta_sigT term typ)
    else
      raw_extern term
  | Cast (term, _, typ) ->
    mkCastC
      (eta_extern env evm idset term,
       CastConv (eta_extern env evm idset typ))
  | Prod (name, typ, body) ->
    (* let ctxt, body = Term.decompose_prod_assum term in *)
    let name, idset' = freshen_name idset name in
    mkProdC
      ([CAst.make name],
       Default Explicit,
       eta_extern env evm idset typ,
       eta_extern (push_local (name, typ) env) evm idset' body)
  | Lambda (name, typ, body) ->
    (* let ctxt, body = Term.decompose_lam_assum term in *)
    let name, idset' = freshen_name idset name in
    mkLambdaC
      ([CAst.make name],
       Default Explicit,
       eta_extern env evm idset typ,
       eta_extern (push_local (name, typ) env) evm idset' body)
  | LetIn (name, term, typ, body) ->
    let name, idset' = freshen_name idset name in
    mkLetInC
      (CAst.make name,
       eta_extern env evm idset term,
       Some (eta_extern env evm idset typ),
       eta_extern (push_let_in (name, term, typ) env) evm idset' body)
  | App (head, args) ->
    if is_or_applies existT head then
      raw_extern term
    else
      mkAppC
        (eta_extern env evm idset head,
         Array.map_to_list (eta_extern env evm idset) args)
  | Const _ | Ind _ | Construct _ ->
    let gref = global_of_constr term in
    CAppExpl ((None, extern_reference idset gref, None), []) |> CAst.make
  | Proj _ ->
    raw_extern term
  | Case (info, motive, discr, cases) ->
    let ind = info.ci_ind in
    let npar, nidx = info.ci_npar, Inductiveops.inductive_nrealargs ind in
    let (((rec_decl :: idx_ctxt) as ret_ctxt), ret_idset), ret_type =
      decompose_lam_n_assum (nidx + 1) motive |> on_fst (freshen_context idset)
    in
    let branches =
      Array.map2 decompose_lam_n_assum info.ci_cstr_nargs cases |>
      Array.map (on_fst (freshen_context idset)) |>
      Array.mapi
        (fun i ((ctxt, idset), body) ->
           CAst.make
             ([[eta_extern_pattern idset npar (ConstructRef (ind, i + 1)) ctxt]],
              eta_extern (push_rel_context ctxt env) evm idset body))
    in
    CCases
      (info.ci_pp_info.style,
       Some (eta_extern (push_rel_context ret_ctxt env) evm ret_idset ret_type),
       [(eta_extern env evm idset discr,
         Some (CAst.make (rel_name rec_decl)),
         Some (eta_extern_pattern idset npar (IndRef ind) idx_ctxt))],
       Array.to_list branches) |>
    CAst.make
  | Fix (([|rec_pos|], 0), ([|Name fix_id|], [|fun_type|], [|fun_body|])) ->
    let (((rec_decl :: _) as dom_ctxt), idset), cod_type =
      decompose_prod_n_assum (rec_pos + 1) fun_type |> on_fst (freshen_context idset)
    in
    let fix_decl = rel_assum (Name fix_id, recompose_prod_assum dom_ctxt cod_type) in
    let fix_ctxt = context_app dom_ctxt [fix_decl] in
    let fix_body = decompose_lam_n_assum (rec_pos + 1) fun_body |> snd in
    let fix_idset = Id.Set.add fix_id idset in
    CFix
      (CAst.make fix_id,
       [(CAst.make fix_id,
         (ident_of_name (rel_name rec_decl) |> Option.map CAst.make, CStructRec),
         eta_extern_context env evm idset dom_ctxt,
         eta_extern (push_rel_context dom_ctxt env) evm idset cod_type,
         eta_extern (push_rel_context fix_ctxt env) evm fix_idset fix_body)]) |>
    CAst.make
  | Fix _ ->
    failwith "Mutual fixed points unsupported"
  | CoFix (0, ([|Name fix_id|], [|fun_type|], [|fun_body|])) ->
    let (dom_ctxt, idset), cod_type =
      decompose_prod_assum fun_type |> on_fst (freshen_context idset)
    in
    let fix_decl = rel_assum (Name fix_id, recompose_prod_assum dom_ctxt cod_type) in
    let fix_ctxt = context_app dom_ctxt [fix_decl] in
    let fix_body = decompose_lam_n_assum (Rel.length dom_ctxt) fun_body |> snd in
    let fix_idset = Id.Set.add fix_id idset in
    CCoFix
      (CAst.make fix_id,
       [(CAst.make fix_id,
         eta_extern_context env evm idset dom_ctxt,
         eta_extern (push_rel_context dom_ctxt env) evm idset cod_type,
         eta_extern (push_rel_context fix_ctxt env) evm fix_idset fix_body)]) |>
    CAst.make
  | CoFix _ ->
    failwith "Mutual co-fixed points unsupported"
  | Sort sort ->
    let gsort =
      match Sorts.family sort with
      | Sorts.InProp -> GProp
      | Sorts.InSet -> GSet
      | Sorts.InType -> GType []
    in
    CSort gsort |> CAst.make
  | Meta _ | Evar _ -> failwith "Metavars and evars unsupported"
and eta_extern_context env evm idset ctxt =
  let binder_of_decl env decl =
    let decl = Termops.map_rel_decl (eta_extern env evm idset) decl in
    let lname = CAst.make (rel_name decl) in
    match rel_value decl with
    | None -> CLocalAssum ([lname], Default Explicit, rel_type decl)
    | Some def -> CLocalDef (lname, def, Some (rel_type decl))
  in
  map_rel_context env binder_of_decl ctxt |> List.rev
