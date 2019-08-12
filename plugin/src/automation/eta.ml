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
open Contextutils
open Apputils
open Sigmautils
open Nameutils
open Envutils

(*
 * TODO move some of this into lib
 *)

(*
 * Apply Coq's name-freshening policy (i.e., increment subscript if necessary)
 * and insert freshened name into the set of used identifiers. Also deanonymize
 * the name, using Coq's standard default name (modulo freshening).
 *
 * See [Namegen.next_name_away] and [Namegen.next_ident_away] to learn more about
 * Coq's freshening policy.
 *)
let freshen_name idset name =
  let id = Namegen.next_name_away name idset in
  Name id, Id.Set.add id idset

(*
 * Freshen all declarations in a rel context, from outermost to innermost
 * bindings, using Coq's standard freshing policy. In effect, append/increment
 * numerical subscripts on recycled identifiers, increasing with binding depth.
 *
 * See [Namegen.next_name_away] and [Namegen.next_ident_away] to learn more about
 * Coq's freshening policy.
 *)
let freshen_context idset ctxt =
  Rel.fold_outside
    (fun decl (ctxt, idset) ->
       let name, idset' = rel_name decl |> freshen_name idset in
       let decl' = Rel.Declaration.set_name name decl in
       Rel.add decl' ctxt, idset')
    ctxt
    ~init:(Rel.empty, idset)

(*
 * Build a surface-level pattern (i.e., [Constrexpr.cases_pattern_expr]) from a
 * rel context with unique identifiers (e.g., freshened beforehand), with nested
 * pattern-match on each sigma-type argument in order to induce definitional
 * eta-expansion.
 *
 * The head symbol (a [global_reference]) must be either an inductive type or a
 * constructor. The rel context should be real-argument arity. (Decoding the Coq
 * parlance, "arity" means the type signature as a rel context, and a "real
 * argument" is a local assumption; hence, parameters are excluded and local
 * definitions are folded into the local assumptions' types.)
 *
 * The identifier set is used to build an unambiguous reference to the head
 * symbol and to the sigma type's constructor.
 *
 * The number of parameters is used to insert that many "skip patterns"
 * (i.e., underscores) before the real arguments, as required by Coq.
 *)
let eta_extern_pattern idset npar head ctxt =
  let extern_ref = Constrextern.extern_reference idset in
  let skip_pat = CAst.make (CPatAtom None) in (* pattern is `_` *)
  let bind_pat =
    let sigT_pat = (* pattern is `@existT _ _ _ _` *)
      let existT_ref = Lazy.force Coqlib.coq_existT_ref |> extern_ref in
      CAst.make (CPatCstr (existT_ref, Some (List.make 4 skip_pat), []))
    in
    fun decl ->
      if applies sigT (rel_type decl) then
        (* pattern is `(@existT _ _ _ _) as x` *)
        CAst.make (CPatAlias (sigT_pat, CAst.make (rel_name decl)))
      else
        (* pattern is `x` *)
        CAst.make (CPatAtom (reference_of_name (rel_name decl)))
  in
  (* pattern is `@head _ ... x|((@existT _ _ _ _) as x) ...` *)
  CAst.make
    (CPatCstr
       (extern_ref head,
        Some (List.rev_map bind_pat ctxt |> List.addn npar skip_pat),
        []))

(*
 * Externalize a variant of the well-typed term, in which every variable with
 * sigma type is eta-expanded (e.g., `x` --> `existT (projT1 x) (projT2 x)`),
 * unless eta-expansion is already available definitionally (e.g.,
 * `x := existT y z` in context or environment). Moreover, every case analysis
 * of a form with a field of sigma type is extended to pattern-match each field
 * of sigma type, therefore inducing a definitional eta-expansion.
 *
 * The purpose of this function is to "eta-externalize" an eliminator of a
 * lifted inductive type and then internalize (type-check) the resulting
 * expression to serve as the lifting of the corresponding eliminator of the
 * base type.
 *)
let rec eta_extern env sigma idset term =
  (* The environment is synchronized with the current position in the *original*
     term *with* variables freshened, and the identifier set accumulates all
     names used for local variables in context (i.e., equal to [rel_context env
     |> Termops.ids_of_rel_context |> Id.Set.of_list] but built incrementally).
     Note how the environment and identifier set are always kept in agreement.

     The evar map stays constant throughout the whole function call. *)
  let raw_extern = EConstr.of_constr %> extern_constr ~lax:true false env sigma in
  (* Flags to extern_constr are important:
     1. Be temporarily lax w.r.t. well-typedness due to changing term context.
     2. Forbid variable renaming, because subterms are externalized separately. *)
  match kind term with
  | Rel i ->
    let decl = lookup_rel i env in
    let typ, val_opt = rel_type decl, rel_value decl in
    (* eta-expand if [typ] ~ `sigT _ _` and [env] |\- [term] := `existT ...` *)
    if applies sigT typ && not (Option.cata (applies existT) false val_opt) then
      raw_extern (eta_sigT term typ)
    else
      raw_extern term
  | Var id ->
    let decl = lookup_named id env in
    let typ, val_opt = named_type decl, named_value decl in
    (* eta-expand if [typ] ~ `sigT _ _` and [env] |\- [term] := `existT ...` *)
    if applies sigT typ && not (Option.cata (applies existT) false val_opt) then
      raw_extern (eta_sigT term typ)
    else
      raw_extern term
  | Cast (term, _, typ) ->
    mkCastC
      (eta_extern env sigma idset term,
       CastConv (eta_extern env sigma idset typ))
  | Prod (name, typ, body) ->
    let name, idset' = freshen_name idset name in
    mkProdC
      ([CAst.make name],
       Default Explicit, (* normal binder *)
       eta_extern env sigma idset typ,
       eta_extern (push_local (name, typ) env) sigma idset' body)
  | Lambda (name, typ, body) ->
    let name, idset' = freshen_name idset name in
    mkLambdaC
      ([CAst.make name],
       Default Explicit, (* normal binder *)
       eta_extern env sigma idset typ,
       eta_extern (push_local (name, typ) env) sigma idset' body)
  | LetIn (name, term, typ, body) ->
    let name, idset' = freshen_name idset name in
    mkLetInC
      (CAst.make name,
       eta_extern env sigma idset term,
       Some (eta_extern env sigma idset typ),
       eta_extern (push_let_in (name, term, typ) env) sigma idset' body)
  | App (head, args) ->
    if is_or_applies existT head then
      (* Job done if [term] ~ `existT ...` *)
      raw_extern term
    else
      mkAppC
        (eta_extern env sigma idset head,
         Array.map_to_list (eta_extern env sigma idset) args)
  | Const _ | Ind _ | Construct _ ->
    let gref = global_of_constr term in
    (* Careful to emit `@symbol` (w/o implicit arguments) instead of `symbol` *)
    CAppExpl ((None, extern_reference idset gref, None), []) |> CAst.make
  | Proj _ ->
    raw_extern term
  | Case (info, motive, discr, cases) ->
    (* According to comments in [Constr], the binding structure of a case
       expression is such that the following expression
         `match <e_0> as <x> in <Ind> _ ... <idx_1> ... <idx_n> return <type> with
          | <Con_1> _ ... <arg_1_1> ... <arg_1_n> => <e_1>
          ...
          | <Con_n> _ ... <arg_n_1> ... <arg_n_n> => <e_n>
          end`
       denotes a case term with the following components:
         motive = Pi <idx_1>. ... Pi <idx_n>. Pi (<x>:<Ind ...>). <type>
         discr = <e>
         cases =  [lambda <arg_1_1>. ... lambda <arg_1_n>. <e_1>;
                   ...;
                   lambda <arg_n_1>. ... lambda <arg_n_n>. <e_n>]
       Note that the inductive type's parameters are always matched with
       underscores and, unlike indices and fields, are *not* bound abstractly in
       the component subterms of the case term.
    *)
    let ind = info.ci_ind in
    let npar, nidx = info.ci_npar, Inductiveops.inductive_nrealargs ind in
    (* [ret_ctxt] binds the type indices (in order) and then the discriminee. *)
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
              eta_extern (push_rel_context ctxt env) sigma idset body))
    in
    CCases
      (info.ci_pp_info.style,
       Some (eta_extern (push_rel_context ret_ctxt env) sigma ret_idset ret_type),
       [(eta_extern env sigma idset discr,
         Some (CAst.make (rel_name rec_decl)),
         Some (eta_extern_pattern idset npar (IndRef ind) idx_ctxt))],
       Array.to_list branches) |>
    CAst.make
  | Fix (([|rec_pos|], 0), ([|Name fix_id|], [|fun_type|], [|fun_body|])) ->
    (* According to comments in [Constr], the binding structure of a fixed-point
       expression is such that the following expression:
         `fix <f> <x_1> (<y> := <e_y>) <x_2> <x_3> {struct <x_2>} : <B> := <e> end`
       denotes a fixed-point term with the following components:
         rec_pos = 1 (number of parameter bindings _before_ the structural one)
         fix_id = <f>
         fun_type = Pi <x_1>. let <y> := <e_y> in Pi <x_2>. Pi <x_3>. <B>
         fun_body = lambda <x_1>. let <y> := <e_y> in lambda <x_2>. lambda <x_3>. <e>
    *)
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
         eta_extern_context env sigma idset dom_ctxt,
         eta_extern (push_rel_context dom_ctxt env) sigma idset cod_type,
         eta_extern (push_rel_context fix_ctxt env) sigma fix_idset fix_body)]) |>
    CAst.make
  | CoFix (0, ([|Name fix_id|], [|fun_type|], [|fun_body|])) ->
    (* Implemented by direct analogy with case for fixed-points. *)
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
         eta_extern_context env sigma idset dom_ctxt,
         eta_extern (push_rel_context dom_ctxt env) sigma idset cod_type,
         eta_extern (push_rel_context fix_ctxt env) sigma fix_idset fix_body)]) |>
    CAst.make
  | Sort sort ->
    (* Delete existing universe constraints so that Coq will infer fresh,
       consistent ones. *)
    let gsort =
      match Sorts.family sort with
      | Sorts.InProp -> GProp
      | Sorts.InSet -> GSet
      | Sorts.InType -> GType []
    in
    CSort gsort |> CAst.make
  | Fix _ -> failwith "eta_extern: Mutual fixed points unsupported"
  | CoFix _ -> failwith "eta_extern: Mutual co-fixed points unsupported"
  | Meta _ | Evar _ -> failwith "eta_extern: Metavars and evars unsupported"
and eta_extern_context env sigma idset ctxt =
  (* Build a [local_binder_expr list] for a freshened rel context [ctxt]
     well-typed in [env]. Types and locally defined terms are recursively eta-
     externalized in a properly synchronized environment but with the same given
     identifier set. *)
  let binder_of_decl env decl =
    let decl = Termops.map_rel_decl (eta_extern env sigma idset) decl in
    let lname = CAst.make (rel_name decl) in
    match rel_value decl with
    | None -> CLocalAssum ([lname], Default Explicit, rel_type decl)
    | Some def -> CLocalDef (lname, def, Some (rel_type decl))
  in
  map_rel_context env binder_of_decl ctxt |> List.rev
