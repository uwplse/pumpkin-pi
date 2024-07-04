(*
 * Dependent elimination for inductive families over sigma-packed indices.
 *)

open Util
open Constr
open Nameops
open Declarations
open Apputils
open Sigmautils
open Contextutils

(*
 * Given a relative context quantifying an inductive family's indices, assemble
 * the list of `constr` arguments to supply the inductive family's type former,
 * such that the argument for any index of sigma type is its eta-expansion.
 *
 * As an example, an `index_ctxt` of `[("x" : bool); ("y" : sigT vector)]`
 * becomes `[@1; existT vector (projT1 @2) (projT2 @2)]`, denoting each `Rel i`
 * as `@i`. Notice how each argument lives directly underneath `index_ctxt`.
 *
 * NOTE: Assumes that all parameter's of the inductive family are externally
 * quantified (i.e., above `index_ctxt`) and are thus effectively fixed.
 *
 * NOTE: Requires that the list of index arguments be used directly under the
 * local bindings (i.e., quantifiers) of `index_ctxt`, due to deBruijn indexing.
 *)
let eta_expand_indices index_ctxt =
  List.map_i
    (fun k (_, typ) ->
       let typ = Vars.lift k typ in
       if applies sigT typ then eta_sigT (mkRel k) typ else mkRel k)
    1
    index_ctxt

(*
 * Given an "arity" `typ` w.r.t. an inductive family over `nindex` indices,
 * substitute each bound index (i.e., `Rel i` for `i` s.t. `1 <= i <= nindex`)
 * with its eta-expansion w.r.t. the sigma type `sigT`, if applicable.
 *
 * The `nindex` quantifiers, which prefix the arity `typ`, are opened for the
 * above substitution and then closed in the result.
 *
 * NOTE: An "arity", in the context of inductive families, is a type quantifying
 * all an inductive family's indices (in order), followed by some codomain type.
 * For example, `forall (n : nat), Type` is an arity w.r.t. `vector`.
 *)
let eta_expand_arity nindex typ =
  let index_ctxt, body = Term.decompose_prod_n nindex typ in
  let indices = eta_expand_indices index_ctxt in
  Vars.liftn nindex (nindex + 1) body |> Vars.substl indices |>
  Term.compose_prod index_ctxt

(*
 * Given the underlying eliminator's motive type, construct the motive term for
 * the wrapped eliminator to apply to that same underlying eliminator.
 *
 * This motive term is an eta expansion of that quantified, except that each
 * index to the inductive family is eliminated via `sigT_rect`, if applicable.
 *
 * By wrapping the quantified motive in this way, the user may (ultimately)
 * supply, to the wrapped eliminator, a motive term that relies on eta expansion
 * for sigma types.
 *
 * NOTE: Assumes that the result term lives underneath the wrapped eliminator's
 * full series of quantifiers (i.e., parameters, then motive, then indices).
 *)
let eta_guard_motive ncons nindex typ =
  let rec aux i typ =
    if i == nindex then
      let motive = mkRel (nindex + nindex + ncons + 1) in
      let indices = Termops.rel_vect 0 nindex in
      mkApp (motive, indices)
    else
      let name, domain, codomain = destProd typ in
      let body = aux (i + 1) codomain in
      if applies sigT domain then
        let body =
          let domain = Vars.lift 2 domain in
          let { index_type; packer } = dest_sigT domain in
          mkLetIn
            (name,
             mkApp (existT, [|index_type; packer; mkRel 2; mkRel 1|]),
             domain,
             Vars.liftn 2 2 body)
        in
        let { index_type; packer } = dest_sigT domain in
        let packed_type = Reduction.beta_app (Vars.lift 1 packer) (mkRel 1) in
        let name_1 = Name.map (fun id -> add_suffix id "_1") (Context.binder_name name) in
        let name_2 = Name.map (fun id -> add_suffix id "_2") (Context.binder_name name) in
        mkApp
          (sigT_rect,
           [|index_type; packer;
             mkLambda (name, domain, codomain);
             mkLambda (get_rel_ctx_name name_1, index_type,
                       mkLambda (get_rel_ctx_name name_2, packed_type, body))|])
      else
        mkLambda ( name, domain, body)
  in
  Vars.lift (ncons + nindex + 1) typ |> aux 0

(*
 * Construct a wrapper term around an inductive family's (given as a
 * `mind_specif`) eliminator (given as a constant `constr` reference with its
 * `types`), returning both the wrapper `constr` and its "natural" `types`.
 *
 * The wrapper term resembles an eta-expansion of the underlying eliminator,
 * except that the applied motive is also an eta-expansion in which any index
 * of sigma type is definitionally eta-expanded. The net effect is that the
 * wrapped eliminator accepts a motive expecting definitional eta-expansion
 * of indices with sigma type.
 *
 * The wrapped eliminator can be understood as enabling implicit dependent
 * elimination for the inductive family w.r.t. its indices of sigma type.
 * Since the canonical form of a sigma type is irrefutable, this (fairly)
 * simple instance of dependent elimination does not need to rely on any
 * extra axiom or any special (proof of a) property like UIP.
 *
 * NOTE: Using the returned `types` is not strictly necessary, but it is much
 * more readable than that inferred by type-checking.
 *)
let eta_guard_eliminator (mind_body, ind_body) elim_term elim_type =
  (* NOTE: The control flow here follows the structure of `elim_type`. *)
  let nparam = mind_body.mind_nparams in
  let nindex = ind_body.mind_nrealargs in
  let ncons = Array.length ind_body.mind_consnames in
  (* Pull off the `nparam` quantifiers for the inductive family's parameters. *)
  let param_ctxt, typ = Term.decompose_prod_n nparam elim_type in
  (* Pull off the quantifier for the elimination motive. *)
  let motive_name, motive_type, typ = destProd typ in
  (* Pull off the `ncons` quantifiers for the constructor recurrences. *)
  let recur_ctxt, typ = Term.decompose_prod_n ncons typ in
  (* Eta-expand any indices of sigma type found in the elimination arity. *)
  let elim_arity = eta_expand_arity nindex typ in
  (* Pull of the `nindex` quantifiers for the inductive family's indices. *)
  let index_ctxt, typ = Term.decompose_prod_n nindex elim_arity in
  (* Assemble the full series of quantifiers for the wrapped eliminator. *)
  let context =
    (* Eta-expand any indices of sigma type found in the motive arity. *)
    let motive_decl = (motive_name, eta_expand_arity nindex motive_type) in
    List.concat [index_ctxt; recur_ctxt; [motive_decl]; param_ctxt]
  in
  (* Assemble the full series of arguments for the underlying eliminator. *)
  let arguments =
    (* Collect the `nparam` parameters bound in `context`. *)
    let params = Termops.rel_vect (nindex + ncons + 1) nparam in
    (* Construct a motive term wrapping that bound in `context`. *)
    let motive = eta_guard_motive ncons nindex motive_type in
    (* Collect the `ncons` constructor recurrences bound in `context`. *)
    let recurs = Termops.rel_vect nindex ncons in
    (* Assemble the `nindex` indices bound in `context`, each eta-expanded if sigma type. *)
    let indices = eta_expand_indices index_ctxt |> Array.rev_of_list in
    Array.concat [params; [|motive|]; recurs; indices]
  in
  (* Close the wrapped eliminator term and type over the `context` of quantifiers. *)
  Term.compose_lam context (mkApp (elim_term, arguments)),
  Term.compose_prod context typ
