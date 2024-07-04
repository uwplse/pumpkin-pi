(*
 * Abstraction specific to ornamental search
 *)

open Constr
open Debruijn
open Indexing
open Names
open Apputils
open Reducers
open Contextutils       

(*
 * Given an application and the index of the argument, abstract by the argument
 *)
let abstract_arg env sigma i typ =
  let arg = get_arg i typ in
  let sigma, arg_typ = reduce_type env sigma arg in
  let args = reindex i (mkRel 1) (shift_all (unfold_args typ)) in
  sigma, mkLambda (get_rel_ctx_name Anonymous, arg_typ, mkAppl (first_fun typ, args))

(* Replace all occurrences of the first term in the second term with Rel 1,
 * lifting de Bruijn indices as needed. The notion of term equality is modulo
 * alpha, casts, application grouping, and universes.
*)
let abstract_subterm sub term =
  let rec surgery (nb, sub) term =
    match eq_constr_head sub term with
    | Some args ->
      mkApp (mkRel (nb + 1), args)
    | None ->
      Constr.map_with_binders
        (fun (nb, sub) -> nb + 1, shift sub)
        surgery
        (nb, sub)
        term
  in surgery (0, shift sub) (shift term)
