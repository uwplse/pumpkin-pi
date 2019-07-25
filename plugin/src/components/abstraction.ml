(*
 * Abstraction specific to ornamental search
 *)

open Constr
open Debruijn
open Indexing
open Names
open Apputils
open Reducers
       
(*
 * Given an application and the index of the argument, abstract by the argument
 *)
let abstract_arg env evd i typ =
  let arg = get_arg i typ in
  let arg_typ = reduce_type env evd arg in
  let args = reindex i (mkRel 1) (shift_all (unfold_args typ)) in
  mkLambda (Anonymous, arg_typ, mkAppl (first_fun typ, args))

(* Replace all occurrences of the first term in the second term with Rel 1,
 * lifting de Bruijn indices as needed. The notion of term equality is modulo
 * alpha, casts, application grouping, and universes.
*)
let abstract_subterm sub term =
  (* Allocate a binding slot for the abstracted subterm *)
  let sub = Vars.lift 1 sub in
  let term = Vars.lift 1 term in
  let rec surgery (nb, sub) term =
    match eq_constr_head sub term with
    | Some args ->
      mkApp (mkRel (nb + 1), args)
    | None ->
      Constr.map_with_binders
        (fun (nb, sub) -> nb + 1, Vars.lift 1 sub)
        surgery
        (nb, sub)
        term
  in
  surgery (0, sub) term
