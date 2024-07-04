(*
 * Abstraction specific to ornamental search
 *)

open Constr
open Environ
open Evd
open Stateutils

(*
 * Given an application and the index of the argument, abstract by the argument
 *)
val abstract_arg : env -> evar_map -> int -> types -> types state

(* Replace all occurrences of the first term in the second term with Rel 1,
 * lifting de Bruijn indices as needed. The notion of term equality is modulo
 * alpha, casts, application grouping, and universes.
*)
val abstract_subterm : env -> constr -> constr -> constr
