(*
 * Abstraction specific to ornamental search
 *)

open Term
open Environ
open Evd

(* 
 * Given an application and the index of the argument, abstract by the argument 
 *)
val abstract_arg : env -> evar_map -> int -> types -> types

