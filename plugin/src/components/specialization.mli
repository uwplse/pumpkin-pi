(*
 * Specialization component for ornamental search
 *)

open Term
open Environ
open Evd
open Lifting

(*
 * Apply an indexing ornament, but don't reduce the result
 *)
val apply_indexing_ornament : env -> evar_map -> lifting -> types -> types
