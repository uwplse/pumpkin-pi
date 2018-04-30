(*
 * Specialization component for ornamental search
 *)

open Term
open Environ
open Evd
open Lifting
open Names

(*
 * Apply an indexing ornament, but don't reduce the result
 *)
val apply_indexing_ornament :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* term to lift *)
  types (* applied term *)

(*
 * Reduce an application of an indexing ornament
 *)
val internalize :
  env ->
  evar_map ->
  Id.t -> (* name of indexer to generate, if applicable *)
  lifting -> (* lifting configuration *)
  types -> (* term to reduce *)
  (types * types option) (* reduced term and optional indexer *)

(*
 * Lift a proof along lifted functions it refers to
 *)
val higher_lift :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* reduced term *)
  (types * types option) (* higher lifting and optional indexing proof *)
