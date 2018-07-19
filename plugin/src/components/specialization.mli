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
 * This lifts the induction principle.
 *
 * The old application and meta-reduction steps were just hacks to accomplish
 * this. So they did this work, but also a lot more work.
 * Accordingly, when this is done, we'll remove the old application
 * and meta-reduction steps.
 * When we do that, the interface for this will also go away, since it will
 * be purely internal.
 *)
val lift_induction_principle :
  env ->
  evar_map ->
  lifting ->
  types ->
  types

(*
 * This lifts a construction.
 *
 * Basically, this moves the refolding part of the algorithm earlier on,
 * so that it doesn't get confused by other functions inside of the
 * construction. Then it applies the derived rules to lift a consruction.
 * Eventually this will be internal when we remove the old buggy code,
 * but for now it's here for testing. Also, eventually we'll cache these,
 * once we know what they look like, so we only have to do it once for each
 * ornament and constructor pair.
 *)
val lift_construction :
  env ->
  evar_map ->
  lifting ->
  types ->
  types


(*
 * Reduce an application of an indexing ornament
 *)
val internalize :
  env ->
  evar_map ->
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

(*
 * Lift a proof along lifted functions it refers to
 *)
val do_lift_core :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* reduced term *)
  (types * types option) (* higher lifting and optional indexing proof *)
