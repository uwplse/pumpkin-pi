open Environ
open Evd
open Constr

(*
 * Replace each match expression within the given term with a definitionally
 * equal application of an eliminator, returning an updated evar_map.
 * Fix and co-fix expressions are not supported and will fail.
 *)
val desugar_matches : env -> evar_map -> types -> evar_map * types
