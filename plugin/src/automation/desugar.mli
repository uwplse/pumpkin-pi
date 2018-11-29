open Environ
open Evd
open Constr

(*
 * Translate each fix or match subterm into an equivalent application of an
 * eliminator, returning an updated evar_map.
 *
 * Mutual fix or cofix subterms are not supported.
 *)
val desugar_fix_match : env -> evar_map -> constr -> evar_map * constr * types
