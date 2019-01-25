open Names
open Environ
open Evd
open Constr
open Coqterms

(*
 * Translate the given term into an equivalent, bisimulative (i.e., homomorpic
 * reduction behavior) version using eliminators instead of match or fix
 * expressions.
 *
 * Mutual recursion and co-recursion are not supported.
 *)
val desugar_term : env -> evar_map -> Constant.t Constmap.t -> constr -> evar_map * constr * types
