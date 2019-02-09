open Names
open Environ
open Evd
open Constr
open Declarations
open Coqterms

type global_substitution = global_reference Globmap.t

(*
 * Translate the given term into an equivalent, bisimulative (i.e., homomorpic
 * reduction behavior) version using eliminators instead of match or fix
 * expressions.
 *
 * Mutual recursion and co-recursion are not supported.
 *)
val desugar_term : env -> evar_map ref -> global_substitution -> constr -> constr

(*
 * Desugar the body term of a constant and define it in the global environment
 * as the given identifier.
 *)
val desugar_constant : global_substitution -> Id.t -> constant_body -> Constant.t

(*
 * Desugar the body structure of a module and define it in the global environment
 * as a new module by the given identifier.
 *)
val desugar_module : global_substitution ref -> Id.t -> module_body -> ModPath.t
