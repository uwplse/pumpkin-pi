open Names
open Constr
open Constrexpr

(*
 * Externalize a variant of the well-typed term, in which every variable with
 * sigma type is eta-expanded (e.g., `x` --> `existT (projT1 x) (projT2 x)`),
 * unless eta-expansion is already available definitionally (e.g.,
 * `x := existT y z` in context or environment). Moreover, every case analysis
 * of a form with a field of sigma type is extended to pattern-match each field
 * of sigma type, therefore inducing a definitional eta-expansion.
 *
 * The purpose of this function is to "eta-externalize" an eliminator of a
 * lifted inductive type and then internalize (type-check) the resulting
 * expression to serve as the lifting of the corresponding eliminator of the
 * base type.
 *)
val eta_extern : Environ.env -> Evd.evar_map -> Id.Set.t -> constr -> constr_expr
