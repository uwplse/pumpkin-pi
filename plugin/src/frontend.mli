open Constrexpr
open Names

(*
 * Identify an algebraic ornament between two types
 * Define the components of the corresponding equivalence
 * (Don't prove section and retraction)
 *)
val find_ornament : Id.t option -> constr_expr -> constr_expr -> unit

(*
 * Lift the supplied function along the supplied ornament
 * Define the lifted version
 *)
val lift_by_ornament : Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(*
 * Lift the designated inductive type along the supplied ornament and declare the
 * lifted version using the given suffix for type and constructor names.
 *)
val lift_inductive_by_ornament : string -> constr_expr -> constr_expr -> inductive -> unit
