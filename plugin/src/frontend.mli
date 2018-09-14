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
 * Translate every match expression into an equivalent eliminator
 * application, defining the new term with the given name.
 *
 * Currently, fixed-point expressions are _not_ supported.
 *)
val translate_matches : Id.t -> constr_expr -> unit
