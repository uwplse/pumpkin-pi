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
val lift_by_ornament : ?suffix:bool -> Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(*
 * Translate each fix or match subterm into an equivalent application of an
 * eliminator, defining the new term with the given name.
 *
 * Mutual fix or cofix subterms are not supported.
 *)
val do_desugar_constant : Id.t -> Libnames.reference -> unit

(*
 * Translate fix and match expressions into eliminations, as in
 * desugar_definition, compositionally throughout a whole module.
 *)
val do_desugar_module : Id.t -> Libnames.reference -> unit
