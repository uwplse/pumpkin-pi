open Constrexpr
open Names
open Ltac_plugin

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
val lift_by_ornament : ?suffix:bool -> ?ignores:Libnames.reference list -> Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(*
 * Unpack sigma types in the functional signature of a constant.
 *
 * This transformation assumes that the input constant was generated by
 * ornamental lifting.
 *)
val do_unpack_constant : Id.t -> Libnames.reference -> unit

