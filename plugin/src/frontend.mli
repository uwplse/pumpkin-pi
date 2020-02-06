open Constrexpr
open Names

(*
 * Identify an algebraic ornament between two types
 * Define the components of the corresponding equivalence
 * If the appropriate option is set, prove that these form an equivalence
 *)
val find_ornament : Id.t option -> constr_expr -> constr_expr -> unit          

(*
 * Save a user-supplied ornament between two types
 *)
val save_ornament :
  constr_expr -> constr_expr -> constr_expr -> constr_expr -> unit
                                                                   
(*
 * Lift the supplied function along an ornament between the supplied types
 * Define the lifted version
 *)
val lift_by_ornament : ?suffix:bool -> ?opaques:Libnames.reference list -> Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(*
  * Lift each module element (constant and inductive definitions) along the given
  * ornament, defining a new module with all the transformed module elements.
  *)
val lift_module_by_ornament : Id.t -> constr_expr -> constr_expr -> Libnames.reference -> unit

(*
 * Unpack sigma types in the functional signature of a constant.
 *
 * This transformation assumes that the input constant was generated by
 * ornamental lifting.
 *)
val do_unpack_constant : Id.t -> Libnames.reference -> unit

(*
 * Add terms to or remove terms from the globally opaque lifting cache
 * at a particular ornament
 *)
val add_lifting_opaques :
  constr_expr -> constr_expr -> Libnames.reference list -> unit
val remove_lifting_opaques :
  constr_expr -> constr_expr ->  Libnames.reference list -> unit
