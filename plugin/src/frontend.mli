open Constrexpr
open Constr
open Names
open Environ

type ornamental_action = env -> Evd.evar_map -> constr -> constr -> constr -> constr * constr option
type ornamental_command = Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(* Identify an algebraic ornament between two types and define its conversion functions  *)
val find_ornament : Id.t -> constr_expr -> constr_expr -> unit

(* TODO temporary: given just an application of the IP, lift it *)
val lift_induction : ornamental_action

(* TODO temporary: given just a construction, lift it *)
val lift_constructor : ornamental_action
                                                            
(* Apply an ornament without meta-reduction *)
val apply_ornament : ornamental_action

(* Meta-reduce a ornamental lifting *)
val reduce_ornament : ornamental_action

(* Post-facto modularization of a meta-reduced ornamental lifting/application *)
val modularize_ornament : ornamental_action

(* Perform application, meta-reduction, and modularization all in sequence *)
val lift_by_ornament : ornamental_action

(* Core lifting algorithm *)
val lift_by_ornament2 : ornamental_action

(* Transform an ornamental action into an ornamental command *)
val make_ornamental_command : ornamental_action -> bool -> ornamental_command
