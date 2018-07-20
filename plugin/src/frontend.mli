open Constrexpr
open Constr
open Names
open Environ

type ornamental_action = env -> Evd.evar_map -> constr -> constr -> constr -> constr * constr option
type ornamental_command = Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(* Identify an algebraic ornament between two types and define its conversion functions  *)
val find_ornament : Id.t -> constr_expr -> constr_expr -> unit
                                                            
(* Core lifting algorithm *)
val lift_by_ornament2 : ornamental_action

(* Transform an ornamental action into an ornamental command *)
val make_ornamental_command : ornamental_action -> bool -> ornamental_command
