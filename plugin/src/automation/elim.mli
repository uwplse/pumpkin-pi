open Names
open Constr
open Constrexpr

val eta_extern : Environ.env -> Evd.evar_map -> Id.Set.t -> constr -> constr_expr
