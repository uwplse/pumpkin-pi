open Names
open Constr

val unpack_constant : Environ.env -> Evd.evar_map -> Constant.t -> Evd.evar_map * constr
