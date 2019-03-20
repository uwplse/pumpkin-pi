open Names
open Constr

val unpack_constant : Environ.env -> Evd.evar_map ref -> Constant.t -> constr
