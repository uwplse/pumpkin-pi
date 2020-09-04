open Constr
open Promotion

(* --- Database for higher lifting --- *)

(*
 * Lookup a lifting along an ornament
 * Arguments: lift_to, lift_back, trm
 *
 * Return None if the lifting does not exist or is not in the current environment
 *)
val lookup_lifting : (constr * constr * constr) -> constr option

(*
 * Store a lifting along an ornament
 * Order of arguments: lift_to, lift_back, trm, lifted_trm
 *)
val save_lifting : (constr * constr * constr) -> constr -> unit

(* --- Database for global opaque liftings --- *)

(*
 * Lookup if a lifting is globally opaque
 * Arguments: lift_to, lift_back, trm
 *)
val lookup_opaque : (constr * constr * constr) -> bool

(*
 * Store an opaque lifting
 * Also saves it as a lifting
 * Order of arguments: lift_to, lift_back, trm
 *)
val save_opaque : (constr * constr * constr) -> unit

(*
 * Remove an opaque lifting
 * Also removes it from liftings
 * Order of arguments: lift_to, lift_back, trm
 *)
val remove_opaque : (constr * constr * constr) -> unit
                                                             
(* --- Temporary cache of constants --- *)

type temporary_cache

(*
 * Initialize the local cache
 *)
val initialize_local_cache : unit -> temporary_cache

(*
 * Check whether a constant is in the local cache
 *)
val is_locally_cached : temporary_cache -> types -> bool

(*
 * Lookup a value in the local cache
 *)
val lookup_local_cache : temporary_cache -> types -> types

(*
 * Add a value to the local cache
 *)
val cache_local : temporary_cache -> types -> types -> unit

(* --- Database of ornaments --- *)

(*
 * Lookup an ornament between two types
 * Arguments: typ1, typ2
 * Order of return values: typ1_to_typ2, typ2_to_typ1, kind of ornament
 *
 * Return None if the ornament does not exist or is not in the current
 * environment
 *)
val lookup_ornament :
  (types * types) -> (constr * constr * kind_of_orn) option

(*
 * Store an ornament between two types, given the function and its inverse
 * Order of arguments: typ1, typ2, typ1_to_typ2, typ2_to_typ1
 *)
val save_ornament :
  (types * types) -> (constr * constr * kind_of_orn) -> unit

(* --- Database of configuration --- *)

(*
 * Lookup DepConstr, DepElim, Eta, and Iota
 * Arguments: orn_o, orn_n
 * Order of return values: dep_constrs, dep_elims, etas, iotas 
 * (for now, just two of these, since this is work in progress)
 *
 * Return None if the configuration does not exist or is not in the current
 * environment
 *)
val lookup_config :
  (types * types) ->
  ((constr array * constr array) *
   (constr * constr) *
   (constr * constr) *
   (constr array * constr array)) option

(*
 * Store DepConstr, DepElim, Eta, and Iota
 *)
val save_dep_constrs : (types * types) -> (constr array * constr array) -> unit
val save_dep_elim : (types * types) -> (constr * constr) -> unit
val save_eta : (types * types) -> (constr * constr) -> unit
val save_iota : (types * types) -> (constr array * constr array) -> unit
