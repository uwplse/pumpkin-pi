open Globnames
open Environ
open Constr
open Evd

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
 * The kind of ornament that is stored
 *)
type kind_of_orn = Algebraic | CurryRecord

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
