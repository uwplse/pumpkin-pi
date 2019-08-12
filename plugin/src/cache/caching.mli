open Globnames
open Environ
open Constr
open Evd

(* --- Database for higher lifting --- *)

(*
 * Register a lifting to the database
 *)
val declare_lifted : global_reference -> global_reference -> unit

(*
 * Search the database for a lifting, returning the reduced version if it exists
 *)
val search_lifted : env -> evar_map -> global_reference -> global_reference option

(*
 * Search the database for a lifting using terms, returning the reduced version
 * if it exists
 *)
val search_lifted_term : env -> evar_map -> types -> types option

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
 * Check if an ornament between two types exists
 *)
val has_ornament : (types * types) -> bool

(*
 * Lookup an ornament between two types
 * Arguments: typ1, typ2
 * Order of return values: typ1_to_typ2, typ2_to_typ1
 *)
val lookup_ornament : (types * types) -> (global_reference * global_reference)

(*
 * Store an ornament between two types, given the function and its inverse
 * Order of arguments: typ1, typ2, typ1_to_typ2, typ2_to_typ1
 *)
val save_ornament : (types * types) -> (global_reference * global_reference) -> unit
