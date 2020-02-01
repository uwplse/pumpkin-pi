open Lifting
open Constr
open Environ
open Hofs
open Evd
open Stateutils
open Caching
open Reducers

(*
 * Lifting configuration: Includes the lifting, types, and cached rules
 * for optimizations, as well as interfaces to ask questions about
 * the configuration and some initialization code.
 *
 * This is where lifting constructors and projections live, since those
 * are configured ahead of time. Eventually, the bulk of lifting eliminators
 * may live here as well.
 *)

(* --- Datatype --- *)
       
(*
 * Lifting configuration, along with the types A and B,
 * rules for constructors and projections that are configurable by equivalence,
 * a cache for constants encountered as the algorithm traverses,
 * and a cache for the constructor rules that refolding determines.
 *)
type lift_config

(* --- Initialization --- *)

val initialize_lift_config :
  env ->
  lifting ->
  (types * types) -> (* A, B *)
  constr list -> (* opaques *)
  evar_map ->
  lift_config state

(* --- Recover or set the lifting --- *)

val get_lifting : lift_config -> lifting

(* --- Caching --- *)

(*
 * Check opaqueness using either local or global cache
 *)
val is_opaque : lift_config -> constr -> bool
    
(*
 * Configurable caching of constants
 *)
val smart_cache : lift_config -> constr -> constr -> unit

(*
 * Check if something is in the local cache
 *)
val is_cached : lift_config -> constr -> bool

(*
 * Lookup something from the local cache
 *)
val lookup_cache : lift_config -> constr -> constr

(* --- Questions about types A and B --- *)

val get_types : lift_config -> types * types

(*
 * Determine if the supplied type is the type we are lifting from
 * Return the arguments if true
 *)
val is_from :
  lift_config -> env -> types -> evar_map -> ((constr list) option) state

(*
 * Like is_from, but just assume it's the right type and get the arguments
 *)
val from_args :
  lift_config -> env -> types -> evar_map -> (constr list) state

(*
 * Like is_from, but taking a term and checking on its type
 *)
val type_is_from :
  lift_config -> env -> constr -> evar_map -> ((constr list) option) state

(*
 * Like type_is_from, but just assume it's the right type and get the arguments
 *)
val type_from_args :
  lift_config -> env -> constr -> evar_map -> (constr list) state
                                                            
(*
 * Get the map of projections of the types for the lifting
 *)
val get_proj_map :
  lift_config -> (constr * constr) list

(*
 * Get the cached lifted constructors of A (which construct B)
 *)
val get_lifted_constrs :
  lift_config -> constr array

(* --- Smart simplification --- *)

(*
 * Return true if a term is packed
 *)
val is_packed : lift_config -> constr -> bool

(*
 * Determine if we can be smarter than Coq and simplify earlier
 * If yes, return how
 * Otherwise, return None
 *)
val can_reduce_now :
  lift_config -> constr -> reducer option

(* --- Modifying the configuration --- *)

val reverse : lift_config -> lift_config
val zoom : lift_config -> lift_config
