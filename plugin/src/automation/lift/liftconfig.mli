open Lifting
open Constr
open Environ
open Evd
open Stateutils
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

type lift_config

(* --- Initialization --- *)

val initialize_lift_config :
  env ->
  lifting ->
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

(* --- Eta, iota, and coherence (for preserving definitional equalities) --- *)

(*
 * Get the cached lifted eta expansion function
 *)
val get_lifted_eta : lift_config -> constr

(*
 * Check if a term applies some projection
 *)
val is_proj :
  lift_config ->
  env ->
  constr ->
  evar_map ->
  (* proj, args, trm_eta *)
  ((constr * constr list * constr) option) state

(*
 * Check if a term may apply the eta expansion function,
 * but don't bother checking the type
 *)
val may_apply_eta : lift_config -> env -> constr -> bool

(*
 * Check if the term applies the eta expansion identity function
 * If so, return the the arguments
 *)
val applies_eta :
  lift_config ->
  env ->
  constr ->
  evar_map ->
  ((constr list) option) state
                         
(*
 * Iota rules
 *)
val get_iota : lift_config -> constr array
val get_lifted_iota : lift_config -> constr array

(*
 * Check if the term applies Iota
 * If so, return the the arguments
 *)
val applies_iota :
  lift_config ->
  env ->
  constr ->
  evar_map ->
  ((int * constr list) option) state
              
(* --- Constructors and eliminators --- *)

(*
 * Get DepConstr
 *)
val get_constrs : lift_config -> constr array
val get_lifted_constrs : lift_config -> constr array

(*
 * Get DepElim
 *)
val get_dep_elim : lift_config -> types
val get_lifted_dep_elim : lift_config -> types

(*
 * Check if the term applies the eta expansion function
 * If so, return the the constructor index, arguments, and whether to treat
 * the constructor as opaque when lifting recursively
 *)
val applies_constr_eta :
  lift_config ->
  env ->
  constr ->
  evar_map ->
  ((int * (constr list)) option) state

(*
 * Check if the term applies DepElim
 * If so return the eta-expanded term and the arguments
 *)
val applies_elim :
  lift_config ->
  env ->
  constr ->
  evar_map ->
  ((constr option * (constr list)) option) state

(* --- Custom simplification --- *)
                                     
(*
 * Custom reduction functions for lifted eta and coherence,
 * for efficiency and to ensure termination. For example, this may
 * simplify projections of existentials.
 *)
val reduce_lifted_eta : lift_config -> reducer
val reduce_coh : lift_config -> reducer
val reduce_constr_app : lift_config -> reducer
val reduce_lifted_elim : lift_config -> reducer

(*
 * Determine if we can be smarter than Coq and simplify earlier
 * If yes, return how
 * Otherwise, return None
 *)
val can_reduce_now : lift_config -> env -> constr -> reducer option

(* --- Modifying the configuration --- *)

val reverse : lift_config -> lift_config
val zoom : env -> lift_config -> lift_config
