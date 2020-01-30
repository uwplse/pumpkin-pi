open Lifting
open Constr
open Environ
open Hofs
open Evd
open Stateutils
open Caching

(*
 * Lifting configuration
 *)

(* --- Datatype --- *)
       
(*
 * Lifting configuration, along with the types A and B,
 * rules for constructors and projections that are configurable by equivalence,
 * a cache for constants encountered as the algorithm traverses,
 * and a cache for the constructor rules that refolding determines.
 *)
type lift_config =
  {
    l : lifting;
    typs : types * types;
    constr_rules : types array;
    proj_rules : types array;
    optimize_proj_packed_rules : (constr * (lift_config -> env -> constr -> constr array -> (lift_config, constr) transformer_with_env -> evar_map -> types state)) list; (* TODO clean type *)
    cache : temporary_cache;
    opaques : temporary_cache
  }

(* --- Auxiliary functions about configuration --- *)

(*
 * Check opaqueness using either local or global cache
 *)
val is_opaque : lift_config -> constr -> bool
    
(*
 * Configurable caching of constants
 *)
val smart_cache : lift_config -> constr -> constr -> unit

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

