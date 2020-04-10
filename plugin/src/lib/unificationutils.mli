open Environ
open Evd
open Constr
open Stateutils

(*
 * Utilities for unification
 *)

(*
 * Make n new evars of any type
 *)
val mk_n_evars :
  int -> env -> evar_map -> (constr list) state

(*
 * Unification
 *)
val unify :
  env -> constr -> constr -> evar_map -> bool state

(*
 * Unify the first two terms and then force evar resolution
 * Return None if cannot unify or cannot resolve evars
 *)
val unify_resolve_evars :
  env -> constr -> constr -> evar_map -> ((constr * constr) option) state

