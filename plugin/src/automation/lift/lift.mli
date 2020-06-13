(*
 * Core lifting algorithm
 *)

open Names
open Constr
open Environ
open Evd
open Lifting
open Stateutils

(*
 * Lift a constant along an ornament
 *)
val do_lift_defn :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* unlifted constant (defined function) *)
  constr list -> (* constants to treat as opaque *)
  types state (* lifted function *)

val do_lift_ind :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  Id.t ->
  string ->
  inductive ->
  constr list -> (* constants to treat as opaque *)
  bool -> (* whether we're lifting a whole module *)
  inductive (* lifted type and number of constructors for caching *)
