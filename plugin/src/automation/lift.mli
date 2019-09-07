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
 * Lift a term along an ornament
 *)
val do_lift_term :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* unlifted term *)
  types state (* lifted term *)

(*
 * Lift a constant along an ornament
 *)
val do_lift_defn :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* unlifted constant (defined function) *)
  types state (* lifted function *)

val do_lift_ind :
  env ->
  evar_map ->
  Id.t ->
  string ->
  lifting ->
  inductive ->
  inductive (* lifted type and number of constructors for caching *)
