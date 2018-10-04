(*
 * Core lifting algorithm from Section 5.1.2
 *)

open Names
open Constr
open Environ
open Evd
open Lifting

(*
 * Lift a term along an ornament
 *)
val do_lift_term :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* unlifted term *)
  types (* lifted term *)

(*
 * Lift a constant along an ornament
 *)
val do_lift_defn :
  env ->
  evar_map ->
  lifting -> (* lifting configuration *)
  types -> (* unlifted constant (defined function) *)
  types (* lifted function *)

val do_lift_ind :
  env ->
  evar_map ->
  Id.t ->
  string ->
  lifting ->
  inductive ->
  inductive
