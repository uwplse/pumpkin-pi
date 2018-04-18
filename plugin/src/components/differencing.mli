(*
 * Differencing for ornamenting inductive types
 *)

open Term
open Environ
open Evd

(* --- Indexing ornaments --- *)

(* 
 * TODO comment
 * TODO clean type
 * TODO erase interface if not accessed from outside
 * TODO clean implementations of everything under this line
 *)
val search_orn_index :
  env ->
  evar_map ->
  int ->
  Names.Id.t ->
  (types * int) ->
  (types * int) ->
  bool ->
  (int option * types option * types)

