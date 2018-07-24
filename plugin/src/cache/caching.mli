open Environ
open Constr
open Evd

(* --- Database for higher lifting --- *)

(*
 * Register a lifting to the database
 *)
val declare_lifted : evar_map -> types -> types -> unit

(*
 * Search the database for a lifting (return the reduced version if it exists)
 *)                                       
val search_lifted : env -> types -> types option
