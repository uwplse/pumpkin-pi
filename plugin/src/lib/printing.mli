(*
 * Debugging functions from PUMPKIN PATCH
 *)

open Term
open Environ

(* --- Conversion to strings --- *)
       
val term_as_string : env -> types -> string
val env_as_string : env -> string
                             
(* --- Debugging with a descriptor --- *)
                             
val debug_term : env -> types -> string -> unit
val debug_terms : env -> types list -> string -> unit
val debug_env : env -> string -> unit
