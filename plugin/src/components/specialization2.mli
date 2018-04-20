(*
 * Experimental syntactic lifting (application and reduction at once)
 *)

open Environ
open Evd
open Lifting
open Term

val lift : env -> evar_map -> lifting -> types -> (types * types option)
