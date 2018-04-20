(*
 * Experimental syntactic lifting (application and reduction at once)
 *)

open Environ
open Evd
open Lifting
open Term

let lift env evd l trm =
  (trm, None) (* TODO *)
