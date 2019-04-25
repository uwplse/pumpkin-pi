open Constr
open Names
open Globnames
open Coqterms
open Lifting
open Caching
open Search
open Lift
open Desugar
open Unpack
open Utilities
open Pp
open Printer
open Ltac_plugin
open Coherence
open Equivalence (* TODO clean *)

(* --- Options for DEVOID --- *)

       
(*
 * Prove the coherence property of the algebraic promotion isomorphism
 *)
val is_search_coh : unit -> bool

(*
 * Prove section and retraction for the algebraic promotion isomorphism
 *)
val is_search_equiv : unit -> bool
