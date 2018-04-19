(*
 * A generalized version of the factoring component from PUMPKIN PATCH
 *)

open Term
open Environ
open Evd
open Lifting

(* --- Type-level factoring --- *)

val factor_product : types -> types list
       
(* --- Non-dependent factoring --- *)       

type factors = (env * types) list
       
val factor_term : types -> env -> evar_map -> types -> factors
val reconstruct_factors : factors -> types list
val apply_factors : factors -> types
val debug_factors : factors -> string -> unit
       
(* --- Dependent factoring --- *)

type factor_tree = Unit | Factor of (env * types) * factor_tree list
                                                         
val factor_term_dep : types -> env -> evar_map -> types -> factor_tree
val debug_factors_dep : factor_tree -> string -> unit

(* --- Factoring lifted but not reduced functions --- *)

(* 
 * Factor a lifted but not yet reduced function
 * Return both the factor tree and the index of the assumption
 *)
val factor_ornamented :
  promotion -> env -> evar_map -> types -> (int * factor_tree)
