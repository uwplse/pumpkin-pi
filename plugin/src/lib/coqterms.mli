(*
 * Coq term and environment management
 *)

open Environ
open Term
open Evd
open Constrexpr
open Names
open Declarations
       
module CRD = Context.Rel.Declaration

(* --- Constants --- *)
                                     
val sigT : types
val existT : types
val sigT_rect : types
val projT1 : types
val projT2 : types

(* --- Representations --- *)

(*
 * Intern a term (for now, ignore the resulting evar_map)
 *)
val intern : env -> evar_map -> constr_expr -> types

(*
 * Extern a term
 *)
val extern : env -> evar_map -> types -> constr_expr

(* --- Constructing terms --- *)

(*
 * mkApp with a list (instead of an array) of arguments
 *)
val mkAppl : (types * types list) -> types

(*
 * Ornament between products and lambdas, without changing anything else
 *)
val prod_to_lambda : types -> types
val lambda_to_prod : types -> types

(* --- Inductive types and their eliminators --- *)

(*
 * Fail if the inductive type is mutually inductive or coinductive
 *)
val check_inductive_supported : mutual_inductive_body -> unit

(*
 * Determine if a term represents an inductive eliminator
 * For now, this is a naive syntactic check
 *)
val is_elim : env -> types -> bool

(*
 * Get the type of an inductive type
 *)
val type_of_inductive : env -> int -> mutual_inductive_body -> types

(*
 * Lookup the eliminator over the type sort
 *)
val type_eliminator : env -> inductive -> types
                                                                 
(* --- Environments --- *)

(*
 * Return a list of all indexes in env as ints, starting with 1
 *)
val all_rel_indexes : env -> int list                              

(*
 * Push to an environment
 *)
val push_local : (name * types) -> env -> env
val push_let_in : (name * types * types) -> env -> env

(*
 * Lookup from an environment
 *)
val lookup_definition : env -> types -> types
val unwrap_definition : env -> types -> types

(*
 * Get bindings to push to an environment
 *)
val bindings_for_inductive :
  env -> mutual_inductive_body -> one_inductive_body array -> CRD.t list
val bindings_for_fix : name array -> types array -> CRD.t list
                                                          
(* --- Basic questions about terms --- *)

(*
 * Get the arity of a function or function type
 *)
val arity : types -> int

(* 
 * Check whether a term (second argument) applies a function (first argument)
 * Don't consider terms convertible to the function
 *)
val applies : types -> types -> bool

(*
 * Check whether a term either is exactly a function or applies it
 *)
val is_or_applies : types  -> types -> bool

(* --- Convertibility and types --- *)
                                
(*
 * Type-checking
 * 
 * Current implementation may cause universe leaks, which will just cause 
 * conservative failure of the plugin
 *)
val infer_type : env -> evar_map -> types -> types
                                               
(*
 * Convertibility, ignoring universe constraints
 *)
val convertible : env -> types -> types -> bool

(* --- Zooming and reconstructing --- *)
                    
(*
 * Zoom n deep
 *)
val zoom_n_prod : env -> int -> types -> (env * types)
val zoom_n_lambda : env -> int -> types -> (env * types)

(*
 * Zoom all the way
 *)
val zoom_lambda_term : env -> types -> (env * types)
val zoom_product_type : env -> types -> (env * types)

(* 
 * Projections of zooming
 *)
val zoom_env : (env -> types -> (env * types)) -> env -> types -> env
val zoom_term : (env -> types -> (env * types)) -> env -> types -> types

(* 
 * Reconstruct until n are left
 *)
val reconstruct_lambda_n : env -> types -> int -> types
val reconstruct_product_n : env -> types -> int -> types

(* 
 * Reconstruct fully
 *)
val reconstruct_lambda : env -> types -> types
val reconstruct_product : env -> types -> types

