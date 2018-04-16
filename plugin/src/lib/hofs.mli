(*
 * Higher-order functions on terms
 *)

open Term
open Environ
open Debruijn
open Coqterms

(* --- Conditional mapping --- *)
       
(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_env_if :
  (env -> 'a -> types -> bool) ->
  (env -> 'a -> types -> types) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  types

(*
 * Like map_term_env_if, but use an empty environment
 *)
val map_term_if :
  ('a -> types -> bool) ->
  ('a -> types -> types) ->
  ('a -> 'a) ->
  'a ->
  types ->
  types

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function lazily
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
val map_term_env_if_lazy :
  (env -> 'a -> types -> bool) ->
  (env -> 'a -> types -> types) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  types

(*
 * Like map_term_env_if_lazy, but use the empty environment
 *)
val map_term_if_lazy :
  ('a -> types -> bool) ->
  ('a -> types -> types) ->
  ('a -> 'a) ->
  'a ->
  types ->
  types

(* --- Propositions --- *)
    
(*
 * Check if a proposition is ever true over some subterm of a term
 * Return true immediately, if it is
 * In other words, return true if and only if map_term_env_if would
 * apply the function f
 *)
val exists_subterm_env :
  (env -> 'a -> types -> bool) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  bool

(* 
 * Like exists_subterm_env, but use the empty environment 
 *)
val exists_subterm :
  ('a -> types -> bool) ->
  ('a -> 'a) ->
  'a ->
  types ->
  bool

(* --- Substitution --- *)

(* 
 * Map a substitution over subterms of a term at the highest level possible
 * Apply the substitution only when the proposition is true
 *)
val all_substs :
  (env -> types -> types -> bool) ->
  env ->
  (types * types) ->
  types ->
  types

    
