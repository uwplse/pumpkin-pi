(*
 * Differencing for ornamenting inductive types
 *)

open Term
open Environ
open Evd

(* --- Differencing terms --- *)

(* 
 * Check if two terms have the same type, ignoring universe inconsistency
 * Use the closure environments to get the respective types, but
 * use the common environment to check type equality
 *)
val same_type :
  env -> evar_map -> (env * types) -> (env * types) -> bool

(*
 * Returns true if two applications contain have a different
 * argument at the given index, using precise syntactic equality.
 * Return true vacuously if the terms are not applications at all.
 *)
val diff_arg : int -> types -> types -> bool

(* --- Differencing inductive types --- *)
                                                                       
(* 
 * Check if two terms are the same modulo an indexing of an inductive type 
 * The first type argument is the inductive property
 * Both pairs are the old inductive type with the old term,
 * and the new inductive type with the new term
 *)
(*
 * TODO hide eventually
 *)
val same_mod_indexing :
  env -> types -> (types * types) -> (types * types) -> bool

(* --- Indexers --- *)

(* 
 * TODO hide eventually all of these eventually
 *)
                                                          
(*
 * Assuming there is an indexing ornamental relationship between two 
 * eliminators, get the type and location of the new index.
 *
 * If indices depend on earlier types, the types may be dependent;
 * the client needs to shift by the appropriate offset.
 *)
val new_index_type : env -> types -> types -> (int * types)

(*
 * Search for an indexing function that relates two inductive types
 * For example, a list and vector are related via list length
 * TODO clean type 
 *)
val search_for_indexer :
  evar_map ->
  int ->
  types ->
  int ->
  types ->
  (env * types * int * types) ->
  (env * types * int * types) ->
  bool ->
  types option
