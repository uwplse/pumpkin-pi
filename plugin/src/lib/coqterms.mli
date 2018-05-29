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

(*
 * Define a new Coq term
 *)
val define_term : Id.t -> evar_map -> types -> unit

(* --- Constructing terms --- *)

(*
 * mkApp with a list (instead of an array) of arguments
 *)
val mkAppl : (types * types list) -> types

(* 
 * Define a constant from an ID in the current path
 *)
val make_constant: Id.t -> types

(*
 * Ornament between products and lambdas, without changing anything else
 *)
val prod_to_lambda : types -> types
val lambda_to_prod : types -> types

(*
 * An application of existT
 *)
type existT_app =
  {
    index_type : types;
    packer : types;
    index : types;
    unpacked : types;
  }

(*
 * Convert between a term and an existT_app
 *)
val pack_existT : existT_app -> types
val dest_existT : types -> existT_app

(*
 * An application of sigT
 *)
type sigT_app =
  {
    index_type : types;
    packer : types;
  }

(*
 * Convert between a term and a sigT_app
 *)
val pack_sigT : sigT_app -> types
val dest_sigT : types -> sigT_app 

(*
 * An application of sigT_rect
 *)
type sigT_elim =
  {
    to_elim : sigT_app;
    packed_type : types;
    unpacked : types;
    arg : types;
  }
                                    
(*
 * Convert between a term and a sigT_elim
 *)
val elim_sigT : sigT_elim -> types
val dest_sigT_elim : types -> sigT_elim

(*
 * Left projection of a sigma type given a sigma type and term of that type
 *)
val project_index : sigT_app -> types -> types

(*
 * Right projection of a sigma type given a sigma type and term of that type
 *)
val project_value : sigT_app -> types -> types

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

(*
 * Applications of eliminators
 *)
type elim_app =
  {
    elim : types;
    pms : types list;
    p : types;
    cs : types list;
    final_args : types list;
  }
                                            
val apply_eliminator : elim_app -> types
val deconstruct_eliminator : env-> evar_map -> types -> elim_app
  
(* --- Environments --- *)

(*
 * Return a list of all indexes in env as ints, starting with 1
 *)
val all_rel_indexes : env -> int list

(*
 * Return a list of relative indexes, from highest to lowest, of size n
 *)
val mk_n_rels : int -> types list

(*
 * Push to an environment
 *)
val push_local : (name * types) -> env -> env
val push_let_in : (name * types * types) -> env -> env

(*
 * Lookup from an environment
 *)
val lookup_pop : int -> env -> (env * CRD.t list)
val lookup_definition : env -> types -> types
val unwrap_definition : env -> types -> types

(*
 * Get bindings to push to an environment
 *)
val bindings_for_inductive :
  env -> mutual_inductive_body -> one_inductive_body array -> CRD.t list
val bindings_for_fix : name array -> types array -> CRD.t list

(*
 * Offset between an environment and an index, or two environments, respectively
 *)
val offset : env -> int -> int
val offset2 : env -> env -> int
                                                          
(* --- Basic questions about terms --- *)

(*
 * Get the arity of a function or function type
 *)
val arity : types -> int

(* 
 * Check whether a term (second argument) applies a function (first argument)
 * Don't consider terms convertible to the function
 *
 * In the plural version, check for both the second and third terms
 *)
val applies : types -> types -> bool
val apply : types -> types -> types -> bool

(*
 * Check whether a term either is exactly a function or applies it
 *
 * In the plural version, check for both the second and the third terms
 *)
val is_or_applies : types  -> types -> bool
val are_or_apply : types -> types -> types -> bool

(* --- Convertibility, reduction, and types --- *)
                                
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

(*
 * Reduction
 *)
val reduce_term : env -> types -> types (* betaiotazeta *)
val delta : env -> types -> types (* delta *)
val reduce_nf : env -> types ->  types (* nf_all *)
val reduce_type : env -> evar_map -> types -> types (* betaiotazeta on types *)
val reduce_to_ind : env -> types -> types (* reduce to applied eliminator *)
val chain_reduce : (* sequencing *)
  (env -> types -> types) ->
  (env -> types -> types) ->
  env ->
  types ->
  types

(* 
 * Apply a function on a type instead of on the term
 *)
val on_type : (types -> 'a) -> env -> evar_map -> types -> 'a

(* --- Basic mapping --- *)

val map_rec_env_fix :
  (env -> 'a -> 'b) ->
  ('a -> 'a) ->
  env ->
  'a ->
  name array ->
  types array ->
  'b
    
val map_term_env :
  (env -> 'a -> types -> types) ->
  ('a -> 'a) ->
  env ->
  'a ->
  types ->
  types

val map_term :
  ('a -> types -> types) ->
  ('a -> 'a) ->
  'a ->
  types ->
  types

(* --- Names --- *)

(* 
 * Add a string suffix to a name identifier 
 *)
val with_suffix : Id.t -> string -> Id.t

(* --- Application and arguments --- *)

(*
 * Get a list of all arguments of a type unfolded at the head
 * Return empty if it's not an application
 *)
val unfold_args : types -> types list

(*
 * Get the very last argument of an application
 *)
val last_arg : types -> types

(*
 * Get the very first function of an application
 *)
val first_fun : types -> types

(*
 * Fully unfold arguments, then get the argument at a given position
 *)
val get_arg : int -> types -> types
