(*
 * Zooming into environments and reconstructing terms from environments
 *)

open Constr
open Environ
                 
(* --- Zoom n deep --- *)

val zoom_n_prod : env -> int -> types -> (env * types)
val zoom_n_lambda : env -> int -> types -> (env * types)

(* --- Zoom all the way --- *)
                                             
val zoom_lambda_term : env -> types -> (env * types)
val zoom_product_type : env -> types -> (env * types)

(* --- Projections of zooming --- *)
                                          
val zoom_env : (env -> types -> (env * types)) -> env -> types -> env
val zoom_term : (env -> types -> (env * types)) -> env -> types -> types

(* --- Zooming for sigma types --- *)

val zoom_sig_lambda : types -> types
val zoom_sig_app : types -> types
val zoom_sig : types -> types

(* --- Conditional zooming for sigma types --- *)

val zoom_if_sig_lambda : types -> types
val zoom_if_sig_app : types -> types
val zoom_if_sig : types -> types
                             
(* --- Reconstruct until n are left --- *)
                                                                     
val reconstruct_lambda_n : env -> types -> int -> types
val reconstruct_product_n : env -> types -> int -> types

(* --- Reconstruct until n are left, skipping a given amount first --- *)
                                                     
val reconstruct_lambda_n_skip : env -> types -> int -> int -> types
val reconstruct_product_n_skip : env -> types -> int -> int -> types

(* --- Reconstruct fully --- *)
                                                                 
val reconstruct_lambda : env -> types -> types
val reconstruct_product : env -> types -> types

(* --- Zoom in and apply a function --- *)

val in_body :
  (env -> types -> (env * types)) ->
  (env -> types -> 'a) ->
  env ->
  types ->
  'a

val in_lambda_body :
  (env -> types -> 'a) -> env -> types -> 'a
                                            
(* --- Zoom in, apply a function, then reconstruct the result --- *)

val zoom_apply :
  (env -> types -> (env * types)) -> (* zoomer *)
  (env -> types -> types) -> (* reconstructer *)
  (env -> types -> types) -> (* function *)
  env ->
  types ->
  types

val zoom_apply_lambda :
  (env -> types -> types) -> env -> types -> types

val zoom_apply_lambda_empty :
  (types -> types) -> types -> types

val zoom_apply_lambda_n :
  int -> (env -> types -> types) -> env -> types -> types

val zoom_apply_lambda_n_skip :
  int -> int -> (env -> types -> types) -> env -> types -> types

