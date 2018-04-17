(*
 * Zooming into environments and reconstructing terms from environments
 *)

open Term
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

(* --- Reconstruct until n are left --- *)
                                                                     
val reconstruct_lambda_n : env -> types -> int -> types
val reconstruct_product_n : env -> types -> int -> types

(* --- Reconstruct until n are left, skipping a given amount first --- *)
                                                     
val reconstruct_lambda_n_skip : env -> types -> int -> int -> types
val reconstruct_product_n_skip : env -> types -> int -> int -> types

(* --- Reconstruct fully --- *)
                                                                 
val reconstruct_lambda : env -> types -> types
val reconstruct_product : env -> types -> types
