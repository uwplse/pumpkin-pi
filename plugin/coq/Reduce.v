Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.
Require Import Lift.

(* TODO opposite direction *)

(* 
 * NOTE: The app_nil_r case needs an automatic proof of indices, which it doesn't have yet.
 * The proof should be automatically derivable from app_nil_r, but the tool only tries to infer an indexing
 * function in the case that we lift back to vectors, like with append_vect and tl_vect.
 * Below we manually derive the proofs we would want, so we can implement this later (TODO).
 *)

Ornamental Reduction in_split_vect_red from in_split_vect_auto using orn_list_vector orn_list_vector_inv.

(* TODO test *)
(* TODO opposite direction too once it's done *)

(* needed for porting discriminate proofs *)
Ornamental Reduction is_cons_vect_red from is_cons_vect_auto using orn_list_vector orn_list_vector_inv.

(* TODO test, opposite *)

Ornamental Reduction hd_error_some_nil_vect_red from hd_error_some_nil_vect_auto using orn_list_vector orn_list_vector_inv.

(* TODO test, opposite *)

(* --- Unimplemented ideas --- *)

(* TODO more proofs *)

(* TODO other types besides lists *)
