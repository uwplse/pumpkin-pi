Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.
Require Import Reduce.

(*
 * Tests for higher lifting.
 *)

Higher lift orn_list_vector orn_list_vector_inv in app_nil_r_vect_red along append_red append_vect_red as app_nil_r_vect_red_higher.
Higher lift orn_list_vector_inv orn_list_vector in app_nil_r_red along append_vect_red append_red as app_nil_r_red_higher.

(*
 * These will fail until it's actually implemented
 *)
Theorem test_app_nil_r_vect:
  forall (A : Type) (pv : packed_vector A),
    append_vect_red A pv (existT (vector A) 0 (nilV A)) = pv.
Proof.
  exact app_nil_r_vect_red_higher.
Qed.

(* 
 * NOTE: We can simplify the above term at some point, which will give more clarity on
 * the lifted term we're looking for.
 *)

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  exact app_nil_r_red_higher.
Qed.
