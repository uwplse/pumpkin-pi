Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.
Require Import Reduce.

(*
 * Tests for higher lifting.
 *)

Higher lift orn_list_vector orn_list_vector_inv in app_nil_r_vect_red as app_nil_r_vect_red_higher.

Theorem test_app_nil_r_vect:
  forall (A : Type) (pv : packed_vector A),
    append_vect_red A pv (existT (vector A) 0 (nilV A)) = pv.
Proof.
  exact app_nil_r_vect_red_higher.
Qed.

Print app_nil_r_vect_red_higher.

Higher lift orn_list_vector_inv orn_list_vector in app_nil_r_red as app_nil_r_red_higher.

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  exact app_nil_r_red_higher.
Qed.

Print app_nil_r_red_higher.