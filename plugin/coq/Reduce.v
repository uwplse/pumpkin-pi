Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(* --- Simple functions on lists --- *)

(*
 * hd and hd_vect
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_auto as hd_vect_red.

Theorem test_hd_vect:
  forall (A : Type) (default : A) (pv : packed_vector A),
    hd_vect_packed A default pv = hd_vect_red A default pv.
Proof.
  intros. reflexivity.
Qed.

(* TODO test relation to old version, eventually branch & simplify etc *)
(* TODO generate coherence proof if asked for *)

Reduce ornament orn_list_vector_inv orn_list_vector in hd_auto as hd_red.

Theorem test_hd:
  forall (A : Type) (default : A) (l : list A),
    hd A default l = hd_red A default l.
Proof.
  intros. reflexivity.
Qed.

(*
 * hd_error and hd_vect_error
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_error_auto as hd_vect_error_red.

Theorem test_hd_vect_error:
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error_packed A pv = hd_vect_error_red A pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in hd_error_auto as hd_error_red.

Theorem test_hd_error:
  forall (A : Type) (l : list A),
    hd_error A l = hd_error_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * tl and tl_vect
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in tl_vect_auto as tl_vect_red.

Theorem test_tl_vect:
  forall (A : Type) (pv : packed_vector A),
    tl_vect_packed A pv = tl_vect_red A pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in tl_auto as tl_red.

Theorem test_tl:
  forall (A : Type) (l : list A),
    tl A l = tl_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * Application
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in append_vect_auto as append_vect_red. 

Theorem test_append_vect_red_index:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = plus_vect_exp A pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

(* Some basic sanity checking, should auto-generate at some point*)
Theorem test_append_vect_red_index_correct_unpacked:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = plus_vect A (projT1 pv1) (projT2 pv1) (projT1 pv2) (projT2 pv2).
Proof.  
  intros. induction pv1. induction p.
  - reflexivity.
  - simpl. simpl in IHp. rewrite IHp. reflexivity.
Qed.

Theorem test_append_vect_red_index_correct:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = projT1 (append_vect_red A pv1 pv2).
Proof.
  intros. induction pv1. induction p.
  - reflexivity.
  - rewrite test_append_vect_red_index_correct_unpacked. 
    unfold plus_vect. simpl. simpl in IHp. rewrite IHp. reflexivity.
Qed.

Theorem test_append_vect:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_packed A pv1 pv2  = append_vect_red A pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in append_auto as append_red.

Theorem test_append :
  forall (A : Type) (l1 : list A) (l2 : list A),
    append A l1 l2  = append_red A l1 l2.
Proof.
  intros. reflexivity.
Qed.

(* --- Proofs --- *)

(* 
 * app_nil_r is a proof that only exists inside of the sigma 
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in app_nil_r_vect_auto as app_nil_r_vect_red.

Print app_nil_r_vect_red.

Reduce ornament orn_list_vector_inv orn_list_vector in app_nil_r_auto as app_nil_r_red.

(* TODO more proofs *)

(* TODO other types besides lists *)