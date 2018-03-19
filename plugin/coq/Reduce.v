Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(* --- Simple functions on lists --- *)

(*
 * hd and hd_vect
 *)

Print hd_vect_packed.

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_auto as hd_vect_red.

Print hd_vect_red.

Theorem test_hd_vect:
  forall (A : Type) (default : A) (pv : packed_vector A),
    hd_vect_packed A default pv = hd_vect_red A default pv.
Proof.
  intros. induction pv. reflexivity.
Qed.

(* TODO test relation to old version, eventually branch & simplify etc *)

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
  forall (A : Type) (n : nat) (v : vector A n),
    hd_vect_error A n v = hd_vect_error_red A n v.
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
  forall (A : Type) (n : nat) (v : vector A n),
    tl_vect A n v = tl_vect_red A n v.
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

Theorem test_append_vect:
  forall (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2),
    append_vect A n1 v1 n2 v2 = append_vect_red A n1 v1 n2 v2.
Proof.
  intros. reflexivity.
Qed.

(*
 * TODO the opposite direction fails, investigate (probably a factoring problem)
 *)
Reduce ornament orn_list_vector_inv orn_list_vector in append_auto as append_red.

Print append_red. (* TODO test *)

(* TODO proofs and more complex things *)

(* TODO other types besides lists *)