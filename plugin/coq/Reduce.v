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
  forall (A : Type) (default : A) (n : nat) (v : vector A n),
    hd_vect A default n v = hd_vect_red A default n v.
Proof.
  intros. reflexivity.
Qed.

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

Print tl_vect_red_index.

Print tl_vect_red.

Theorem test_tl_vect:
  forall (A : Type) (n : nat) (v : vector A n),
    tl_vect A n v = tl_vect_red A n v.
Proof.
  intros. reflexivity.
Qed.

(* TODO app *)

(* Currently fails (factoring problem) 
Reduce ornament orn_list_vector orn_list_vector_inv in append_vect_auto as append_vect_red.*)

(* TODO proofs and more complex things *)

(* TODO other types *)