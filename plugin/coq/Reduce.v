Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(* --- Simple functions on lists --- *)

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

(* TODO app *)

(* TODO proofs and more complex things *)