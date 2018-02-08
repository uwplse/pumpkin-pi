Require Import List.
Require Import Ornamental.Ornaments.

(*--- Lists and Vectors ---*)

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

Find ornament list vector as orn_list_vector.

Print orn_list_vector_index.

Theorem test_index:
  forall (A : Type) (l : list A),
    orn_list_vector_index A l = length l.
Proof.
  intros. auto.
Qed.

Find ornament vector list as orn_vector_list.

Print orn_vector_list_index.

Theorem test_index_inv:
  forall (A : Type) (l : list A),
    orn_vector_list_index A l = length l.
Proof.
  intros. auto.
Qed.

(* --- Backwards lists --- *)

Inductive rev_list (A : Type) : Type :=
| rev_nil : rev_list A
| rev_cons : rev_list A -> A -> rev_list A.

Inductive rev_vector (A : Type) : nat -> Type :=
| rev_nilV : rev_vector A 0
| rev_consV : forall (n : nat), rev_vector A n -> A -> rev_vector A (S n).

Find ornament rev_list rev_vector as orn_rev_list_rev_vector.

Print orn_rev_list_rev_vector_index.

Definition rev_list_length (A : Type) (rl : rev_list A) :=
  rev_list_rect
    A
    (fun (_ : rev_list A) => nat)
    0
    (fun (r : rev_list A) (n : nat) (a : A) =>
      S n)
    rl.

Theorem test_index_2:
  forall (A : Type) (l : rev_list A),
    orn_rev_list_rev_vector_index A l = rev_list_length A l.
Proof.
  intros. auto.
Qed.

Find ornament rev_vector rev_list as orn_rev_vector_rev_list.

Print orn_rev_vector_rev_list_index.

Theorem test_index_inv_2:
  forall (A : Type) (l : rev_list A),
    orn_rev_vector_rev_list_index A l = rev_list_length A l.
Proof.
  intros. auto.
Qed.

(* --- Binary Trees and Indexed Binary Trees --- *)

Inductive bintree (A : Type) : Type :=
| leaf :
    bintree A
| node :
    bintree A -> A -> bintree A -> bintree A.

Inductive bintreeV (A : Type) : nat -> Type :=
| leafV :
    bintreeV A 0
| nodeV :
    forall (n m : nat),
      bintreeV A n -> A -> bintreeV A m -> bintreeV A (n + m).

Find ornament bintree bintreeV as orn_bintree_bintreeV.

Print orn_bintree_bintreeV_index.

Definition bintree_size (A : Type) (tr : bintree A) :=
  bintree_rect
    A
    (fun (_ : bintree A) => nat)
    0
    (fun (l : bintree A) (nl : nat) (a : A) (r : bintree A) (nr : nat) =>
      nl + nr)
    tr.

Theorem test_index_3:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_index A tr = bintree_size A tr.
Proof.
  intros. auto.
Qed.

Find ornament bintreeV bintree as orn_bintreeV_bintree.

Print orn_bintreeV_bintree_index.

Theorem test_index_inv_3:
  forall (A : Type) (tr : bintree A),
    orn_bintreeV_bintree_index A tr = bintree_size A tr.
Proof.
  intros. auto.
Qed.

