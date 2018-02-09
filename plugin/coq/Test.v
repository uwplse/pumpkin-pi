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

(* --- Lists of values of two types (making sure parameter logic works) --- *)

Inductive list2 (A : Type) (B : Type) : Type :=
| nil2 : list2 A B
| cons2 : A -> B -> list2 A B -> list2 A B.

Inductive vector2 (A : Type) (B : Type) : nat -> Type :=
| nilV2 : vector2 A B 0
| consV2 : forall (n : nat), A -> B -> vector2 A B n -> vector2 A B (S (S n)).

Definition length2 (A : Type) (B : Type) (l : list2 A B) :=
  list2_rect
    A
    B
    (fun (_ : list2 A B) => nat)
    0
    (fun (a : A) (b : B) (l' : list2 A B) (IH : nat) =>
      S (S IH))
    l.

Find ornament list2 vector2 as orn_list2_vector2.

Print orn_list2_vector2_index.

Theorem test_index_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    orn_list2_vector2_index A B l = length2 A B l.
Proof.
  intros. auto.
Qed.

Find ornament vector2 list2 as orn_vector2_list2.

Print orn_vector2_list2_index.

Theorem test_index_inv_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    orn_vector2_list2_index A B l = length2 A B l.
Proof.
  intros. auto.
Qed.

(* --- TODO what happens when your index from two nats in the context? --- *)

(* --- TODO what happens when your index depends on an earlier term? --- *)

(* --- TODO what does it mean if the index already existed in the old constructor, but wasn't used, or was used differently? How do we handle that? ---*)

(* --- TODO Or, for example, if there's only one nat but it's a tree? --- *)

(* --- TODO examples from notebook etc --- *)

(* --- TODO then write ornamentation function --- *)
