Require Import List.
Require Import Ornamental.Ornaments.

(*--- Lists and Vectors ---*)

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

Find ornament list vector as orn_list_vector.

Theorem test_index:
  forall (A : Type) (l : list A),
    orn_list_vector_index A l = length l.
Proof.
  intros. auto.
Qed.

Theorem test_orn:
  forall (A : Type) (l : list A),
    vector A (length l).
Proof.
  exact orn_list_vector.
Qed.

Theorem test_orn_inv:
  forall (A : Type) (n : nat) (v : vector A n),
    list A.
Proof.
  exact orn_list_vector_inv.
Qed.

(* --- Backwards lists --- *)

Inductive rev_list (A : Type) : Type :=
| rev_nil : rev_list A
| rev_cons : rev_list A -> A -> rev_list A.

Inductive rev_vector (A : Type) : nat -> Type :=
| rev_nilV : rev_vector A 0
| rev_consV : forall (n : nat), rev_vector A n -> A -> rev_vector A (S n).

Find ornament rev_list rev_vector as orn_rev_list_rev_vector.

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

Theorem test_orn_2:
  forall (A : Type) (l : rev_list A),
    rev_vector A (rev_list_length A l).
Proof.
  exact orn_rev_list_rev_vector.
Qed.

Theorem rest_orn_inv_2:
  forall (A : Type) (n : nat) (v : rev_vector A n),
    rev_list A.
Proof.
  exact orn_rev_list_rev_vector_inv.
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

Theorem test_orn_3:
  forall (A : Type) (tr : bintree A),
    bintreeV A (bintree_size A tr).
Proof.
  exact orn_bintree_bintreeV.
Qed.

Theorem test_orn_inv_3:
  forall (A : Type) (n : nat) (tr : bintreeV A n),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_inv.
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

Theorem test_index_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    orn_list2_vector2_index A B l = length2 A B l.
Proof.
  intros. auto.
Qed.

(* --- Balanced binary trees --- *)

Inductive bal_bintree (A : Type) : nat -> Type :=
| bal_leaf :
    bal_bintree A 0
| bal_node :
    forall (n : nat),
      bal_bintree A n -> A -> bal_bintree A n -> bal_bintree A (n + n).

(*
 * This technically works, but has an extra condition we don't find yet:
 *
 * Find ornament bintree bal_bintree as bintree_balancer.
 *
 * Print bintree_balancer_index.
 *
 * That is, we can find an indexing function, but note that to use it
 * (and to port bintrees to bal_bintrees anyways) we need a balanced
 * premise. We should be able to also infer the balanced premise automatically,
 * but it's tricky to know when we actually need to do this.
 * It seems like when the same index is referenced by several of the
 * other bintrees. We should revisit this at some point.
 *)

(* --- BintreeV with nats in reverse order --- *)

Inductive bintreeV_rev (A : Type) : nat -> Type :=
| leafV_rev :
    bintreeV_rev A 0
| nodeV_rev :
    forall (n m : nat),
      bintreeV_rev A m -> A -> bintreeV_rev A n -> bintreeV_rev A (n + m).

Definition bintree_size_rev (A : Type) (tr : bintree A) :=
  bintree_rect
    A
    (fun (_ : bintree A) => nat)
    0
    (fun (l : bintree A) (nl : nat) (a : A) (r : bintree A) (nr : nat) =>
      nr + nl)
    tr.

Find ornament bintree bintreeV_rev as orn_bintree_bintreeV_rev.

Print orn_bintree_bintreeV_rev_index.

Theorem test_index_6:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_rev_index A tr = bintree_size_rev A tr.
Proof.
  intros. auto.
Qed.

Find ornament bintreeV_rev bintree as orn_bintreeV_rev_bintree.

Print orn_bintreeV_rev_bintree_index.

Theorem test_index_inv_6:
  forall (A : Type) (tr : bintree A),
    orn_bintreeV_rev_bintree_index A tr = bintree_size_rev A tr.
Proof.
  intros. auto.
Qed.

(* --- Vectors using multiple nats --- *)

(*
 * If we add another nat to this hypothesis, then we have something incompletely
 * determined, because we need an extra nat in each case.
 *)

Inductive vector3 (A : Type) : nat -> Type :=
| nilV3 : vector3 A 0
| consV3 : forall (n m : nat), A -> vector3 A n -> vector3 A (n + m).

(*
 * This will fail (as it should, for now, though with a better error):
 *
 * Find ornament list vector3 as orn_list_vector3.
 *
 * Print orn_list_vector3_index.
 *)

Inductive vector4 (A : Type) : nat -> Type :=
| nilV4 : vector4 A 0
| consV4 : forall (n m : nat), A -> vector4 A (n + m) -> vector4 A n.

(*
 * This will fail (as it should, for now, though with a better error):
 *
 * Find ornament list vector4 as orn_list_vector4.
 *
 * Print orn_list_vector4_index.
 *)

(* --- TODO adding a nat index to a nat list or nat rev_list --- *)

(* --- TODO adding an index when one already exists --- *)

(* --- TODO adding indexes that aren't first --- *)

(* --- TODO weirder indexes --- *)

(* --- TODO what happens when your index depends on an earlier term? --- *)

(* --- TODO what does it mean if the index already existed in the old constructor, but wasn't used, or was used differently? How do we handle that? ---*)

(* --- TODO examples from notebook etc --- *)

(* --- TODO then write ornamentation function --- *)

(* --- TODO move the weirder ones to separate files; write a test script --- *)
