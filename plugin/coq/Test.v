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

Theorem test_orn_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    vector2 A B (orn_list2_vector2_index A B l).
Proof.
  exact orn_list2_vector2.
Qed.

Theorem test_orn_inv_4:
  forall (A : Type) (B : Type) (n : nat) (l : vector2 A B n),
    list2 A B.
Proof.
  exact orn_list2_vector2_inv.
Qed.

(* --- Adding a nat index to a nat list --- *)

Inductive nat_list : Type :=
| nat_nil : nat_list
| nat_cons : nat -> nat_list -> nat_list.

Inductive nat_vector : nat -> Type :=
| nat_nilV : nat_vector 0
| nat_consV : forall (n : nat), nat -> nat_vector n -> nat_vector (S n).

Find ornament nat_list nat_vector as orn_natlist_natvector.

Definition nat_length (l : nat_list) :=
  nat_list_rect
    (fun (_ : nat_list) => nat)
    0
    (fun (_ : nat) (_ : nat_list) (IH : nat) =>
      S IH)
    l.

Theorem test_index_5:
  forall (l : nat_list),
    orn_natlist_natvector_index l = nat_length l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_5:
  forall (l : nat_list),
    nat_vector (nat_length l).
Proof.
  exact orn_natlist_natvector.
Qed.

Theorem test_orn_inv_5:
  forall (n : nat) (v : nat_vector n),
    nat_list.
Proof.
  exact orn_natlist_natvector_inv.
Qed.

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

Theorem test_index_6:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_rev_index A tr = bintree_size_rev A tr.
Proof.
  intros. auto.
Qed.

Theorem test_orn_6:
  forall (A : Type) (tr : bintree A),
    bintreeV_rev A (bintree_size_rev A tr).
Proof.
  exact orn_bintree_bintreeV_rev.
Qed.

Theorem test_orn_inv_6:
  forall (A : Type) (n : nat) (tr : bintreeV_rev A n),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_rev_inv.
Qed.

(* --- Adding an index whose type that matches an already existing index --- *)

Inductive doublevector (A : Type) : nat -> nat -> Type :=
| dnilV : doublevector A 0 0
| dconsV :
    forall (n m : nat),
      A -> doublevector A n m -> doublevector A (S (S n)) (S m).

Find ornament vector doublevector as orn_vector_doublevector.

Definition vector_double_size (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n : nat) (v : vector A n) => nat)
    O
    (fun (n : nat) (a : A) (v : vector A n) (IH : nat) =>
      S (S IH))
    n
    v.

Theorem test_index_7:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector_index A n = vector_double_size A n.
Proof.
  intros. auto.
Qed.

Theorem test_orn_7:
  forall (A : Type) (n : nat) (v : vector A n),
    doublevector A (vector_double_size A n v) n.
Proof.
  exact orn_vector_doublevector.
Qed.

Theorem test_orn_inv_7:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector A n m),
    vector A m.
Proof.
  exact orn_vector_doublevector_inv.
Qed.

(* --- Same as above, but switch the position we change --- *)

Inductive doublevector2 (A : Type) : nat -> nat -> Type :=
| dnilV2 : doublevector2 A 0 0
| dconsV2 :
    forall (n m : nat),
      A -> doublevector2 A n m -> doublevector2 A (S n) (S (S m)).

Find ornament vector doublevector2 as orn_vector_doublevector2.

Theorem test_index_8:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector2_index A n = vector_double_size A n.
Proof.
  intros. auto.
Qed.

Theorem test_orn_8:
  forall (A : Type) (n : nat) (v : vector A n),
    doublevector2 A n (vector_double_size A n v).
Proof.
  exact orn_vector_doublevector2.
Qed.

Theorem test_orn_inv_8:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector2 A n m),
    vector A n.
Proof.
  exact orn_vector_doublevector2_inv.
Qed.

(* --- Don't change at all --- *)


(* --- TODO adding an index that is computed from a hypothesis with a different type --- *)

(* --- TODO adding an index when one already exists --- *)

(* --- TODO adding indexes that aren't first --- *)

(* --- TODO adding multiple indices at once --- *)

(* --- TODO indexing by the old type, but without making it fin-like --- *)

(* --- TODO adding an index with several uses --- *)

(* --- TODO weirder indexes --- *)

(* --- TODO indices that depend on earlier indices and parameters --- *)

(* --- TODO what does it mean if the index already existed in the old constructor, but wasn't used, or was used differently? How do we handle that? ---*)

(* --- TODO base cases with arguments --- *)

(* --- TODO examples from notebook etc --- *)

(* --- TODO write a test script --- *)

