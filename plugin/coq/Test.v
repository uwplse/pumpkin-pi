(*
 * BEGIN DEVOID DEMO, PART 2
 *)
Require Import List.
Require Import Ornamental.Ornaments.

(*
 * Since search is the thing I want to focus on today, these tests just show
 * that search can handle a lot of different types. It makes a bunch of restrictions,
 * still, which I describe in the paper. If you're interested in some failing
 * examples, check ShouldFail.v.
 *
 * The numbers are weird here because it's a subset of the ones I show in master,
 * for brevity.
 * 
 * We turn on the options to prove search correct in each case:
 *)
Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.

(* --- Binary Trees and Indexed Binary Trees --- *)

(*
 * We can handle trees. Here's the tree analogue of a vector:
 *)

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
      bintreeV A n -> A -> bintreeV A m -> bintreeV A (S (n + m)).

Definition packed_bintreeV (T : Type) :=
  sigT (A := nat) (fun (n : nat) => bintreeV T n).

Find ornament bintree bintreeV as orn_bintree_bintreeV.

Definition bintree_size (A : Type) (tr : bintree A) :=
  bintree_rect
    A
    (fun (_ : bintree A) => nat)
    0
    (fun (l : bintree A) (nl : nat) (a : A) (r : bintree A) (nr : nat) =>
      S (nl + nr))
    tr.

Theorem test_index_3:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_index A tr = bintree_size A tr.
Proof.
  intros. auto.
Qed.

Theorem test_orn_3:
  forall (A : Type) (tr : bintree A),
    packed_bintreeV A.
Proof.
  exact orn_bintree_bintreeV.
Qed.

Theorem test_orn_index_3:
  forall (A : Type) (tr : bintree A),
    projT1 (orn_bintree_bintreeV A tr) = orn_bintree_bintreeV_index A tr.
Proof.
  exact orn_bintree_bintreeV_coh.
Qed.

Theorem test_orn_inv_3:
  forall (A : Type) (tr : packed_bintreeV A),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_inv.
Qed.

Theorem test_orn_inv_unpack_3:
  forall (A : Type) (n : nat) (tr : bintreeV A n),
    bintree A.
Proof.
  intros. apply orn_bintree_bintreeV_inv. exists n. apply tr.
Qed.

Theorem test_section_3:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_inv A (orn_bintree_bintreeV A tr) = tr.
Proof.
  exact orn_bintree_bintreeV_section.
Qed.

Theorem test_retraction_3:
  forall (A : Type) (tr : packed_bintreeV A),
    orn_bintree_bintreeV A (orn_bintree_bintreeV_inv A tr) = tr.
Proof.
  exact orn_bintree_bintreeV_retraction.
Qed.

(* --- Adding an index whose type that matches an already existing index --- *)

(*
 * If the new index has the same type as an existing index, we can disambiguate:
 *)

Inductive doublevector (A : Type) : nat -> nat -> Type :=
| dnilV : doublevector A 0 0
| dconsV :
    forall (n m : nat),
      A -> doublevector A n m -> doublevector A (S (S n)) (S m).

Definition packed_doublevector (A : Type) (m : nat) :=
  sigT (A := nat) (fun n : nat => doublevector A n m).

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
    orn_vector_doublevector_index A n v = vector_double_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_7:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector A n.
Proof.
  exact orn_vector_doublevector.
Qed.

Theorem test_orn_index_7:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector A n v) = orn_vector_doublevector_index A n v.
Proof.
  exact orn_vector_doublevector_coh.
Qed.

Theorem test_orn_inv_7:
  forall (A : Type) (m : nat) (d : packed_doublevector A m),
    vector A m.
Proof.
  exact orn_vector_doublevector_inv.
Qed.

Theorem test_orn_inv_unpack_7:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector A n m),
    vector A m.
Proof.
  intros. apply orn_vector_doublevector_inv. exists n. apply d.
Qed.

Theorem test_section_7:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector_inv A n (orn_vector_doublevector A n v) = v.
Proof.
  exact orn_vector_doublevector_section.
Qed.

Theorem test_retraction_7:
  forall (A : Type) (n : nat) (v : packed_doublevector A n),
    orn_vector_doublevector A n (orn_vector_doublevector_inv A n v) = v.
Proof.
  exact orn_vector_doublevector_retraction.
Qed.

(* --- Doublevector with an identical index --- *)

(*
 * If our indices are identical, we just arbitrarily pick one:
 *)

Inductive doublevector3 (A : Type) : nat -> nat -> Type :=
| dnilV3 : doublevector3 A 0 0
| dconsV3 :
    forall (n m : nat),
      A -> doublevector3 A n m -> doublevector3 A (S n) (S m).

Definition packed_doublevector3 (A : Type) (n : nat) :=
  sigT (A := nat) (fun (m : nat) => doublevector3 A n m).

Find ornament vector doublevector3 as orn_vector_doublevector3.

Definition vector_size (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n : nat) (v : vector A n) => nat)
    O
    (fun (n : nat) (a : A) (v : vector A n) (IH : nat) =>
      S IH)
    n
    v.

Theorem test_index_9:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector3_index A n v = vector_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_9:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector3 A n.
Proof.
  exact orn_vector_doublevector3.
Qed.

Theorem test_orn_index_9:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector3 A n v) = orn_vector_doublevector3_index A n v.
Proof.
  exact orn_vector_doublevector3_coh.
Qed.

Theorem test_orn_inv_9:
  forall (A : Type) (n : nat) (d : packed_doublevector3 A n),
    vector A n.
Proof.
  exact orn_vector_doublevector3_inv.
Qed.

Theorem test_orn_inv_unpack_9:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector3 A n m),
    vector A n.
Proof.
  intros. apply orn_vector_doublevector3_inv. exists m. apply d.
Qed.

Theorem test_section_9:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector3_inv A n (orn_vector_doublevector3 A n v) = v.
Proof.
  exact orn_vector_doublevector3_section.
Qed.

Theorem test_retraction_9:
  forall (A : Type) (n : nat) (v : packed_doublevector3 A n),
    orn_vector_doublevector3 A n (orn_vector_doublevector3_inv A n v) = v.
Proof.
  exact orn_vector_doublevector3_retraction.
Qed.

(* --- What if we change a base case index? --- *)

(*
 * If only the base case index changes, we can tell which one is new still:
 *)

Inductive doublevector4 (A : Type) : nat -> nat -> Type :=
| dnilV4 : doublevector4 A 1 0
| dconsV4 :
    forall (n m : nat),
      A -> doublevector4 A n m -> doublevector4 A (S n) (S m).

Definition packed_doublevector4 (A : Type) (m : nat) :=
  sigT (A := nat) (fun (n : nat) => doublevector4 A n m).

Find ornament vector doublevector4 as orn_vector_doublevector4.

Definition S_vector_size (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n : nat) (v : vector A n) => nat)
    1
    (fun (n : nat) (a : A) (v : vector A n) (IH : nat) =>
      S IH)
    n
    v.

Theorem test_index_10:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector4_index A n v = S_vector_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_10:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector4 A n.
Proof.
  exact orn_vector_doublevector4.
Qed.

Theorem test_orn_index_10:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector4 A n v) = orn_vector_doublevector4_index A n v.
Proof.
  exact orn_vector_doublevector4_coh.
Qed.

Theorem test_orn_inv_10:
  forall (A : Type) (m : nat) (d : packed_doublevector4 A m),
    vector A m.
Proof.
  exact orn_vector_doublevector4_inv.
Qed.

Theorem test_orn_inv_unpack_10:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector4 A n m),
    vector A m.
Proof.
  intros. apply orn_vector_doublevector4_inv. exists n. apply d.
Qed.

Theorem test_section_10:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector4_inv A n (orn_vector_doublevector4 A n v) = v.
Proof.
  exact orn_vector_doublevector4_section.
Qed.

Theorem test_retraction_10:
  forall (A : Type) (n : nat) (v : packed_doublevector4 A n),
    orn_vector_doublevector4 A n (orn_vector_doublevector4_inv A n v) = v.
Proof.
  exact orn_vector_doublevector4_retraction.
Qed.

(*
 * And so on. For more interesting examples, if you're curious, see the
 * case study. For example, our fold can be an invariant. 
 *)

(*
 * END DEVOID DEMO, PART 2
 *)