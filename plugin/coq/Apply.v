Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Test applying ornaments to lift functions, without internalizing
 * the ornamentation (so the type won't be useful yet).
 *)

(* --- Simple functions on lists --- *)

Definition hd (A : Type) (default : A) (l : list A) :=
  list_rect
    (fun (_ : list A) => A)
    default
    (fun (x : A) (_ : list A) (_ : A) =>
      x)
    l.

Definition hd_vect (A : Type) (default : A) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => A)
    default
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : A) =>
      x)
    n
    v.

Definition hd_vect_packed (A : Type) (default : A) (pv : packed_vector A) :=
  hd_vect A default (projT1 pv) (projT2 pv).

Apply ornament orn_list_vector orn_list_vector_inv in hd as hd_vect_auto.
Apply ornament orn_list_vector_inv orn_list_vector in hd_vect_packed as hd_auto.

Theorem test_orn_hd :
  forall (A : Type) (a : A) (pv : packed_vector A),
    hd_vect_auto A a pv = hd_vect_packed A a pv.
Proof.
  intros. induction pv; induction p; auto.
Qed.

Theorem test_orn_hd_proj :
  forall (A : Type) (a : A) (n : nat) (v : vector A n),
    hd_vect_auto A a (existT (vector A) n v) = hd_vect A a n v.
Proof.
  intros. induction v; auto.
Qed.

Theorem test_deorn_hd :
  forall (A : Type) (a : A) (l : list A),
    hd_auto A a l = hd A a l.
Proof.
  intros. induction l; auto.
Qed.

Definition hd_error (A : Type) (l:list A) :=
  list_rect
    (fun (_ : list A) => option A)
    None
    (fun (x : A) (_ : list A) (_ : option A) =>
      Some x)
    l.

Definition hd_vect_error (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => option A)
    None
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : option A) =>
      Some x)
    n
    v.

Definition hd_vect_error_packed (A : Type) (pv : packed_vector A) :=
  hd_vect_error A (projT1 pv) (projT2 pv).

Apply ornament orn_list_vector orn_list_vector_inv in hd_error as hd_vect_error_auto.
Apply ornament orn_list_vector_inv orn_list_vector in hd_vect_error_packed as hd_error_auto.

(*
 * Same situation as above
 *)
Theorem test_orn_hd_error :
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error_auto A pv = hd_vect_error_packed A pv.
Proof.
  intros. induction pv; induction p; auto.
Qed.

Theorem test_orn_hd_error_proj :
  forall (A : Type) (n : nat) (v : vector A n),
    hd_vect_error_auto A (existT (vector A) n v) = hd_vect_error A n v.
Proof.
  intros. induction v; auto.
Qed.

Theorem test_deorn_hd_error :
  forall (A : Type) (a : A) (l : list A),
    hd_error_auto A l = hd_error A l.
Proof.
  intros. induction l; auto.
Qed.

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

(* For now, we don't eliminate the vector reference, since incides might refer to other things *)
Definition plus_vect (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => nat)
    n2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : nat) =>
      S (IH))
    n1
    v1.

Definition append_vect (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => vector A (plus_vect A n0 v0 n2 v2))
    v2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : vector A (plus_vect A n0 v0 n2 v2)) =>
      consV A (plus_vect A n0 v0 n2 v2) a IH)
    n1
    v1.

Definition append_vect_packed (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A) :=
  existT
    (fun H : nat => vector A H)
    (plus_vect A (projT1 pv1) (projT2 pv1) (projT1 pv2) (projT2 pv2))
    (append_vect A (projT1 pv1) (projT2 pv1) (projT1 pv2) (projT2 pv2)).

Apply ornament orn_list_vector orn_list_vector_inv in append as append_vect_auto.
Apply ornament orn_list_vector_inv orn_list_vector in append_vect_packed as append_auto.

(*
 * For this one, we can't state the equality, but we can use existsT.
 *)
Theorem eq_vect_cons:
  forall A n (v : vector A n) n' (v' : vector A n'), 
    existT (vector A) n v = existT (vector A) n' v' ->
    forall (a : A),
      (existT (vector A) (S n) (consV A n a v)) =
      (existT (vector A) (S n') (consV A n' a v')).
Proof.
  intros. inversion H. subst. auto.
Qed.

Theorem test_orn_append:
  forall A (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_packed A pv1 pv2 = append_vect_auto A pv1 pv2.
Proof.
  intros. induction pv1; induction pv2; induction p; induction p0; try apply eq_vect_cons; auto.
Qed.

Theorem test_orn_append_proj :
  forall (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2),
    existT
      (vector A)
      (projT1 (append_vect_auto A (existT (vector A) n1 v1) (existT (vector A) n2 v2)))
      (projT2 (append_vect_auto A (existT (vector A) n1 v1) (existT (vector A) n2 v2))) =
    existT
      (vector A)
      (plus_vect A n1 v1 n2 v2)
      (append_vect A n1 v1 n2 v2).
Proof.
  intros. induction v1; induction v2; try apply eq_vect_cons; auto.
Qed.

(*
 * To prove the deornamentation case, we need the same lemma,
 * but we can state the equality directly.
 *)
Theorem eq_cons:
  forall A (l : list A) (l' : list A),
    l = l' ->
    forall (a : A), a :: l = a :: l'.
Proof.
  intros. inversion H. subst. auto.
Qed.

Theorem test_deorn_append:
  forall A (l : list A) (l' : list A),
    append A l l' = append_auto A l l'.
Proof.
  intros. induction l; induction l'; try apply eq_cons; auto.
Qed.

Definition tl (A : Type) (l:list A) :=
  list_rect
    (fun (_ : list A) => list A)
    nil
    (fun (a : A) (m : list A) (_ : list A) =>
      m)
    l.

(* For now, we don't eliminate the vector reference, since incides might refer to other things *)
Definition pred_vect (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => nat)
    0
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : nat) =>
      n0)
    n
    v.

Definition tl_vect (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => vector A (pred_vect A n0 v0))
    (nilV A)
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : vector A (pred_vect A n0 v0)) =>
      v0)
    n
    v.

Definition tl_vect_packed (A : Type) (pv : packed_vector A) :=
  existT
    (vector A) (* note currying when reducing *)
    (pred_vect A (projT1 pv) (projT2 pv))
    (tl_vect A (projT1 pv) (projT2 pv)).

Apply ornament orn_list_vector orn_list_vector_inv in tl as tl_vect_auto.
Apply ornament orn_list_vector_inv orn_list_vector in tl_vect_packed as tl_auto.

Theorem coh_vect:
  forall (A : Type) (n : nat) (v : vector A n),
    existT (vector A) (orn_list_vector_index A (orn_list_vector_inv A (existT (vector A) n v))) (projT2 (orn_list_vector A (orn_list_vector_inv A (existT (vector A) n v)))) = 
    existT (vector A) n v.
Proof.
  intros. induction v.
  - reflexivity.
  - apply eq_vect_cons. apply IHv.
Qed.

(*
 * Same situation as above
 *)
Theorem test_orn_tl :
  forall (A : Type) (pv : packed_vector A),
    tl_vect_auto A pv = tl_vect_packed A pv.
Proof.
  intros. induction pv; induction p; try apply coh_vect; auto.
Qed.

Theorem test_orn_tl_proj :
  forall (A : Type) (n : nat) (v : vector A n),
    existT
      (vector A)
      (projT1 (tl_vect_auto A (existT (vector A) n v)))
      (projT2 (tl_vect_auto A (existT (vector A) n v))) =
    existT
      (vector A)
      (pred_vect A n v)
      (tl_vect A n v).
Proof.
  intros. induction v; try apply coh_vect; auto.
Qed.

Theorem coh:
  forall (A : Type) (l : list A),
    orn_list_vector_inv A (existT (vector A) (orn_list_vector_index A l) (projT2 (orn_list_vector A l))) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - apply eq_cons. apply IHl.
Qed.

Theorem test_deorn_tl :
  forall (A : Type) (a : A) (l : list A),
    tl_auto A l = tl A l.
Proof.
  intros. induction l; try apply coh; auto.
Qed.

(* TODO try In, then you can try the facts about In, which should translate over as soon
   as app translates over. Then try app_nil_r and so on. *)

(* TODO test more to see if there are bugs before internalizing *)

(* TODO test some functions on other types besides lists/vectors *)
