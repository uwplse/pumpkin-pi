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
  sigT_rect
    (fun _ : packed_vector A => A)
    (fun (n : nat) (v : vector A n) =>
      hd_vect A default n v)
    pv.

Apply ornament orn_list_vector orn_list_vector_inv in hd as hd_vect_auto.
Apply ornament orn_list_vector_inv orn_list_vector in hd_vect_packed as hd_auto.

Theorem test_orn_hd :
  forall (A : Type) (a : A) (pv : packed_vector A),
    hd_vect_auto A a pv = hd_vect_packed A a pv.
Proof.
  intros. induction pv; induction p; auto.
Qed.

(*
 * TODO then test that we can extract hd_vect from this if we want,
 * and same for all functions below
 *)

Theorem test_deorn_hd :
  forall (A : Type) (a : A) (l : list A),
    hd_auto A a l = hd A a l.
Proof.
  intros. induction l; auto.
Qed.

(*
 * TODO then test that we can get this from hd_vect if we want,
 * and same for all functions below
 *)

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
  sigT_rect
    (fun _ : packed_vector A => option A)
    (fun (n : nat) (v : vector A n) =>
      hd_vect_error A n v)
    pv.

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

Theorem append_vect_packed :
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    packed_vector A.
Proof.
  intros. apply orn_list_vector.
  apply append.
  - apply orn_list_vector_inv. apply pv1.
  - apply orn_list_vector_inv. apply pv2.
Qed.

Print append_vect_packed.
(* TODO define etc once this works *)

Apply ornament orn_list_vector orn_list_vector_inv in append as append_vect_auto.
Apply ornament orn_list_vector_inv orn_list_vector in append_vect as append_auto.

Check append_vect_auto.

(*
 * For this one, we can't state the equality, but we can use existsT.
 *)
Definition eq_vect A n (v : vector A n) n' (v' : vector A n') :=
  existT (vector A) n v = existT (vector A) n' v'.

Theorem eq_vect_cons:
  forall A n (v : vector A n) n' (v' : vector A n'),
    eq_vect A n v n' v' ->
    forall (a : A), eq_vect A (S n) (consV A n a v) (S n') (consV A n' a v').
Proof.
  unfold eq_vect.
  intros. inversion H. subst. auto.
Qed.

Theorem test_orn_append:
  forall A n (v : vector A n) n' (v' : vector A n'),
    eq_vect
      A
      (plus_vect A n v n' v')
      (append_vect A n v n' v')
      (orn_list_vector_index
        A
        (append A (orn_list_vector_inv A n v) (orn_list_vector_inv A n' v')))
      (append_vect_auto A n v n' v').
Proof.
  unfold eq_vect.
  intros. induction v; induction v'; try apply eq_vect_cons; auto.
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

Apply ornament orn_list_vector orn_list_vector_inv in tl as tl_vect_auto.
Apply ornament orn_list_vector_inv orn_list_vector in tl_vect as tl_auto.

Theorem coh_vect:
  forall (A : Type) (n : nat) (v : vector A n),
    eq_vect
      A
      (orn_list_vector_index A (orn_list_vector_inv A n v))
      (orn_list_vector A (orn_list_vector_inv A n v))
      n
      v.
Proof.
  intros. induction v.
  - reflexivity.
  - apply eq_vect_cons. apply IHv.
Qed.

(*
 * Same situation as above
 *)
Theorem test_orn_tl :
  forall (A : Type) (n : nat) (v : vector A n),
    eq_vect
      A
      (orn_list_vector_index A (tl A (orn_list_vector_inv A n v)))
      (tl_vect_auto A n v)
      (pred_vect A n v)
      (tl_vect A n v).
Proof.
  unfold eq_vect.
  intros. induction v; try apply coh_vect; auto.
Qed.

Theorem coh:
  forall (A : Type) (l : list A),
    orn_list_vector_inv A (orn_list_vector_index A l) (orn_list_vector A l) = l.
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
