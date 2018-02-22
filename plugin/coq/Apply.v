Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

Definition hd (A : Type) (default : A) (l : list A) :=
  list_rect
    (fun (_ : list A) => A)
    default
    (fun (x : A) (_ : list A) (_ : A) =>
      x)
    l.

Apply ornament orn_list_vector orn_list_vector_inv in hd as hd_vect_auto.

Definition hd_vect (A : Type) (default : A) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => A)
    default
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : A) =>
      x)
    n
    v.

(*
 * Note how it's not definitionally equal, but we can prove it.
 * For it to be definitionally equal, we need to internalize the
 * ornamentation and run some reduction steps.
 *)
Theorem test_orn_hd :
  forall (A : Type) (a : A) (n : nat) (v : vector A n),
    hd_vect_auto A a n v = hd_vect A a n v.
Proof.
  intros. induction v; auto.
Qed.

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

Definition append_vect (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => vector A (n0 + n2))
    v2
    (fun (n0 : nat) (a : A) (_ : vector A n0) (IH : vector A (n0 + n2)) =>
      consV A (n0 + n2) a IH)
    n1
    v1.

Apply ornament orn_list_vector orn_list_vector_inv in append as append_vect_auto.

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
      (n + n')
      (append_vect A n v n' v')
      (orn_list_vector_index
        A
        (append A (orn_list_vector_inv A n v) (orn_list_vector_inv A n' v')))
      (append_vect_auto A n v n' v').
Proof.
  unfold eq_vect.
  intros. induction v; induction v'; try apply eq_vect_cons; auto.
Qed.



