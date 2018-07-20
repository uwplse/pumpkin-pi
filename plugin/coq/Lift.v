Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Test lifting directly
 *)

(* --- Simple constructor tests ---- *)

Definition nil' := @nil.

Lift2 orn_list_vector orn_list_vector_inv in nil' as nil'_c.
Theorem testNil:
  forall A, nil'_c A = existT (vector A) 0 (nilV A).
Proof.
  intros. reflexivity.
Qed.

Definition nilV' (A : Type) :=
  existT (vector A) 0 (nilV A).

Lift2 orn_list_vector_inv orn_list_vector in nilV' as nilV'_c.
Theorem testNilV:
  forall A, nilV'_c A = @nil A.
Proof.
  intros. reflexivity.
Qed.

Definition cons' := @cons.

Lift2 orn_list_vector orn_list_vector_inv in cons' as cons'_c.
Theorem testCons:
  forall A a pv, 
    cons'_c A a pv = 
    existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)).
Proof.
  intros. reflexivity.
Qed.

Definition consV' (A : Type) (a : A) (pv : sigT (vector A)) :=
  existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)).

Lift2 orn_list_vector_inv orn_list_vector in consV' as consV'_c.
Theorem testConsV:
  forall A a l,
    consV'_c A a l = @cons A a l.
Proof.
  intros. reflexivity.
Qed.

(* --- Simple functions --- *)

Definition hd (A : Type) (default : A) (l : list A) :=
  list_rect
    (fun (_ : list A) => A)
    default
    (fun (x : A) (_ : list A) (_ : A) =>
      x)
    l.

Definition hd_vect (A : Type) (default : A) (pv : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => A)
    default
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : A) =>
      x)
    (projT1 pv)
    (projT2 pv).

Lift2 orn_list_vector orn_list_vector_inv in hd as hd_vect_lifted.

Theorem test_hd_vect:
  forall (A : Type) (default : A) (pv : packed_vector A),
    hd_vect A default pv = hd_vect_lifted A default pv.
Proof.
  intros. reflexivity.
Qed.

Lift2 orn_list_vector_inv orn_list_vector in hd_vect as hd_lifted.

Theorem test_hd:
  forall (A : Type) (default : A) (l : list A),
    hd A default l = hd_lifted A default l.
Proof.
  intros. reflexivity.
Qed.

(* flist/flector version *)

Definition hdF (default : nat) (l : natFlector.flist) :=
  natFlector.flist_rect
    (fun (_ : natFlector.flist) => nat)
    default
    (fun (x : nat) (_ : natFlector.flist) (_ : nat) =>
      x)
    l.

Definition hd_vectF (default : nat) (pv : sigT natFlector.flector) :=
  natFlector.flector_rect
    (fun (n0 : nat) (_ : natFlector.flector n0) => nat)
    default
    (fun (n0 : nat) (x : nat) (_ : natFlector.flector n0) (_ : nat) =>
      x)
    (projT1 pv)
    (projT2 pv).

Lift2 orn_flist_flector_nat orn_flist_flector_nat_inv in hdF as hd_vectF_lifted.

Theorem test_hd_vectF:
  forall (default : nat) (pv : sigT natFlector.flector),
    hd_vectF default pv = hd_vectF_lifted default pv.
Proof.
  intros. reflexivity.
Qed.

Lift2 orn_flist_flector_nat_inv orn_flist_flector_nat in hd_vectF as hdF_lifted.

Theorem test_hdF:
  forall (default : nat) (l : natFlector.flist),
    hdF default l = hdF_lifted default l.
Proof.
  intros. reflexivity.
Qed.

(* hd_error *)

Definition hd_error (A : Type) (l : list A) :=
  list_rect
    (fun (_ : list A) => option A)
    None
    (fun (x : A) (_ : list A) (_ : option A) =>
      Some x)
    l.

Definition hd_vect_error (A : Type) (v : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => option A)
    None
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : option A) =>
      Some x)
    (projT1 v)
    (projT2 v).

Lift2 orn_list_vector orn_list_vector_inv in hd_error as hd_vect_error_lifted.

Theorem test_hd_vect_error:
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error A pv = hd_vect_error_lifted A pv.
Proof.
  intros. reflexivity.
Qed.

Lift2 orn_list_vector_inv orn_list_vector in hd_vect_error as hd_error_lifted.

Theorem test_hd_error:
  forall (A : Type) (l : list A),
    hd_error A l = hd_error_lifted A l.
Proof.
  intros. reflexivity.
Qed.

(* append *)

(*
 * Test applying ornaments to lift functions, without internalizing
 * the ornamentation (so the type won't be useful yet).
 *)

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

Definition append_vect (A : Type) (pv1 : sigT (vector A)) (pv2 : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => sigT (fun (n : nat) => vector A n))
    pv2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : sigT (fun (n : nat) => vector A n)) =>
      existT
        (vector A)
        (S (projT1 IH))
        (consV A (projT1 IH) a (projT2 IH)))
    (projT1 pv1)
    (projT2 pv1).

Lift2 orn_list_vector orn_list_vector_inv in append as append_vect_lifted.

Theorem test_append_vect:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect A pv1 pv2  = append_vect_lifted A pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Lift2 orn_list_vector_inv orn_list_vector in append_vect as append_lifted.

Theorem test_append :
  forall (A : Type) (l1 : list A) (l2 : list A),
    append A l1 l2  = append_lifted A l1 l2.
Proof.
  intros. reflexivity.
Qed.


(* TODO rest of tests, eta, case study *)
