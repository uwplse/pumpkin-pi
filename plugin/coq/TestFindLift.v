Require Import List.
Require Import Ornamental.Ornaments.

(*
 * This file tests automatically running
 * Find Ornament on the first invocation of Lift.
 * For it to work, both Find Ornament and Lift need to work.
 * The difference between this and the relevant part of TestLift.v 
 * is that this does not import Test, which has the relevant Find Ornament commands.
 *)

(* --- Simple constructor tests ---- *)

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

Definition packed_vector (T : Type) :=
  sigT (fun (n : nat) => vector T n).

Definition nil' := @nil.

Lift list vector in nil' as nil'_c.
Theorem testNil:
  forall A, nil'_c A = existT (vector A) 0 (nilV A).
Proof.
  intros. reflexivity.
Qed.

Definition nilV' (A : Type) :=
  existT (vector A) 0 (nilV A).

Lift vector list in nilV' as nilV'_c.
Theorem testNilV:
  forall A, nilV'_c A = @nil A.
Proof.
  intros. reflexivity.
Qed.

Definition cons' := @cons.

Lift list vector in cons' as cons'_c.
Theorem testCons:
  forall A a pv,
    cons'_c A a pv =
    existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)).
Proof.
  intros. reflexivity.
Qed.

Lift vector list in cons'_c as consV'_c.
Theorem testConsV:
  forall A a l,
    consV'_c A a l = @cons A a l.
Proof.
  intros. reflexivity.
Qed.
