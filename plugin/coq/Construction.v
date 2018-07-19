Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Temporary file to test lifting constructions, before we replace buggy code in higher lifting.
 *)

Definition nil' := @nil.

Lift constructor orn_list_vector orn_list_vector_inv in nil' as nil'_c.
Print nil'_c.
Theorem testNil:
  forall A, nil'_c A = existT (vector A) 0 (nilV A).
Proof.
  intros. reflexivity.
Qed.

Definition nilV' (A : Type) :=
  existT (vector A) 0 (nilV A).

Lift constructor orn_list_vector_inv orn_list_vector in nilV' as nilV'_c.
Print nilV'_c.
Theorem testNilV:
  forall A, nilV'_c A = @nil A.
Proof.
  intros. reflexivity.
Qed.

Definition cons' := @cons.

Lift constructor orn_list_vector orn_list_vector_inv in cons' as cons'_c.
Print cons'_c.
Theorem testCons:
  forall A a l, 
    cons'_c A a l = 
    existT (vector A) (S (projT1 (orn_list_vector A l))) (consV A (projT1 (orn_list_vector A l)) a (projT2 (orn_list_vector A l))).
Proof.
  intros. reflexivity.
Qed.

Definition consV' (A : Type) (a : A) (pv : sigT (vector A)) :=
  existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)).

Lift constructor orn_list_vector_inv orn_list_vector in consV' as consV'_c.
Print consV'_c.
Theorem testConsV:
  forall A a pv,
    consV'_c A a pv = @cons A a (orn_list_vector_inv A (existT (vector A) (projT1 pv) (projT2 pv))).
Proof.
  intros. reflexivity.
Qed.

(* TODO once this works, test chaining w/ actual arguments, e.g. calling a function or constructing recursively *)
(* TODO try w/ trees, case study stuff, etc. *)
