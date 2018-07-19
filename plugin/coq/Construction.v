Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Temporary file to test lifting constructions, before we replace buggy code in higher lifting.
 *)

Definition nil' := @nil.

Lift constructor orn_list_vector orn_list_vector_inv in nil' as nil'_c.
Theorem testNil:
  forall A, nil'_c A = existT (vector A) 0 (nilV A).
Proof.
  intros. reflexivity.
Qed.

Definition nilV' (A : Type) :=
  existT (vector A) 0 (nilV A).

Lift constructor orn_list_vector_inv orn_list_vector in nilV' as nilV'_c.
Theorem testNilV:
  forall A, nilV'_c A = @nil A.
Proof.
  intros. reflexivity.
Qed.

Definition cons' := @cons.

Lift constructor orn_list_vector orn_list_vector_inv in cons' as cons'_c.
Print cons'_c.

Definition consV' (A : Type) (n : nat) (a : A) (v : vector A n) :=
  existT (vector A) (S n) (consV A n a v).

Lift constructor orn_list_vector_inv orn_list_vector in consV' as consV'_c.
Print consV'_c.

(* TODO once this works, test chaining w/ actual arguments, e.g. calling a function or constructing recursively *)
(* TODO try w/ trees, case study stuff, etc. *)
