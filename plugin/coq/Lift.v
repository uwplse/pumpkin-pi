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
Print nil'_c.
Theorem testNil:
  forall A, nil'_c A = existT (vector A) 0 (nilV A).
Proof.
  intros. reflexivity.
Qed.

Definition nilV' (A : Type) :=
  existT (vector A) 0 (nilV A).

Lift2 orn_list_vector_inv orn_list_vector in nilV' as nilV'_c.
Print nilV'_c.
Theorem testNilV:
  forall A, nilV'_c A = @nil A.
Proof.
  intros. reflexivity.
Qed.

Definition cons' := @cons.

Lift2 orn_list_vector orn_list_vector_inv in cons' as cons'_c.
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

Lift2 orn_list_vector_inv orn_list_vector in consV' as consV'_c.
Print consV'_c.
Theorem testConsV:
  forall A a pv,
    consV'_c A a pv = @cons A a (orn_list_vector_inv A (existT (vector A) (projT1 pv) (projT2 pv))).
Proof.
  intros. reflexivity.
Qed.

(* TODO once this works, test chaining w/ actual arguments, e.g. calling a function or constructing recursively *)
(* TODO try w/ trees, case study stuff, etc. *)


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

Lift2 orn_list_vector orn_list_vector_inv in hd as hd_vect_lift.
Print hd_vect_lift.

Lift2 orn_list_vector_inv orn_list_vector in hd_vect as hd_lift.
Print hd_lift.
