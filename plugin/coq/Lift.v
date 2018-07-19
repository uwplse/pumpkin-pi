Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Test lifting directly
 *)

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
