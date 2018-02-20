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

Apply ornament orn_list_vector in hd as hd_vect.
