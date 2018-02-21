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

Print hd_vect_auto.

(* TODO test *)

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

Apply ornament orn_list_vector orn_list_vector_inv in append as append_vect_auto.

Print append_vect_auto.

(* TODO test *)


