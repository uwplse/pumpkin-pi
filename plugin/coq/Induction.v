Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Temporary file to test lifting induction principles, before we cut
 * out extra steps of the old algorithm.
 *)

Section test.

  Parameter (A : Type).
  Parameter (default : A).
  Parameter (l : list A).

  Definition hd :=
    list_rect
      (fun (_ : list A) => A)
      default
      (fun (x : A) (_ : list A) (_ : A) =>
        x)
      l.

End test.

Lift induction orn_list_vector orn_list_vector_inv in hd as hd_vect_ind.
Print hd_vect_ind.

(* TODO test more once basic code works at all *)
(* TODO try w/ eta, etc *)
