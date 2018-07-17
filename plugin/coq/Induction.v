Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Temporary file to test lifting induction principles, before we cut
 * out extra steps of the old algorithm.
 *)

Definition hd (A : Type) (default : A) (l : list A) :=
  list_rect
    (fun (_ : list A) => A)
    default
    (fun (x : A) (_ : list A) (_ : A) =>
      x)
    l.

Lift induction orn_list_vector orn_list_vector_inv in hd as hd_vect_ind.
Print hd_vect_ind.

(* TODO other direction *)
(* TODO test more once basic code works at all *)
(* TODO try w/ eta, etc *)
(* TODO try types w/ indices in different places, a tree function, stuff from case studies *)
