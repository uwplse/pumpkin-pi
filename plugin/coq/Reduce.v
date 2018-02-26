Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(* --- Simple functions on lists --- *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_auto as hd_vect.