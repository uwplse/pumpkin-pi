Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(* --- Simple functions on lists --- *)

(*
 * hd and hd_vect
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_auto as hd_vect_red.

Theorem test_hd_vect:
  forall (A : Type) (default : A) (pv : packed_vector A),
    hd_vect_packed A default pv = hd_vect_red A default pv.
Proof.
  intros. reflexivity.
Qed.

(* TODO test relation to old version, eventually branch & simplify etc *)

Reduce ornament orn_list_vector_inv orn_list_vector in hd_auto as hd_red.

Theorem test_hd:
  forall (A : Type) (default : A) (l : list A),
    hd A default l = hd_red A default l.
Proof.
  intros. reflexivity.
Qed.

(*
 * hd_error and hd_vect_error
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_error_auto as hd_vect_error_red.

Theorem test_hd_vect_error:
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error_packed A pv = hd_vect_error_red A pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in hd_error_auto as hd_error_red.

Theorem test_hd_error:
  forall (A : Type) (l : list A),
    hd_error A l = hd_error_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * tl and tl_vect
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in tl_vect_auto as tl_vect_red.

Print tl_vect_red. 

Theorem test_tl_vect:
  forall (A : Type) (pv : packed_vector A),
    tl_vect_packed A pv = tl_vect_red A pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in tl_auto as tl_red.

Theorem test_tl:
  forall (A : Type) (l : list A),
    tl A l = tl_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * Application
 *)

Definition check2 (A : Type) (n : nat) (v : vector A n) (l2 : @sigT nat (fun (n1 : nat) => vector A n1)) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) =>
      @sigT nat (fun (n1 : nat) => vector A n1))
    l2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : @sigT nat (fun (n1 : nat) => vector A n1)) =>
      @existT
        nat
        (fun (n1 : nat) => vector A n1)
        (S
          (@sigT_rect
             nat
             (fun (n1 : nat) => vector A n1)
             (fun (pv : @sigT nat (fun (n1 : nat) => vector A n1)) => nat)
             (fun (n1 : nat) (v1 : vector A n1) => n1)
             IH))
        (@consV
          A
          (@sigT_rect
            nat
            (fun (n1 : nat) => vector A n1) 
            (fun (pv : @sigT nat (fun (n1 : nat) => vector A n1)) => nat)
            (fun (n1 : nat) (v1 : vector A n1) => n1)
            IH)
          a
          (@sigT_rect
            nat
            (fun (n1 : nat) => vector A n1)
            (fun (pv : @sigT nat (fun (n1 : nat) => vector A n1)) => 
              vector
                A
                (@sigT_rect
                  nat
                  (fun (n1 : nat) => vector A n1)
                  (fun (pv : @sigT nat (fun (n1 : nat) => vector A n1)) => nat)
                  (fun (n1 : nat) (v1 : vector A n1) => n1)
                  pv))
            (fun (n1 : nat) (v1 : vector A n1) => v1)
            IH)))
     n
     v.

Check check2.

Reduce ornament orn_list_vector orn_list_vector_inv in append_vect_auto as append_vect_red. 

Print append_vect_red.

Theorem test_append_vect:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_packed A pv1 pv2  = append_vect_red A pv1 pv2.
Proof.
  intros. induction pv1. reflexivity.
Qed.

(*
 * TODO the opposite direction fails, investigate (probably a factoring problem)
 *)
Reduce ornament orn_list_vector_inv orn_list_vector in append_auto as append_red.

Print append_red. (* TODO test *)

(* TODO proofs and more complex things *)

(* TODO other types besides lists *)