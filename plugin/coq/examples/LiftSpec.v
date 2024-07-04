(*
 * Section 3.2 Examples
 *)

Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Search. (* <-- includes our ornament *)
Require Import Example. (* <-- includes our functions  *)

(* syntax to match paper *)
Notation vector := Vector.t.
Notation consV n t v := (Vector.cons _ t n v).
Notation nilV := Vector.nil.
Notation promote := ltv.
Notation zip := hs_to_coq.zip.
Notation zip_with_is_zip := hs_to_coq.zip_with_is_zip.
Arguments zip {_} {_} _ _.
Arguments zipV_p {_} {_} _ _.
Arguments promote {_} _.

(* --- Types go to types --- *)

Lift list vector in list as vector_p.
Print vector_p.

(* --- Terms go to terms --- *)

Lift list vector in (cons 5 nil) as v_p.
Print v_p.

(* --- Functions take inputs to inputs, and outputs to outputs --- *)

(* auxiliary lemma to refold constructors *)
Lemma promote_pres_cons:
  forall {T} (t : T) (l : list T),
    promote (cons t l) = 
    existT _ 
      (S (projT1 (promote l))) 
      (consV (projT1 (promote l)) t (projT2 (promote l))).
Proof.
  auto.
Qed.

Ltac refold := rewrite promote_pres_cons.

(*
 * With that in mind, the proof is pretty simple:
 *)
Example lift_pres_zip:
  forall {T1} {T2} (l1 : list T1) (l2 : list T2),
     promote (zip l1 l2) = 
     zipV_p (promote l1) (promote l2).
Proof. 
  induction l1; auto. refold.
  induction l2; auto. simpl. refold. refold.
  rewrite (IHl1 l2).
  auto.
Qed.

(* --- Dependent types make this harder to state --- *)

Check hs_to_coq.zip_with_is_zip.

(* conclusions are incomparable *)
Fail Example bad_intuition:
  forall {A} {B} (l1 : list A) (l2 : list B),
    zip_with_is_zip A B l1 l2 = 
    zip_with_is_zipV_p A B (promote l1) (promote l2).
(* we really need a heterogenous relation *)
