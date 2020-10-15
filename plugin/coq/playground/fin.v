(*
 * Vectors and Fin (also from Anders)
 * Thanks to James Wilcox for the missing gaps that I needed!
 * https://gist.github.com/wilcoxjay/10cc817d20ad7148899c3725a1ebf06e
 *)
Require Import Ornamental.Ornaments.
Set DEVOID lift type.

Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.

(* needed for this equivalence *)
Require Import Coq.Logic.FunctionalExtensionality.

Section Config.

Parameter T : Type.

Definition A (n : nat) :=
  Vector.t T n.

Definition B (n : nat) :=
  Fin.t n -> T.

Definition dep_constr_A_0 : A 0 :=
  Vector.nil T.

Definition dep_constr_A_1 (t : T) (n : nat) (v : A n) : A (S n) :=
  Vector.cons T t n v.

Program Definition dep_constr_B_0 : B 0.
Proof.
  unfold B. intros f. apply Fin.case0. apply f.
Defined.

Definition dep_constr_B_1 (t : T) (n : nat) (b : B n) : B (S n) :=
  fun f =>
  match f with
  | Fin.F1 => fun _ => t
  | Fin.FS f' => fun b' => b' f'
  end b.

Definition eta_A (n : nat) (a : A n) : A n := a.
Definition eta_B (n : nat) (b : B n) : B n := b.

(* TODO for practicality, might need this instead, unsure: *)
(*Definition eta_A (n m : nat) (H : n = m) (a : A n) : A m := eq_rect m A a n H.*)
(* and eta B might need to use the tail/hd properties. we'll see *)

Definition dep_elim_A (P : forall n : nat, A n -> Type) (f0 : P 0 dep_constr_A_0)
  (f1 : forall (t : T) (n : nat) (v : A n), P n v -> P (S n) (dep_constr_A_1 t n v)) 
  (n : nat) (v : A n) 
: P n v 
:=
  Vector.t_rect T P f0 f1 n v.

Definition hd n (b : B (S n)) : T :=
  b Fin.F1.

Definition tl n (b : B (S n)) : B n :=
  fun f => b (Fin.FS f).

Lemma eta_dep_constr_B_0:
  forall (b : B 0),
    dep_constr_B_0 = b.
Proof.
  intros b.
  apply functional_extensionality_dep_good.
  intros f.
  apply Fin.case0.
  apply f.
Defined.

Lemma eta_dep_constr_B_1:
  forall (n : nat) (b : B (S n)),
    dep_constr_B_1 (hd n b) n (tl n b) = b.
Proof.
  intros n b.
  apply functional_extensionality_dep_good.
  intros f.
  revert b.
  refine (
    match f with
    | Fin.F1 => _
    | Fin.FS _ => _
    end
  ); reflexivity.
Defined.

Program Definition dep_elim_B (P : forall n : nat, B n -> Type) (f0 : P 0 dep_constr_B_0)
  (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f)) 
  (n : nat) (b : B n) 
: P n b. 
Proof.
  induction n.
  - replace b with dep_constr_B_0 by (apply eta_dep_constr_B_0). auto.
  - replace b with (dep_constr_B_1 (hd n b) n (tl n b)) by (apply eta_dep_constr_B_1). auto.
Defined.

(*
 * I expect all of our iotas to be trivial except iota_B_1:
 *)
Lemma iota_A_0 :
 forall (P : forall (n : nat), A n -> Type)
   (f0 : P 0 dep_constr_A_0)
   (f1 : forall (t : T) (n : nat) (f : A n), P n f -> P (S n) (dep_constr_A_1 t n f))
   (Q : P 0 dep_constr_A_0 -> Type),
   Q (dep_elim_A P f0 f1 0 dep_constr_A_0) ->
   Q f0.
Proof.
  intros. auto.
Defined.

Lemma iota_A_1 :
 forall (P : forall (n : nat), A n -> Type)
   (f0 : P 0 dep_constr_A_0)
   (f1 : forall (t : T) (n : nat) (f : A n), P n f -> P (S n) (dep_constr_A_1 t n f))
   (t : T) (n : nat) (f : A n) (Q : P (S n) (dep_constr_A_1 t n f) -> Type),
   Q (dep_elim_A P f0 f1 (S n) (dep_constr_A_1 t n f)) ->
   Q (f1 t n f (dep_elim_A P f0 f1 n f)).
Proof.
  intros. auto.
Defined.

(*
 * Needed for iota_B_0:
 *)
Lemma eta_refl_B_0:
  eta_dep_constr_B_0 dep_constr_B_0 = eq_refl.
Proof.
  intros. unfold eta_dep_constr_B_0.
  symmetry. eapply eq_trans.
  - symmetry. apply functional_extensionality_dep_good_refl.
  - f_equal. extensionality f.
    apply Fin.case0. apply f.
Defined.

Lemma iota_B_0 :
 forall (P : forall (n : nat), B n -> Type)
   (f0 : P 0 dep_constr_B_0)
   (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f))
   (Q : P 0 dep_constr_B_0 -> Type),
   Q (dep_elim_B P f0 f1 0 dep_constr_B_0) ->
   Q f0.
Proof.
  intros. simpl in X. rewrite eta_refl_B_0 in X. apply X.
Defined.

(*
 * Needed for iota_B_1:
 *)
Lemma eta_refl_B_1:
  forall (n : nat) (t : T) (b : B n),
    eta_dep_constr_B_1 n (dep_constr_B_1 t n b) = eq_refl.
Proof.
  intros. unfold eta_dep_constr_B_1. unfold hd. unfold tl. simpl.
  symmetry. eapply eq_trans.
  - symmetry. apply functional_extensionality_dep_good_refl.
  - f_equal. extensionality f.
    revert b. 
    refine (
    match f with
    | Fin.F1 => _
    | Fin.FS _ => _
    end); auto.
Defined.

Lemma iota_B_1 :
 forall (P : forall (n : nat), B n -> Type)
   (f0 : P 0 dep_constr_B_0)
   (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f))
   (t : T) (n : nat) (b : B n) (Q : P (S n) (dep_constr_B_1 t n b) -> Type),
   Q (dep_elim_B P f0 f1 (S n) (dep_constr_B_1 t n b)) ->
   Q (f1 t n b (dep_elim_B P f0 f1 n b)).
Proof.
  intros. simpl in X. unfold hd in X. unfold tl in X. simpl in X.
  rewrite eta_refl_B_1 in X. apply X.
Defined.

End Config.

Section Equivalence.

(*
 * These should form their own equivalence:
 *)
Definition f {n : nat} (a : A n) : B n :=
  dep_elim_A
    (fun n _ => B n) 
    dep_constr_B_0
    (fun t n b IH => dep_constr_B_1 t n IH)
    n
    a.

Definition g {n : nat} (b : B n) : A n :=
  dep_elim_B
    (fun n _ => A n) 
    dep_constr_A_0
    (fun t n b IH => dep_constr_A_1 t n IH)
    n
    b.

(*
 * This could be much easier, but I want to make a point of doing this algorithmically!
 *)
Lemma section {n : nat} (a : A n) : g (f a) = a.
Proof.
  apply dep_elim_A with (n := n) (v := a); unfold f; unfold g; intros.
  - unfold dep_constr_A_0 at 1. unfold dep_constr_A_0 at 1.
    apply (iota_B_0 (fun n _ => A n) dep_constr_A_0 (fun t n b IH => dep_constr_A_1 t n IH)).
    unfold dep_constr_B_0 at 1.
    apply (iota_A_0 (fun n _ => B n) dep_constr_B_0 (fun t n a IH => dep_constr_B_1 t n IH)).
    reflexivity.
  - unfold dep_constr_A_1 at 1. unfold dep_constr_A_1 at 1.
    replace (dep_constr_A_1 t n0 v) with (dep_constr_A_1 t n0 (g (f v))).
    + unfold g. unfold f.
      apply (iota_B_1 (fun n _ => A n) dep_constr_A_0 (fun t n b IH => dep_constr_A_1 t n IH) t n0).
      apply (iota_A_1 (fun n _ => B n) dep_constr_B_0 (fun t n a IH => dep_constr_B_1 t n IH)).
      reflexivity.
    + unfold g. unfold f. rewrite H. reflexivity. 
Defined.

(*
 * The point being that this direction should mirror this exactly, despite iota actually mattering here.
 *)
Lemma retraction {n : nat} (b : B n) : f (g b) = b.
Proof.
  apply dep_elim_B with (n := n) (b := b); unfold f; unfold g; intros.
  - unfold dep_constr_B_0 at 1. unfold dep_constr_B_0 at 1.
    apply (iota_A_0 (fun n _ => B n) dep_constr_B_0 (fun t n a IH => dep_constr_B_1 t n IH)).
    unfold dep_constr_A_0 at 1.
    apply (iota_B_0 (fun n _ => A n) dep_constr_A_0 (fun t n b IH => dep_constr_A_1 t n IH)).
    reflexivity.
  - unfold dep_constr_B_1 at 1. unfold dep_constr_B_1 at 1.
    replace (dep_constr_B_1 t n0 f0) with (dep_constr_B_1 t n0 (f (g f0))).
    + unfold f. unfold g.
      apply (iota_A_1 (fun n _ => B n) dep_constr_B_0 (fun t n a IH => dep_constr_B_1 t n IH) t n0).
      apply (iota_B_1 (fun n _ => A n) dep_constr_A_0 (fun t n a IH => dep_constr_A_1 t n IH)).
      reflexivity.
    + unfold f. unfold g. rewrite H. reflexivity. 
Defined.

End Equivalence.

(* hahaha holy shit *)
