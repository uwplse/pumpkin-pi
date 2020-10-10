(*
 * I wonder...
 *)
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.

Set DEVOID lift type.

Parameter A : Type.
Parameter B : Type.

Parameter f : A -> B.
Parameter g : B -> A.

Parameter section : forall (a : A), g (f a) = a.
Parameter retraction : forall (b : B), f (g b) = b.

Definition retraction_adjoint := Adjoint.fg_id' f g section retraction.

Definition ignore_A := A.

(*
 * Then we get:
 *)
Definition dep_constr_A_0 (a : ignore_A) : A := a.
Definition dep_constr_B_0 (a : ignore_A) : B := f a.

(*
 * Eta:
 *)
Definition eta_A (a : A) := a.
Definition eta_B (b : B) := b.

(*
 * This gives us dep_elim:
 *)
Program Definition dep_elim_A (P : A -> Type) (f0 : forall (a : A), P (dep_constr_A_0 a)) (a : A) : P (eta_A a).
Proof.
  apply f0.
Defined.

Program Definition dep_elim_B (P : B -> Type) (f0 : forall (a : A), P (dep_constr_B_0 a)) (b : B) : P (eta_B b).
Proof.
  rewrite <- retraction. apply f0.
Defined.

(*
 * iota over A is easy, but for iota over B it is a bit weirder:
 *)
Lemma iota_A_0 :
  forall (P : A -> Type) (f0 : forall (a : A), P (dep_constr_A_0 a)) (a : A) (Q : P (dep_constr_A_0 a) -> Type),
    Q (dep_elim_A P f0 (dep_constr_A_0 a)) ->
    Q (f0 a).
Proof.
  intros. apply X.
Defined.

(* 
 * This one we can always do:
 *)
Lemma iota_B_aux:
  forall a,
    dep_elim_B 
      (fun _ : B => A)
      (fun a0 : A => dep_constr_A_0 a0)
      (dep_constr_B_0 a)
    =
    dep_constr_A_0 a.
Proof.
  intros a. unfold dep_elim_B. 
  unfold dep_constr_A_0. unfold dep_constr_B_0. unfold eta_B.
  rewrite retraction.
  apply section.
Defined.
(*
 * But?
 *)
Lemma iota_B_aux_gen:
  forall (P : B -> Type) (a : A) (f0 : forall (a : A), P (dep_constr_B_0 a)),
    dep_elim_B 
      P
      (fun a0 : A => f0 a0)
      (dep_constr_B_0 a)
    =
    f0 a.
Proof.
  intros P a f0. unfold dep_elim_B. 
  unfold dep_constr_A_0. unfold dep_constr_B_0. unfold eta_B.
  unfold dep_constr_B_0 in *.
  admit. (* unsure how to solve, if possible *)
Admitted.

(*
 * Can we always do that one??? I don't know!
 * But it's the remaining proof obligation (paper probably should clarify this better for
 * the base case). So we can construct _some_ configuration from an equivalence
 * if and only if we can prove this.
 *)
Lemma iota_B_0 :
  forall (P : B -> Type) (f0 : forall (a : A), P (dep_constr_B_0 a)) (a : A) (Q : P (dep_constr_B_0 a) -> Type),
    Q (dep_elim_B P f0 (dep_constr_B_0 a)) ->
    Q (f0 a).
Proof.
  intros. unfold dep_elim_B in X. unfold eta_B in X. unfold dep_constr_B_0 in X.
  rewrite <- iota_B_aux_gen. apply X.
Defined.

(*
 * These should form their own equivalence:
 *)
Definition f' (a : A) : B :=
  dep_elim_A (fun _ => B) (fun a => dep_constr_B_0 a) a.

Definition g' (b : B) : A :=
  dep_elim_B (fun _ => A) (fun a => dep_constr_A_0 a) b.

(*
 * Ah, here is yet another surprise!
 * These each follow by _both_ iota, not just by one.
 * Need to think more and fix paper appropriately.
 * The idea that it forms an equivalence is true, but my proof sketch of section
 * and retraction doesn't follow in all cases---sometimes need both iota.
 * What is the meaning of this? And when will I eat dinner?
 *)
Lemma section' (a : A) : g' (f' a) = a.
Proof.
  replace a with (eta_A a) by reflexivity.
  apply dep_elim_A.
  intros a0.
  unfold f'. unfold g'.
  unfold dep_constr_A_0 at 1. unfold dep_constr_A_0 at 1.
  apply (iota_B_0 (fun _ => A) (fun a0 : A => dep_constr_A_0 a0) a0).
  apply (iota_A_0 (fun _ => B) (fun a0 : A => dep_constr_B_0 a0) a0).
  reflexivity.
Defined.

Lemma retraction' (b : B) : f' (g' b) = b.
Proof.
  replace b with (eta_B b) by reflexivity.
  apply dep_elim_B.
  intros a.
  unfold f'. unfold g'.
  unfold dep_constr_B_0 at 1. unfold dep_constr_B_0 at 1.
  apply (iota_A_0 (fun _ => B) (fun a0 : A => dep_constr_B_0 a0) a).
  apply (iota_B_0 (fun _ => A) (fun a0 : A => dep_constr_A_0 a0) a).
  reflexivity.
Defined.

