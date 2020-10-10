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
 * Eta is trivial:
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
  unfold dep_constr_B_0 in f0. unfold eta_B.
  rewrite <- retraction. apply f0.
Defined.

(*
 * No inductive cases, so trivial iota:
 *)
Definition iota_A_0 (P : A -> Type) (f0 : forall (a : A), P (dep_constr_A_0 a)) (a : A) (Q : P (dep_constr_A_0 a) -> Type) (H : Q (f0 a)) :=
  H.

Definition iota_B_0 (P : B -> Type) (f0 : forall (a : A), P (dep_constr_B_0 a)) (a : A) (Q : P (dep_constr_B_0 a) -> Type) (H : Q (f0 a)) :=
  H.

(*
 * These should form their own equivalence:
 *)
Definition f' (a : A) : B :=
  dep_elim_A (fun _ => B) (fun a => dep_constr_B_0 a) a.

Definition g' (b : B) : A :=
  dep_elim_B (fun _ => A) (fun a => dep_constr_A_0 a) b.

Lemma section' (a : A) : g' (f' a) = a.
Proof.
  (* is it possible to get this only the configuration terms, not using section directly? 
     if not, is it possible to redefine the configuration terms such that this is possible? *)
Admitted.

Lemma retraction' (b : B) : f' (g' b) = b.
Proof.
  (* is it possible to get this only the configuration terms, not using retraction directly? 
     if not, is it possible to redefine the configuration terms such that this is possible? *)
Admitted.


