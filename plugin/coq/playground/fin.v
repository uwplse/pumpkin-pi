(*
 * Vectors and Fin (also from Anders)
 *)
Require Import Ornamental.Ornaments.
Set DEVOID lift type.

Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.

Section Config.

Parameter T : Type.

(* needed for this equivalence *)
Axiom funext : forall {X} {Y : X -> Type},
  forall (f g : forall x : X, Y x),
  (forall x, f x = g x) -> f = g.

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

Program Definition dep_constr_B_1 (t : T) (n : nat) (f : B n) : B (S n).
Proof.
  unfold B in *. intros. apply @Fin.rectS with (n := n).
  - intros. apply t.
  - intros. apply X.
  - apply H.
Defined.

Definition eta_A (n : nat) (a : A n) : A n := a.
Definition eta_B (n : nat) (b : B n) : B n := b.

(* might need this instead, unsure: *)
(*Definition eta_A (n m : nat) (H : n = m) (a : A n) : A m := eq_rect m A a n H.*)

Definition dep_elim_A (P : forall n : nat, A n -> Type) (f0 : P 0 dep_constr_A_0)
  (f1 : forall (t : T) (n : nat) (v : A n), P n v -> P (S n) (dep_constr_A_1 t n v)) 
  (n : nat) (v : A n) 
: P n v 
:=
  Vector.t_rect T P f0 f1 n v.

Program Definition dep_elim_B (P : forall n : nat, B n -> Type) (f0 : P 0 dep_constr_B_0)
  (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f)) 
  (n : nat) (f : B n) 
: P n f. 
Proof.
  assert (prod (P n f) (Fin.t (S n))).
  - induction n.
    + intros. rewrite (funext f (fun f : Fin.t 0 => Fin.case0 (fun _ : Fin.t 0 => T) f)).
      * split; auto. constructor.
      * apply Fin.case0.
    + split.
      * unfold B in f. unfold dep_constr_B_1 in f1. apply @Fin.caseS' with (n := n).
        -- apply IHn. unfold B. intros. apply f. constructor.
        -- specialize (IHn (fun (x : Fin.t n) => f (FS x))). destruct IHn. specialize (f1 (f t) n (fun (x : Fin.t n) => f (FS x)) p).
           rewrite (funext f (dep_constr_B_1 (f t) n (fun x : Fin.t n => f (FS x)))); auto.
           (* ??? ugh *)
           admit.
Admitted.

  - 


