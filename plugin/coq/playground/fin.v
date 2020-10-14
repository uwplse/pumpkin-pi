(*
 * Vectors and Fin (also from Anders)
 * Thanks to James Wilcox for the missing gaps that I needed!
 * https://gist.github.com/wilcoxjay/10cc817d20ad7148899c3725a1ebf06e
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

Definition dep_constr_B_1 (t : T) (n : nat) (b : B n) : B (S n) :=
  fun f =>
  match f with
  | Fin.F1 => fun _ => t
  | Fin.FS f' => fun b' => b' f'
  end b.

Definition eta_A (n : nat) (a : A n) : A n := a.
Definition eta_B (n : nat) (b : B n) : B n := b.

(* might need this instead, unsure: *)
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

Lemma tl_OK:
  forall (n : nat) (b : B (S n)),
    dep_constr_B_1 (hd n b) n (tl n b) = b.
Proof.
  intros n b.
  apply funext.
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
  - rewrite (funext b (fun f : Fin.t 0 => Fin.case0 (fun _ : Fin.t 0 => T) f)); auto.
    intros f. apply Fin.case0. apply f.
  - replace b with (dep_constr_B_1 (hd n b) n (tl n b)); auto.
    apply tl_OK.
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
   Q (dep_elim_A P f0 f1 0 dep_constr_A_0).
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

Lemma iota_B_0 :
 forall (P : forall (n : nat), B n -> Type)
   (f0 : P 0 dep_constr_B_0)
   (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f))
   (Q : P 0 dep_constr_B_0 -> Type),
   Q (dep_elim_B P f0 f1 0 dep_constr_B_0) ->
   Q (dep_elim_B P f0 f1 0 dep_constr_B_0).
Proof.
  intros. auto.
Defined.

Lemma iota_B_1 :
 forall (P : forall (n : nat), B n -> Type)
   (f0 : P 0 dep_constr_B_0)
   (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f))
   (t : T) (n : nat) (f : B n) (Q : P (S n) (dep_constr_B_1 t n f) -> Type),
   Q (dep_elim_B P f0 f1 (S n) (dep_constr_B_1 t n f)) ->
   Q (f1 t n f (dep_elim_B P f0 f1 n f)).
Proof.
  intros. admit. (* TODO indeed! *)
Admitted.
