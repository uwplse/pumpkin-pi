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

(* cons---not sure what this looks like *)
Parameter dep_constr_B_1 : forall (t : T) (n : nat) (f : B n), B (S n).

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

(* TODO stuck on defining these, if possible*)
Parameter hd : forall (n : nat) (f : B (S n)), T.
Parameter tail : forall (n : nat) (f : B (S n)), B n.

Axiom tail_OK:
  forall (n : nat) (b : B (S n)),
    dep_constr_B_1 (hd n b) n (tail n b) = b.

(* Over vectors, sanity check: *)
Program Definition hd_vect : forall (n : nat) (f : A (S n)), T.
Proof.
  intros. apply (Vector.hd f).
Defined.

Program Definition tl_vect : forall (n : nat) (f : A (S n)), A n.
Proof.
  intros. apply (Vector.tl f).
Defined.

Lemma tail_OK_vect:
  forall (n : nat) (a : A (S n)),
    dep_constr_A_1 (hd_vect n a) n (tl_vect n a) = a.
Proof.
  intros. symmetry. apply VectorSpec.eta.
Defined.

Program Definition dep_elim_B (P : forall n : nat, B n -> Type) (f0 : P 0 dep_constr_B_0)
  (f1 : forall (t : T) (n : nat) (f : B n), P n f -> P (S n) (dep_constr_B_1 t n f)) 
  (n : nat) (b : B n) 
: P n b. 
Proof.
  induction n.
  - rewrite (funext b (fun f : Fin.t 0 => Fin.case0 (fun _ : Fin.t 0 => T) f)); auto.
    intros f. apply Fin.case0. apply f.
  - pose (f1 (hd n b) n (tail n b) (IHn (tail n b))).
    replace b with (dep_constr_B_1 (hd n b) n (tail n b)); auto.
    apply tail_OK.
Defined.

(* FinVec→Vec : {n : ℕ} → FinVec A n → Vec A n
FinVec→Vec {n = zero}  xs = []
FinVec→Vec {n = suc _} xs = xs zero ∷ FinVec→Vec (λ x → xs (suc x))

Vec→FinVec : {n : ℕ} → Vec A n → FinVec A n
Vec→FinVec (xs : Vec A n) (f : Fin n)  = lookup f xs

lookup : ∀ {n} {A : Type ℓ} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs*)

