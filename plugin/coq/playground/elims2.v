Add LoadPath "coq/playground".
Require Import Vector.
Require Import List.
Require Import elims.

Notation vector := Vector.t.
Notation nilV := Vector.nil.
Notation consV := Vector.cons.

(*
 * More of an attempt at understanding why lifting eliminators is OK, formally.
 *)

(* --- Algebraic ornaments --- *)

Module Algebraic.

Definition transport_A_B {T} := list_to_t T.
Definition transport_B_A {T} := list_to_t_inv T.

(*
 * Dependent constructors with explicit transport:
 *)
Definition Tenilv T := transport_A_B (@nil T).
Definition Teconsv T t s := transport_A_B (@cons T t (transport_B_A s)).

(*
 * Dependent constructors with implicit transport:
 *)
Definition enilv T := existT _ 0 (nilV T).
Definition econsv T t s := existT _ (S (projT1 s)) (@consV T t (projT1 s) (projT2 s)).

(*
 * Correspondence:
 *)
Lemma Tenilv_enilv:
  forall (T : Type), Tenilv T = enilv T.
Proof.
  reflexivity.
Defined.

Lemma transport_cons:
  forall (T : Type) (t : T) (l : list T),
    transport_A_B (@cons T t l) =
    existT _ (S (projT1 (transport_A_B l))) (@consV T t (projT1 (transport_A_B l)) (projT2 (transport_A_B l))).
Proof.
  reflexivity.
Defined.

Lemma Teconsv_econsv:
  forall (T : Type) (t : T) (s : sigT (vector T)),
    Teconsv T t s = econsv T t s.
Proof.
  intros. unfold Teconsv, econsv.
  rewrite transport_cons.
  rewrite list_to_t_retraction.
  auto.
Defined.

(*
 * Dependent elimination with explicit transport:
 *)
Definition TQ {T : Type} (P : sigT (vector T) -> Type) := fun l => P (transport_A_B l).

Program Definition Tpenilv {T : Type} (P : sigT (vector T) -> Type) :
  P (Tenilv T) -> 
  TQ P (@nil T).
Proof.
  intros pnil. apply pnil.
Defined.

Definition Tpeconsv {T : Type} (P : sigT (vector T) -> Type) :
  (forall t (s : sigT (vector T)), P s -> P (Teconsv T t s)) ->
  (forall t (l : list T), TQ P l -> TQ P (@cons T t l)).
Proof.
  intros pcons. intros t l IHl. unfold TQ.
  specialize (pcons t (transport_A_B l)).
  rewrite Teconsv_econsv in pcons.
  apply pcons.
  apply IHl.
Defined.

Lemma PQ_retract:
  forall {T} P s,
    @TQ T P (transport_B_A s) = P s.
Proof.
  intros. unfold TQ. f_equal. apply list_to_t_retraction.
Defined.

Lemma TsigT_vect_rect :
  (forall (T : Type) (P : list T -> Type),
    P nil ->
    (forall (t : T) (l : list T), P l -> P (@cons T t l)) ->
    forall (l : list T), P l) ->
  (forall (T : Type) (P : sigT (vector T) -> Type),
    P (Tenilv T) ->
    (forall (t : T) (s : sigT (vector T)), P s -> P (Teconsv T t s)) ->
    forall (s : sigT (vector T)), P s).
Proof.
  intros list_rect T P qnil qcons s. rewrite <- PQ_retract. 
  apply (@list_rect T (TQ P) (Tpenilv P qnil) (Tpeconsv P qcons) (transport_B_A s)).
Defined.

Definition sigT_vect_rect_via_list_rect := TsigT_vect_rect list_rect.

(*
 * Dependent elimination with implicit transport:
 *)
Lemma sigT_vect_rect :
  (forall (T : Type) (P : sigT (vector T) -> Type),
    P (enilv T) ->
    (forall (t : T) (s : sigT (vector T)), P s -> P (econsv T t s)) ->
    forall (s : sigT (vector T)), P s).
Proof.
  intros T P qnil qcons s. induction s. induction p.
  - apply qnil.
  - specialize (qcons h (existT _ n p) IHp). (* <- note reconstruction *)
    apply qcons.
Defined.

(* Where we have eliminated something, we reconstruct it inside of the innermost eliminator. *)

End Algebraic.

(* --- Let's see --- *)

Inductive Foo : nat -> Type :=
| f : forall (n : nat), Foo n.

Inductive Bar : nat -> Type :=
| f1 : Bar 0
| f2 : forall (n : nat), Bar n -> Bar (S n).

Program Definition Foo_to_Bar : forall (n : nat), Foo n -> Bar n.
Proof.
  intros. induction H.
  - induction n.
    + apply f1.
    + apply f2. apply IHn.
Defined.

Program Definition Bar_to_Foo : forall (n : nat), Bar n -> Foo n.
Proof.
  intros. apply f.
Defined.

Theorem Foo_to_Bar_section:
  forall (n : nat) (f : Foo n), Bar_to_Foo n (Foo_to_Bar n f) = f.
Proof.
  intros. induction f0. reflexivity.
Defined.

Theorem Foo_to_Bar_retraction:
  forall (n : nat) (b : Bar n), Foo_to_Bar n (Bar_to_Foo n b) = b.
Proof.
  intros. induction b.
  - auto.
  - simpl. simpl in IHb. rewrite IHb. auto.
Defined.

(*
 * Constructor:
 *)
Definition Tbarf (n : nat) :=
  Foo_to_Bar n (f n).

Definition barf (n : nat) :=
  nat_rect Bar f1 (fun _ IHn => f2 _ IHn) n.

Lemma Tbarf_barf:
  forall (n : nat), Tbarf n = barf n.
Proof.
  reflexivity.
Defined.

Lemma Foo_Bar_P:
  forall (n : nat) (P : forall (n : nat), Bar n -> Type) (b : Bar n), 
    P n (Foo_to_Bar n (Bar_to_Foo n b)) ->
    P n b.
Proof.
  intros. rewrite Foo_to_Bar_retraction in X. apply X.
Defined.

Lemma Bar_Foo_rect:
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (barf n)) ->
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b.
  apply Foo_Bar_P. (* in algorithm, though, we internalize this retraction call? How? *)
  apply pf0.
Defined.

(* internalized retraction becomes: *)
Lemma Bar_nat_rect_1:
  forall (n : nat) (b : Bar n),
    Foo_to_Bar n (f n) = b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. unfold Foo_to_Bar in IHb. simpl in IHb. rewrite IHb. reflexivity.
Defined.

Lemma Bar_nat_rect:
  forall (n : nat) (b : Bar n),
    nat_rect Bar f1 (fun (n : nat) (IHn : Bar n) => f2 n IHn) n = b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. rewrite IHb. reflexivity.
Defined.

Lemma Bar_Foo_rect':
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (barf n)) ->
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b.
  rewrite <- Bar_nat_rect.
  apply pf0.
Defined.

(* internalized section becomes: *)

Theorem Foo_to_Bar_section_1:
  forall (n : nat) (f : Foo n), Bar_to_Foo n (nat_rect Bar f1 (fun (n : nat) (IHn : Bar n) => f2 n IHn) n) = f.
Proof.
  intros. induction f0. reflexivity.
Defined.

Theorem Foo_to_Bar_section_2:
  forall (n : nat) (f0 : Foo n), nat_rect Foo (f 0) (fun (n : nat) (IHn : Foo n) => f (S n)) n = f0.
Proof.
  intros. induction f0. induction n; reflexivity. (* whyyyy *)
Defined.

Lemma Foo_Bar_rect:
  forall P : forall n : nat, Foo n -> Type,
    P 0 (f 0) ->
    (forall (n : nat) (f0 : Foo n), P n (f n) -> P (S n) (f (S n))) ->
    forall (n : nat) (b : Foo n), P n (f n).
Proof.
  intros P pf1 pf2 n fo. induction n. (* <-- internalized Foo_to_Bar *)
  - apply pf1.
  - apply (pf2 n (f n)). apply IHn. apply f. (* <-- internalized Bar_to_Foo *)
Defined.

(* IDK, I'm confused by how to define these eliminators more generally *)
