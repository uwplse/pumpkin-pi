From Coq Require Vector.

(*
 * Compatibility with SSReflect is basically impossible. Here's what we can
 * do with no changes to DEVOID. But this doesn't get you far enough to use
 * any lemmas from SSReflect. Will be a WIP.
 *)
Definition vector := Vector.t.

Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID search prove coherence.
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

Record Concrete :=
  {
    concreteField : vector bool 2;
  }.

Find ornament list vector.

Preprocess length as length'.

Definition tuple n T : Type := { l : list T & length' T l = n }.

Record Abstract :=
  {
    abstractField : tuple 2 bool
  }.

(* --- Custom indexing function --- *)

Lemma length_index:
  forall T l,
    length' T l = list_to_t_index T l.
Proof.
  intros T l. induction l; auto.
Defined.

Definition rew_index_length T l :=
  @eq_rect_r _ (list_to_t_index T l) _ (projT2 (list_to_t T l)) (length' T l) (length_index T l).

Definition f (T : Type) (l : list T) : sigT (Vector.t T).
  exists (length' T l). apply (rew_index_length T l).
Defined.

Definition g (T : Type) (s : sigT (Vector.t T)) : list T.
  apply (list_to_t_inv T s).
Defined.

Save ornament list Vector.t { promote = f; forget = g }.
Lift list vector in tuple as tuple'.

Scheme Induction for Abstract Sort Prop.
Scheme Induction for Abstract Sort Set.
Scheme Induction for Abstract Sort Type.

Lift list vector in Abstract as Concrete'.

(*
 * For now, you need to prove this by hand (plus lots of other things are broken):
 *)

Definition fakeAdvanceMessageConcrete' (a : Concrete') : Concrete'.
  induction a. induction abstractField0.
  constructor. econstructor. apply p.
Defined.

Definition Concrete'_Concrete (c : Concrete') : Concrete.
  induction c. induction abstractField0. induction x. constructor.
  simpl in p. rewrite <- p. apply p0.
Defined.

Definition Concrete_Concrete' (c : Concrete) : Concrete'.
  induction c. constructor. exists (existT _ _ concreteField0).
  reflexivity.
Defined.

Lemma section: forall c, Concrete_Concrete' (Concrete'_Concrete c) = c.
  induction c. induction abstractField0. induction x. simpl in *. subst.
  f_equal.
Defined.

Lemma retraction: forall c, Concrete'_Concrete (Concrete_Concrete' c) = c.
  induction c. reflexivity.
Defined.

(*
 * This means you also need to transport by hand:
 *)
Definition fakeAdvanceMessageConcrete (c : Concrete) : Concrete.
  apply Concrete'_Concrete.
  apply fakeAdvanceMessageConcrete'.
  apply Concrete_Concrete'.
  apply c.
Defined.

From mathcomp Require Import
     eqtype
     seq
     ssreflect
     ssrnat
.

(*
On the other hand, destructing a fixed-size [tuple] is easy as equalities are
delayed.
 *)
Definition inBoundsTuple : forall (corked : tuple' 2 bool), Prop.
  move => [] [] // n1 [] // b1 n2 t eq. simpl in eq. exact (b1 = false).
Defined.

(* etc... *)

(*
Here is when it really hurts: [inBoundsConcrete] depends on the vector
being of size 2, but that dependency is not explicit in the type, so one cannot
abstract over it.
 *)
Definition noDoubleCorkUncorkGeneralized n v :=
  match n as n' return Vector.t bool n' -> Prop with
  | 2 => fun v =>
          inBoundsConcrete {| concreteField := v |} ->
          inBoundsConcrete (fakeAdvanceMessageConcrete {| concreteField := v |})
  | _ => fun _ => True
  end v.

Theorem noDoubleCorkUncorkConcrete
  : forall c,
    inBoundsConcrete c ->
    inBoundsConcrete (fakeAdvanceMessageConcrete c).
Proof.
  move => [].
  cut (forall c, noDoubleCorkUncorkGeneralized 2 c) => // c.
  have := eq_refl 2.
  move : {1 3 4} 2 c => n2.
  elim / @Vector.t_ind => // h1 n1 t _.
  move : t.
  elim / @Vector.t_ind => // h2 [] //.
  apply : (Vector.case0 (A := bool)) => _ _.
  rewrite / noDoubleCorkUncorkGeneralized //=.
Qed.

(*
Compare the [tuple] version:
 *)
Theorem noDoubleCorkUncorkAbstract
  : forall a,
    inBoundsAbstract a ->
    inBoundsAbstract (fakeAdvanceMessageAbstract a).
Proof.
  move => [] [] [] // b1 [] // b2 [] //.
Qed.
