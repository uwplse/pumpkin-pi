Require Import Coq.Program.Tactics.
Require Import PeanoNat.
Require Import Ornamental.Ornaments.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Set DEVOID search prove equivalence.
Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.
Set DEVOID lift type.

(*
 * Following "Internalizing Representation Independence with Univalence"
 * by Carlo Angiuli, Evan Cavallo, Anders Mortberg, and Max Zeuner,
 * what if we encode monoids and their structures, then look at nat and bin?
 * Then perhaps we can lift to the common interface automatically.
 *
 * Agda has definitional eta for Sigma types, so these types are quite
 * messy in Coq, which lacks definitional eta for Sigma types.
 * After one pass of this, it may be worth investigating whether
 * we can use records or somethign similar to encode some of these
 * types nicely in Coq.
 *)
Definition TypeWithStr (S : Type -> Type) : Type :=
  sigT (fun (X : Type) => S X).

Definition RawMonoidStructure (X : Type) : Type :=
  X * (X -> X -> X).

Definition RawMonoid := TypeWithStr RawMonoidStructure.

Definition MonoidAxioms (M : RawMonoid) : Type :=
  let (id, op) := projT2 M in
  ((forall x y z, op x (op y z) = (op (op x y) z)) * (* associativity *)
   (forall x, (op x id = x) * (op id x = x))). (* identity *)

Definition MonoidStructure (X : Type) : Type :=
  sigT (fun (S : RawMonoidStructure X) => MonoidAxioms (existT _ X S)).

Definition Monoid := TypeWithStr MonoidStructure.

(*
 * Still following that paper: structured equivalences of monoids.
 *)
Definition MonoidEquiv (M N : Monoid) (f : projT1 M -> projT1 N) (g : projT1 N -> projT1 M)
  (section : forall (x : projT1 M), g (f x) = x)
  (retraction : forall (y : projT1 N), f (g y) = y)
  : Type
:=
  let (id_M, op_M) := projT1 (projT2 M) in
  let (id_N, op_N) := projT1 (projT2 N) in
  ((f id_M = id_N) *
   (forall x y, f (op_M x y) = op_N (f x) (f y))).

(*
 * One way I deviated was by not forcing this in Set.
 * This might matter, but it might not, for us, and I prefer to work over Type.
 * So let's leave that for now.
 *
 * We don't have internal SIP. But what could external SIP get us?
 * Perhaps let's formulate the nat to bin problem this way and see!
 * We can show both of these are monoids:
 *)
Definition NatMonoid : Monoid :=
  existT
    (fun (X : Type) => MonoidStructure X)
    nat
    (existT
      (fun (S : RawMonoidStructure nat) => MonoidAxioms (existT RawMonoidStructure nat S)) 
      (0, Init.Nat.add)
      (Nat.add_assoc, fun x : nat => (Nat.add_0_r x, eq_refl))).

Program Definition BinMonoid : Monoid :=
  existT
    (fun (X : Type) => MonoidStructure X)
    N
    (existT
      (fun (S : RawMonoidStructure N) => MonoidAxioms (existT RawMonoidStructure N S)) 
      (0%N, N.add)
      (N.add_assoc, fun x : N => (N.add_0_r x, eq_refl))).

(*
 * But the point of the SIP paper is that it is sufficient to just show one
 * is a monoid, then define the monoid equivalence; then we should be able
 * to get that the other is a monoid for free. This is significant because
 * the proofs of N.add_0_r and so on can be annoying.
 * So what does this look like?
 * Does the standard equivalence work?
 *)
Definition equivIsMonoidEquiv
  : MonoidEquiv NatMonoid BinMonoid N.of_nat N.to_nat Nat2N.id N2Nat.id
:=
  (eq_refl, Nat2N.inj_add).

(*
 * It does.
 * But I guess the thing is, we won't have defined BinMonoid at all.
 * Rather we should be able to infer it from N.of_nat and N.to_nat,
 * plus Nat2N.id and N2Nat.id, plus N.add.
 * Given that the equivalence is a monoid equivalence.
 * Is that right?
 * How?
 *
 * The paper says that there's one property we need to show in order to get this.
 * Maybe showing that property will help us understand how automation follows.
 * This is already done for us, but does it work only by induction on nat?
 * It seems to use section, so I'm a bit confused about how to do it only
 * by induction over nat? I should ask Carlo about what he means by
 * "which can readily be achieved by N-induction" on page 15.
 * 
 * Anders Mortberg sent me the Agda code, and it is obvious but only with a lemma first.
 * The lemma in Anders' code isn't quite what we need I guess.
 * And it turns out these proofs, even in Anders' code, are not done purely over nat.
 * They use the equivalent of BinPos.Pos.add_succ_l.
 * Even Anders proves this by induction over BinPos.Pos (as does the Coq standard library).
 * Whatever, okay, let's do it in Coq however it works.
 *)
Lemma of_succ_nat_unfold:
  forall (n : nat),
    BinPos.Pos.of_succ_nat n =
    match n with
    | 0 => xH
    | S _ => BinPos.Pos.succ (BinPos.Pos.of_nat n)
    end.
Proof.
  intros n. induction n; auto.
  simpl. f_equal. apply IHn.
Defined.

Lemma add_pos_succ_ok:
  forall (x y : nat),
    BinPos.Pos.of_succ_nat (x + S y) =
    BinPos.Pos.add (BinPos.Pos.of_succ_nat x) (BinPos.Pos.of_succ_nat y).
Proof.
  intros x y. induction x.
  - symmetry. apply BinPos.Pos.add_1_l. (* <-- uses pos-induction *)
  - replace (BinPos.Pos.of_succ_nat (S x)) with (BinPos.Pos.succ (BinPos.Pos.of_nat (S x))).
    + rewrite BinPos.Pos.add_succ_l. (* <-- uses pos-induction *)
      simpl. f_equal. rewrite IHx. f_equal.
      apply of_succ_nat_unfold.
    + simpl. symmetry. f_equal. apply of_succ_nat_unfold. 
Defined.

(*
 * Okay, then:
 *)
Lemma structure_preserving:
  forall (x y : nat),
    N.of_nat (x + y) = N.add (N.of_nat x) (N.of_nat y).
Proof.
  intros x. induction x; intros.
  - reflexivity.
  - induction y; intros.
    + simpl. f_equal. f_equal. apply Nat.add_0_r.
    + simpl. f_equal. apply add_pos_succ_ok.
Defined.

(*
 * So it still relies on induction over pos at some point, I think because
 * it needs to eta-expand pos, effectively.
 * Is there a way to never, ever induct over bin here,
 * without basically defining the induction principle for bin in terms of nat?
 * No idea. But even Anders doesn't do this.
 * So I'm confused about the point he was making.
 *
 * Nonetheless, let us suppose that we have this lemma.
 * What kind of automation can we get from this?
 * And do we need this lemma proven, or only for the fact that it holds to be true?
 * And so on.
 *
 * I guess the first question is how we can get a BinMonoid from a NatMonoid.
 *)
Module Automation.

(*
 * Given a BinMonoid, we can use our proof to define:
 *)
Definition equivIsMonoidEquiv
  : MonoidEquiv NatMonoid BinMonoid N.of_nat N.to_nat Nat2N.id N2Nat.id
:=
  (eq_refl, structure_preserving).


Print equivIsMonoidEquiv.

(*
 * If we don't have a BinMonoid, implicitly this still has this type:
 *)
Definition equivIsMonoidEquivImplicit :=
  (@eq_refl N (N.of_nat O), (* identity checks out *)
   structure_preserving).   (* structure preserving over addition *)

(*
 * In effect, it is like we have defined an inductive type where the 
 * constructors are O and addition.
 * And what we have here is sort of like the iota rules for
 * each constructor.
 *)
Check equivIsMonoidEquivImplicit.

(*
 * If we translate it to such a problem, maybe it is painless to use the
 * existing PUMPKIN Pi infrastructure?
 *
 * I don't know, but let's see if there's a normal equivalence between
 * NatMonoid and BinMonoid first.
 * I think the point is for any Monoid, we can show this equivalence.
 *)
Definition A := {s : RawMonoidStructure nat & MonoidAxioms (existT RawMonoidStructure nat s)}.
Definition B := {s : RawMonoidStructure N & MonoidAxioms (existT RawMonoidStructure N s)}.

Program Definition f : A -> B.
Proof.
  intros n. induction n. induction x.
  exists (N.of_nat a, fun n1 n2 => N.of_nat (b (N.to_nat n1) (N.to_nat n2))).
  unfold MonoidAxioms in *; simpl in *.
  destruct p. split; intros.
  - f_equal. repeat rewrite Nat2N.id. apply e.
  - rewrite Nat2N.id. specialize (p (N.to_nat x)). destruct p. split.
    + rewrite e0. apply N2Nat.id.
    + rewrite e1. apply N2Nat.id.
Defined.

Program Definition g : B -> A.
Proof.
  intros n. induction n. induction x.
  exists (N.to_nat a, fun n1 n2 => N.to_nat (b (N.of_nat n1) (N.of_nat n2))).
  unfold MonoidAxioms in *; simpl in *.
  destruct p. split; intros.
  - f_equal. repeat rewrite N2Nat.id. apply e.
  - rewrite N2Nat.id. specialize (p (N.of_nat x)). destruct p. split.
    + rewrite e0. apply Nat2N.id.
    + rewrite e1. apply Nat2N.id.
Defined.

(*
 * Ah, I think this only holds up to funext :).
 *)
Lemma section :
  forall (a : A), g (f a) = a.
Proof.
  intros a. induction a. induction x. simpl.
  apply eq_existT_uncurried. 
  assert ((N.to_nat (N.of_nat a),
  fun n1 n2 : nat =>
  N.to_nat (N.of_nat (b (N.to_nat (N.of_nat n1)) (N.to_nat (N.of_nat n2))))) =
  (a, b)).
  - rewrite Nat2N.id. admit.
Abort.

(*
 * In fact even the equivalence between the RawMonoidStructures only
 * holds up to funext.
 *
 * But since it's metatheoretically true, I think the idea is that you
 * can transform any A into a B, and it will preserve transport?
 * But surely definitional equality becomes annoying at some point.
 * It always does.
 *
 * I am curious what happens if we just do the dumbest possible thing
 * and transform the operation.
 * I think we will need an iota equivalent.
 * I super want an inductive framing of this problem.
 *
 * I also bet there's a problem in unifying with addition, maybe
 * solvable by way of annotations.
 *
 * Are there any useful equivalences we can show directly, internally?
 *)

End Automation.
