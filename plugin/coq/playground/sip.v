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
 *)


