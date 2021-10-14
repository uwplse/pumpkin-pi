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
: Type :=
  let (id_M, op_M) := projT1 (projT2 M) in
  let (id_N, op_N) := projT1 (projT2 N) in
  ((f id_M = id_N) *
   (forall x y, f (op_M x y) = op_N (f x) (f y))).

