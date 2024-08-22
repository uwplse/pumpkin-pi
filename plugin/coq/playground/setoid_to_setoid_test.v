Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.
Require Import SetoidClass.

Inductive A : Set :=
| oneA : A
| twoA : A
| threeA : A.

Definition eqA (a1 a2 : A) :=
  match a1, a2 with
  | oneA, oneA => True
  | oneA, twoA => False
  | oneA, threeA => False
  | twoA, oneA => False
  | twoA, twoA => True
  | twoA, threeA => True
  | threeA, oneA => False
  | threeA, twoA => True
  | threeA, threeA => True
  end.

Instance eqA_refl : Reflexive eqA.
Proof.
  intros a.
  unfold eqA.
  destruct a; auto.
Qed.

Instance eqA_sym : Symmetric eqA.
Proof.
  unfold eqA.
  intros a1 a2 H.
  destruct a1;
  destruct a2;
  auto.
Qed.

Instance eqA_trans : Transitive eqA.
Proof.
  unfold eqA.
  intros a1 a2 a3 H1 H2.
  destruct a1;
  destruct a2;
  destruct a3;
  auto.  
Qed.

Instance eqA_equiv : Equivalence eqA.
Proof.
  split.
  apply eqA_refl.
  apply eqA_sym.
  apply eqA_trans.
Qed.

Definition depConstrAOne := oneA.
Definition depConstrATwo := twoA.

Definition depRecA (C : Type) (c1 c2 : C) (a : A) : C :=
  match a with
  | oneA => c1
  | twoA => c2
  | threeA => c2
  end.

Definition iotaRecAOne (C : Type) (c1 c2 : C) (a : A) :
  forall (Q : C -> Type),
    Q c1 -> Q (depRecA C c1 c2 depConstrAOne).
Proof.
  intros.
  apply X.
Qed.

Definition iotaRecATwo (C : Type) (c1 c2 : C) (a : A) :
  forall (Q : C -> Type),
    Q c2 -> Q (depRecA C c1 c2 depConstrATwo).
Proof.
  intros.
  apply X.
Qed.

Definition etaA (a : A) := a.

Inductive B : Set :=
| oneB : B
| twoB : B
| threeB : B.

Definition eqB (b1 b2 : B) :=
  match b1, b2 with
  | oneB, oneB => True
  | oneB, twoB => True
  | oneB, threeB => False
  | twoB, oneB => True
  | twoB, twoB => True
  | twoB, threeB => False
  | threeB, oneB => False
  | threeB, twoB => False
  | threeB, threeB => True
  end.

Instance eqB_refl : Reflexive eqB.
Proof.
  intros a.
  unfold eqB.
  destruct a; auto.
Qed.

Instance eqB_sym : Symmetric eqB.
Proof.
  unfold eqB.
  intros a1 a2 H.
  destruct a1;
  destruct a2;
  auto.
Qed.

Instance eqB_trans : Transitive eqB.
Proof.
  unfold eqB.
  intros a1 a2 a3 H1 H2.
  destruct a1;
  destruct a2;
  destruct a3;
  auto.  
Qed.

Instance eqB_equiv : Equivalence eqB.
Proof.
  split.
  apply eqB_refl.
  apply eqB_sym.
  apply eqB_trans.
Qed.

Definition depConstrBOne := oneB.
Definition depConstrBTwo := threeB.

Definition depRecB (C : Type) (c1 c2 : C) (a : B) : C :=
  match a with
  | oneB => c1
  | twoB => c1
  | threeB => c2
  end.

Definition iotaRecBOne (C : Type) (c1 c2 : C) (a : B) :
  forall (Q : C -> Type),
    Q c1 -> Q (depRecB C c1 c2 depConstrBOne).
Proof.
  intros.
  apply X.
Qed.

Definition iotaRecBTwo (C : Type) (c1 c2 : C) (a : B) :
  forall (Q : C -> Type),
    Q c2 -> Q (depRecB C c1 c2 depConstrBTwo).
Proof.
  intros.
  apply X.
Qed.

Definition etaB (a : B) := a.

Definition promote (a : A) : B :=
  depRecA B depConstrBOne depConstrBTwo a.

Definition forget (b : B) : A :=
  depRecB A depConstrAOne depConstrATwo b.

Save setoid A B { promote = promote ; forget = forget ; types_a = A ; rels_a = eqA ; equiv_proofs_a = eqA_equiv ; types_b = B ; rels_b = eqB ; equiv_proofs_b = eqB_equiv }.

Configure Lift A B {
    constrs_a = depConstrAOne depConstrATwo ;
    constrs_b = depConstrBOne depConstrBTwo ;
    elim_a = depRecA ;
    elim_b = depRecB ;
    eta_a = etaA ;
    eta_b = etaB ;
    iota_a = iotaRecAOne iotaRecATwo ;
    iota_b = iotaRecBOne iotaRecBTwo
  }.

Definition test_reflexivityA (a : A) := reflexivity a.

Set Printing All.
Print test_reflexivityA.

Lift A B in test_reflexivityA as test_reflexivityB.

Print test_reflexivityB.

Definition test_reflexivityA2 := reflexivity.

Print test_reflexivityA2.

Lift A B in test_reflexivityA2 as test_reflexivityB2.

Print test_reflexivityB2.

Definition test_equiv_relA := eqA.

Lift A B in test_equiv_relA as test_equiv_relB.

Print test_equiv_relB.

Definition test_equiv_relA2 (a : A) (n : nat) := eqA a.

Print test_equiv_relA2.

Lift A B in test_equiv_relA2 as test_equiv_relB2.

Print test_equiv_relB2.

Definition test_equiv_relA3 (a a2 : A) (n : nat) := eqA a a2.

Print test_equiv_relA3.

Lift A B in test_equiv_relA3 as test_equiv_relB3.

Print test_equiv_relB3.

Definition test_equiv_relA4 := eqA depConstrAOne depConstrATwo.

Print test_equiv_relA4.

Lift A B in test_equiv_relA4 as test_equiv_relB4.

Print test_equiv_relB4.
