Require Import List Relation_Definitions Morphisms Setoid.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.

Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.
Set DEVOID lift type.

(*
 * This file defines an extremely simple setoid equivalence.
 * The source type has two elements which are equivalent 
 * under our equivalence relation, and the target type has
 * one element. The terms that are repaired test the rules we
 * use to repair terms across setoid equivalences.
 *
 * This is the inverse direction of ToSetoidTest.v.
 *)

Definition eq_prod {A B : Type} (eqA : A -> A -> Prop) (eqB : B -> B -> Prop) (p1 p2 : A * B) : Prop :=
  match p1, p2 with
  | (a1 , b1) , (a2 , b2) => (eqA a1 a2) /\ (eqB b1 b2)
  end.

Theorem eq_prod_refl {A B : Type} (eqA : A -> A -> Prop) `(Reflexive _ eqA) (eqB : B -> B -> Prop) `(Reflexive _ eqB) : Reflexive (eq_prod eqA eqB).
Proof.
  intros q. unfold eq_prod. destruct q.
  split; reflexivity.
Qed.

Theorem eq_prod_sym {A B : Type} (eqA : A -> A -> Prop) `(Symmetric _ eqA) (eqB : B -> B -> Prop) `(Symmetric _ eqB) : Symmetric (eq_prod eqA eqB).
Proof.
  intros q1 q2 H1. unfold eq_prod.
  destruct q1.
  destruct q2.
  destruct H1.
  split; symmetry; auto.
Qed.

Theorem eq_prod_trans {A B : Type} (eqA : A -> A -> Prop) `(Transitive _ eqA) (eqB : B -> B -> Prop) `(Transitive _ eqB) : Transitive (eq_prod eqA eqB).
Proof.
  intros q1 q2 q3 H1 H2. unfold eq_prod.
  destruct q1.
  destruct q2.
  destruct q3.
  destruct H1.
  destruct H2.
  split.
  - apply (H a a0 a1); auto.
  - apply (H0 b b0 b1); auto.
Qed.

Theorem eq_prod_equiv {A B : Type} (eqA : A -> A -> Prop) `(Equivalence _ eqA) (eqB : B -> B -> Prop) `(Equivalence _ eqB) : Equivalence (eq_prod eqA eqB).
Proof.
  destruct H. destruct H0. split.
  - apply eq_prod_refl; auto.
  - apply eq_prod_sym; auto.
  - apply eq_prod_trans; auto.
Qed.

Module Source.
  Inductive unit :=
  | one
  | two.

  Definition eq_unit (u1 u2 : unit) : Prop := True.

  Instance eq_unit_refl : Reflexive eq_unit.
  Proof.
    intros z.
    destruct z; reflexivity.
  Qed.

  Instance eq_unit_sym : Symmetric eq_unit.
  Proof.
    intros z1 z2 H.
    apply I.
  Qed.

  Instance eq_unit_trans : Transitive eq_unit.
  Proof.
    intros z1 z2 z3 H1 H2.
    apply I.
  Qed.

  Instance eq_unit_equiv : Equivalence eq_unit.
  Proof.
    split.
    - apply eq_unit_refl.
    - apply eq_unit_sym.
    - apply eq_unit_trans.
  Qed.

  Definition nat_unit_prod := prod nat unit.

  Definition eq_nat_unit_prod : nat * unit -> nat * unit -> Prop :=
    eq_prod (@eq nat) eq_unit.

  Instance eq_nat_unit_prod_equiv : Equivalence eq_nat_unit_prod.
  Proof.
    apply eq_prod_equiv.
    apply eq_equivalence.
    apply eq_unit_equiv.
  Qed.

  Definition depConstr := one.

  Definition depRec (C : Type)
    (out : C)
    (u : unit) :
    C :=
  out.

  Definition iotaRecEq (C : Type)
    (out : C)
    (u : unit) :
    depRec C out u = out.
  Proof.
    destruct u; reflexivity.
  Qed.

  Definition iotaRec (C : Type)
    (out : C)
    (u : unit) :
    forall (Q : C -> Type),
      (Q (depRec C out u)) -> Q out.
  Proof.
    intros.
    rewrite <- (iotaRecEq C out u).
    apply X.
  Qed.

  Definition iotaRecRev (C : Type)
    (out : C)
    (u : unit) :
    forall (Q : C -> Type),
      Q out -> (Q (depRec C out u)).
  Proof.
    intros.
    rewrite -> (iotaRecEq C out u).
    apply X.
  Qed.

  Definition eq_test := eq_unit depConstr depConstr.

  Definition eq_test2 := eq_nat_unit_prod (1, depConstr) (1, depConstr).

  Definition eq_test3 := eq_unit depConstr depConstr \/ (True /\ eq_unit depConstr depConstr).
  
  Theorem eq_refl_test : eq_unit depConstr depConstr.
  Proof.
    reflexivity.
  Qed.

  Theorem eq_refl_test2 : eq_nat_unit_prod (1, depConstr) (1, depConstr).
  Proof.
    reflexivity.
  Qed.

  Theorem eq_rect_test : forall (x : unit), eq_unit x depConstr -> eq_unit x depConstr.
  Proof.
    intros.
    rewrite_annotate H.
    reflexivity.
  Qed.

  Theorem eq_rect_test2 : forall (x : unit),
      eq_nat_unit_prod (1, x) (1, depConstr) -> eq_nat_unit_prod (1, x) (1, depConstr).
  Proof.
    intros.
    rewrite_annotate H.   
    reflexivity.
  Qed.

  Definition f (x : unit) := 1.

  Theorem eq_rect_test3 : forall (x y : unit), eq_unit x y -> eq_unit x y \/ eq_unit x y.
  Proof.
    intros.
    rewrite_annotate H.
    left.
    reflexivity.
  Qed.    

  Theorem proper_test : forall (x y : unit), eq_unit x y -> f x = f y.
  Proof.
    intros.
    rewrite_annotate H.
    reflexivity.
  Qed.  
  
End Source.

Module Target.
  Inductive unit :=
  | tt.

  Definition depConstr := tt.

  Definition depRec (C : Type) := unit_rect (fun _ => C).

  Definition iotaRecEq (C : Type)
    (out : C)
    (u : unit) :
  depRec C out u = out.
  Proof.
    destruct u.
    reflexivity.
  Qed.

  Definition iotaRec (C : Type)
    (out : C)
    (u : unit) :
    forall (Q : C -> Type),
      (Q (depRec C out u)) -> Q out.
  Proof.
    intros.
    rewrite <- (iotaRecEq C out u).
    apply X.
  Qed.

  Definition iotaRecRev (C : Type)
    (out : C)
    (u : unit) :
    forall (Q : C -> Type),
      Q out -> (Q (depRec C out u)).
  Proof.
    intros.
    rewrite -> (iotaRecEq C out u).
    apply X.
  Qed.
End Target.

Definition old := Source.unit.

Definition new := Target.unit.

Instance eq_unit_equiv : Equivalence Source.eq_unit.
Proof.
  apply Source.eq_unit_equiv.
Qed.

Instance eq_nat_unit_prod_equiv : Equivalence Source.eq_nat_unit_prod.
Proof.
  apply Source.eq_nat_unit_prod_equiv.
Qed.

Definition etaSource (x : old) := x.

Definition etaTarget (x : new) := x.

Definition p (x : old) := Source.one.

Definition f (x : new) := Target.tt.
                            
Save setoid old new { promote = p ; forget = f ; types_a = Source.unit Source.nat_unit_prod ; rels_a = Source.eq_unit Source.eq_nat_unit_prod ; equiv_proofs_a = Source.eq_unit_equiv Source.eq_nat_unit_prod_equiv ; types_b = ; rels_b = ; equiv_proofs_b = }.

Configure Lift old new {
    constrs_a = Source.depConstr ;
    constrs_b = Target.depConstr ;
    elim_a = Source.depRec ;
    elim_b = Target.depRec ;
    eta_a = etaSource ;
    eta_b = etaTarget ;
    iota_a = Source.iotaRec ;
    iota_b = Target.iotaRec
  }.

Lift old new in Source.eq_test as eq_test.

Print eq_test.

Lift old new in Source.eq_refl_test as eq_refl_test.

Print eq_refl_test.

Lift old new in Source.eq_test2 as eq_test2.

Print eq_test2.

Lift old new in Source.eq_refl_test2 as eq_refl_test2.

Print eq_refl_test2.

Lift old new in Source.eq_test3 as eq_test3.

Print eq_test3.

Lift old new in Source.f as func.

Print func.

Lift old new in Source.eq_rect_test as eq_rect_test.

Print eq_rect_test.

Lift old new in Source.eq_rect_test2 as eq_rect_test2.

Print eq_rect_test2.

Lift old new in Source.eq_rect_test3 as eq_rect_test3.

Print eq_rect_test3.

Lift old new in Source.proper_test as proper_test.

Print proper_test.
