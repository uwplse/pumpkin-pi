Require Import List Relation_Definitions Morphisms Setoid.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.

Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.
Set DEVOID lift type.

Module Source.
  Inductive unit :=
  | tt.

  Definition eq_test := eq tt tt.

  Definition eq_test2 := eq (1, tt) (1, tt).

  Definition eq_refl_test : eq tt tt := eq_refl.

  Definition eq_refl_test2 : eq (1, tt) (1, tt) := eq_refl.

  Theorem eq_rect_test : forall (x : unit), eq x tt -> eq x tt.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Theorem eq_rect_test2 : forall (x : unit), eq (1, x) (1, tt) -> eq (1, x) (1, tt).
  Proof.
    intros.
    rewrite H.   
    reflexivity.
  Qed.
  
End Source.

Module Target.
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
  
End Target.

Definition SourceUnit := Source.unit.

Definition depConstrSource := Source.tt.
Definition depConstrTarget := Target.one.

Definition depRecSource (C : Type) := Source.unit_rect (fun _ => C).

Definition depRecTarget (C : Type)
    (out : C)
    (u : Target.unit) :
    C :=
  out.

Definition iotaRecSourceEq (C : Type)
    (out : C)
    (u : Source.unit) :
  depRecSource C out u = out.
Proof.
  destruct u.
  reflexivity.
Qed.

Definition iotaRecSource (C : Type)
  (out : C)
  (u : Source.unit) :
  forall (Q : C -> Type),
    (Q (depRecSource C out u)) -> Q out.
Proof.
  intros.
  rewrite <- (iotaRecSourceEq C out u).
  apply X.
Qed.

Definition iotaRecSourceRev (C : Type)
  (out : C)
  (u : Source.unit) :
  forall (Q : C -> Type),
    Q out -> (Q (depRecSource C out u)).
Proof.
  intros.
  rewrite -> (iotaRecSourceEq C out u).
  apply X.
Qed.

Definition iotaRecTargetEq (C : Type)
    (out : C)
    (u : Target.unit) :
  depRecTarget C out u = out.
Proof.
  destruct u; reflexivity.
Qed.

Definition iotaRecTarget (C : Type)
  (out : C)
  (u : Target.unit) :
  forall (Q : C -> Type),
    (Q (depRecTarget C out u)) -> Q out.
Proof.
  intros.
  rewrite <- (iotaRecTargetEq C out u).
  apply X.
Qed.

Definition iotaRecTargetRev (C : Type)
  (out : C)
  (u : Target.unit) :
  forall (Q : C -> Type),
    Q out -> (Q (depRecTarget C out u)).
Proof.
  intros.
  rewrite -> (iotaRecTargetEq C out u).
  apply X.
Qed.

Definition p (x : Source.unit) := Target.one.

Definition f (x : Target.unit) := Source.tt.

(* this line does something bad in Proof General. *)
Save setoid Source.unit Target.unit { promote = p ; forget = f }.
