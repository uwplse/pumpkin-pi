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

Preprocess Module Source as Source_p.

Definition old := Source_p.unit.

Preprocess Module Target as Target_p.

Definition new := Target_p.unit.

Definition depConstrSource := Source_p.tt.
Definition depConstrTarget := Target_p.one.

Definition depRecSource (C : Type) := Source_p.unit_rect (fun _ => C).

Definition depRecTarget (C : Type)
    (out : C)
    (u : new) :
    C :=
  out.

Definition iotaRecSourceEq (C : Type)
    (out : C)
    (u : old) :
  depRecSource C out u = out.
Proof.
  destruct u.
  reflexivity.
Qed.

Definition iotaRecSource (C : Type)
  (out : C)
  (u : old) :
  forall (Q : C -> Type),
    (Q (depRecSource C out u)) -> Q out.
Proof.
  intros.
  rewrite <- (iotaRecSourceEq C out u).
  apply X.
Qed.

Definition iotaRecSourceRev (C : Type)
  (out : C)
  (u : old) :
  forall (Q : C -> Type),
    Q out -> (Q (depRecSource C out u)).
Proof.
  intros.
  rewrite -> (iotaRecSourceEq C out u).
  apply X.
Qed.

Definition iotaRecTargetEq (C : Type)
    (out : C)
    (u : new) :
  depRecTarget C out u = out.
Proof.
  destruct u; reflexivity.
Qed.

Definition iotaRecTarget (C : Type)
  (out : C)
  (u : new) :
  forall (Q : C -> Type),
    (Q (depRecTarget C out u)) -> Q out.
Proof.
  intros.
  rewrite <- (iotaRecTargetEq C out u).
  apply X.
Qed.

Definition iotaRecTargetRev (C : Type)
  (out : C)
  (u : new) :
  forall (Q : C -> Type),
    Q out -> (Q (depRecTarget C out u)).
Proof.
  intros.
  rewrite -> (iotaRecTargetEq C out u).
  apply X.
Qed.

Definition etaSource (x : old) := x.

Definition etaTarget (x : new) := x.

Definition p (x : old) := Target_p.one.

Definition f (x : new) := Source_p.tt.

(* this line does something bad in Proof General. *)
Save setoid old new { promote = p ; forget = f ; types = Target_p.unit ; rels = Target_p.eq_unit ; equiv_proofs = Target_p.eq_unit_equiv}.

Print tt.

Configure Lift old new {
    constrs_a = depConstrSource ;
    constrs_b = depConstrTarget ;
    elim_a = depRecSource ;
    elim_b = depRecTarget ;
    eta_a = etaSource ;
    eta_b = etaTarget ;
    iota_a = iotaRecSource ;
    iota_b = iotaRecTarget
  }.

Print tt.

Lift old new in Source_p.eq_test as eq_test.

Print eq_test.
