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

  Definition eq_test3 := eq tt tt \/ (True /\ eq tt tt).
  Definition eq_refl_test : eq tt tt := @eq_refl unit tt.

  Definition eq_refl_test2 : eq (1, tt) (1, tt) := eq_refl.

  Theorem eq_rect_test : forall (x : unit), eq x tt -> eq x tt.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Print eq_rect_test.

  Theorem eq_rect_test2 : forall (x : unit), eq (1, x) (1, tt) -> eq (1, x) (1, tt).
  Proof.
    intros.
    rewrite H.   
    reflexivity.
  Qed.

  Definition f (x : unit) := 1.

  Theorem eq_rect_test3 : forall (x y : unit), x = y -> x = y \/ x = y.
  Proof.
    intros.
    apply (@eq_rect _ x (fun z => x = z \/ x = y)).
    left.
    reflexivity.
    apply H.
  Qed.    

  Theorem proper_test : forall (x y : unit), x = y -> f x = f y.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.    
  
End Source.

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

  Definition nat_unit_prod := prod nat unit.

  Definition eq_nat_unit_prod : nat * unit -> nat * unit -> Prop :=
    eq_prod (@eq nat) eq_unit.

  About eq_equivalence.

  Instance eq_nat_unit_prod_equiv : Equivalence eq_nat_unit_prod.
  Proof.
    apply eq_prod_equiv.
    apply eq_equivalence.
    apply eq_unit_equiv.
  Qed.   
  
End Target.

Preprocess Module Source as Source_p.

Definition old := Source_p.unit.

Preprocess Module Target as Target_p.

Definition new := Target_p.unit.

Instance eq_unit_equiv : Equivalence Target_p.eq_unit.
Proof.
  apply Target_p.eq_unit_equiv.
Qed.

Instance eq_nat_unit_prod_equiv : Equivalence Target_p.eq_nat_unit_prod.
Proof.
  apply Target_p.eq_nat_unit_prod_equiv.
Qed.

Theorem testing (x : Target_p.unit) (H : Target_p.eq_unit x Target_p.one) :
  (forall (_ : (Target_p.eq_unit Target_p.one Target_p.one)),
  ((fun x : Target_p.unit => Target_p.eq_unit x Target_p.one) x)).
Proof.
  intros.
  simpl.
  rewrite H.
  assumption.
Qed.

Theorem testing2 (x : Target_p.unit) (H : Target_p.eq_nat_unit_prod (1, x) (1, Target_p.one)) : ((fun p : nat * Target_p.unit =>
  Target_p.eq_nat_unit_prod p (1, Target_p.one)) (1, Target_p.one) ->
 (fun p : nat * Target_p.unit =>
  Target_p.eq_nat_unit_prod p (1, Target_p.one)) (1, x)).
Proof.
  intros.
  cbn beta delta.
  rewrite H.
  assumption.
Qed.

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

Compute (@Equivalence_Reflexive new Target_p.eq_unit Target_p.eq_unit_equiv).

Theorem test : forall (x : new), Target_p.eq_unit x x.
Proof.
  apply (@Equivalence_Reflexive new Target_p.eq_unit Target_p.eq_unit_equiv).
Defined.

Print test.
                            
(* this line does something bad in Proof General. *)
Save setoid old new { promote = p ; forget = f ; types = Target_p.unit Target_p.nat_unit_prod ; rels = Target_p.eq_unit Target_p.eq_nat_unit_prod ; equiv_proofs = Target_p.eq_unit_equiv Target_p.eq_nat_unit_prod_equiv }.

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

Lift old new in Source_p.eq_refl_test as eq_refl_test.

Print eq_refl_test.

Lift old new in Source_p.eq_test2 as eq_test2.

Print eq_test2.

Lift old new in Source_p.eq_refl_test2 as eq_refl_test2.

Print eq_refl_test2.

Lift old new in Source_p.eq_test3 as eq_test3.

Print eq_test3.

Lift old new in Source_p.f as func.

Print func.

Instance func_proper : Proper (Target_p.eq_unit ==> eq) func.
Proof.
  intros x y H.
  destruct x;
  destruct y;
  reflexivity.
Qed.

Lift old new in Source_p.eq_rect_test as eq_rect_test.

Print eq_rect_test.

Lift old new in Source_p.eq_rect_test2 as eq_rect_test2.

Print eq_rect_test2.

Print Source_p.eq_rect_test3.

Lift old new in Source_p.eq_rect_test3 as eq_rect_test3.

Print eq_rect_test3.

Lift old new in Source_p.proper_test as proper_test.

Print proper_test.


