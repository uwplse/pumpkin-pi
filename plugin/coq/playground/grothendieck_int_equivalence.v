Require Import Relation_Definitions Morphisms Lia Eqdep_dec EqdepFacts.

Module IndInt.

Inductive Z : Set :=
| pos : nat -> Z
| negsuc : nat -> Z.

Definition depConstrPos (n : nat) : Z := pos n.
Definition depConstrNegSuc (n : nat) : Z := negsuc n.

Definition depElim (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (z : Z) :
  P z :=
  match z with
  | pos n => posP n
  | negsuc n => negSucP n
  end.

Theorem iotaPosEq (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat)
  (Q : P (depConstrPos n) -> Type) :
  Q (depElim P posP negSucP (depConstrPos n)) = Q (posP n).
Proof.
  reflexivity.
Qed.

Theorem iotaPos (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrPos n) -> Type),
  (Q (depElim P posP negSucP (depConstrPos n))) -> Q (posP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaPosRev (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrPos n) -> Type),
  Q (posP n) -> (Q (depElim P posP negSucP (depConstrPos n))).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaNegSucEq (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat)
  (Q : P (depConstrNegSuc n) -> Type) :
  Q (depElim P posP negSucP (depConstrNegSuc n)) = Q (negSucP n).
Proof.
  reflexivity.
Qed.

Theorem iotaNegSuc (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrNegSuc n) -> Type),
  (Q (depElim P posP negSucP (depConstrNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaNegSucRev (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrNegSuc n) -> Type),
  Q (negSucP n) -> (Q (depElim P posP negSucP (depConstrNegSuc n))).
Proof.
  intros.
  apply X.
Qed.

Print nat_rec.

Definition constZ {A : Type} (a : A) := Z.

Definition sucZ (z : Z) : Z :=
  depElim
    constZ
    (fun (n : nat) => depConstrPos (S n))
    (fun (n : nat) => nat_rec constZ (depConstrPos 0) (fun (m : nat) _ => depConstrNegSuc m) n)
    z.

Definition predZ (z : Z) : Z :=
  depElim
    constZ
    (fun (n : nat) => nat_rec constZ (depConstrNegSuc 0) (fun (m : nat) _ => depConstrPos m) n)
    (fun (n : nat) => depConstrNegSuc (S n))
    z.

Definition add_posZ (z : Z) (n : nat) : Z :=
  nat_rec constZ z (fun _ (p : Z) => sucZ p) n.

Definition add_negsucZ (z : Z) (n : nat) : Z :=
  nat_rec constZ (predZ z) (fun _ (p : Z) => predZ p) n.

Definition addZ (z1 z2 : Z) : Z :=
  depElim
    constZ
    (fun (p : nat) => add_posZ z1 p)
    (fun (p : nat) => add_negsucZ z1 p)
    z2.


Theorem add0LZ (z : Z) : z = addZ (depConstrPos 0) z.
Proof.
  eapply (depElim (fun (z1 : Z) => z1 = addZ (depConstrPos 0) z1)).
  - induction n.
    + reflexivity.
    + apply (iotaPos
                constZ
                (fun q => depConstrPos (S q))
                (fun q => nat_rec constZ (depConstrPos 0) (fun m _ => depConstrNegSuc m) q)
                n
                (fun s => s = addZ (depConstrPos 0) (depConstrPos (S n)))).
      apply (iotaPosRev
               constZ
               (fun q => add_posZ (depConstrPos 0) q)
               (fun q => add_negsucZ (depConstrPos 0) q)
               (S n)
               (fun s => depElim
                           constZ
                           (fun m => depConstrPos (S m))
                           (fun m => nat_rec
                                       constZ
                                       (depConstrPos 0)
                                       (fun p _ => depConstrNegSuc p)
                                       m)
                           (depConstrPos n) = s)).
      apply (iotaPos
               constZ
               (fun q => add_posZ (depConstrPos 0) q)
               (fun q => add_negsucZ (depConstrPos 0) q)
               n
               (fun s => depElim
                           constZ
                           (fun m => depConstrPos (S m))
                           (fun m => nat_rec
                                       constZ
                                       (depConstrPos 0)
                                       (fun p _ => depConstrNegSuc p)
                                       m)
                           (depConstrPos n) = sucZ s)).
      apply (f_equal sucZ).
      apply IHn.
  - induction n.
    + reflexivity.
    + apply (iotaNegSuc
                constZ
                (fun q => nat_rec constZ (depConstrNegSuc 0) (fun m _ => depConstrPos m) q)
                (fun q => depConstrNegSuc (S q))
                n
                (fun s => s = addZ (depConstrPos 0) (depConstrNegSuc (S n)))).
      apply (iotaNegSucRev
               constZ
               (fun q => add_posZ (depConstrPos 0) q)
               (fun q => add_negsucZ (depConstrPos 0) q)
               (S n)
               (fun s => depElim
                           constZ
                           (fun m => nat_rec
                                       constZ
                                       (depConstrNegSuc 0)
                                       (fun p _ => depConstrPos p)
                                       m)
                           (fun m => depConstrNegSuc (S m))
                           (depConstrNegSuc n) = s)).
      apply (iotaNegSuc
               constZ
               (fun q => add_posZ (depConstrPos 0) q)
               (fun q => add_negsucZ (depConstrPos 0) q)
               n
               (fun s => depElim
                           constZ
                           (fun m => nat_rec
                                       constZ
                                       (depConstrNegSuc 0)
                                       (fun p _ => depConstrPos p)
                                       m)
                           (fun m => depConstrNegSuc (S m))
                           (depConstrNegSuc n) = predZ s)).
      apply (f_equal predZ).
      apply IHn.
Qed.
       
End IndInt.

Module GInt.

  Definition Z := (prod nat nat).
  Definition eq_Z (z1 z2 : Z) : Prop :=
    match z1, z2 with
    | (a1, a2), (b1, b2) => a1 + b2 = a2 + b1
    end.

  Instance eq_Z_refl : Reflexive eq_Z.
  Proof.
    intros z.
    destruct z.
    unfold eq_Z.
    lia.
  Qed.

  Instance eq_Z_sym : Symmetric eq_Z.
  Proof.
    unfold eq_Z.
    intros z1 z2 H.
    destruct z1.
    destruct z2.
    lia.
  Qed.

  Instance eq_Z_trans : Transitive eq_Z.
  Proof.
    unfold eq_Z.
    intros z1 z2 z3 H1 H2.
    destruct z1.
    destruct z2.
    destruct z3.
    lia.
  Qed.

  Instance eq_Z_equiv : Equivalence eq_Z.
  Proof.
    split.
    - apply eq_Z_refl.
    - apply eq_Z_sym.
    - apply eq_Z_trans.
  Qed.

  Theorem eq_Z_suc : forall (n1 n2 : nat),
      eq_Z (n1, n2) (S n1, S n2).
  Proof.
    intros.
    unfold eq_Z.
    lia.
  Qed.

  Theorem eq_Z_suc_redl : forall (z : Z) (n1 n2 : nat),
      eq_Z (S n1, S n2) z -> eq_Z (n1, n2) z.
  Proof.
    unfold eq_Z.
    intros.
    destruct z.
    lia.
  Qed.

  Theorem eq_Z_suc_redr : forall (z : Z) (n1 n2 : nat),
      eq_Z z (S n1, S n2) -> eq_Z z (n1, n2).
  Proof.
    unfold eq_Z.
    intros.
    destruct z.
    lia.
  Qed.

  Definition depConstrPos (n : nat) : Z := (n, 0).
  Definition depConstrNegSuc (n : nat) : Z := (0, S n).

  Fixpoint canonicalize' (n1 n2 : nat) :=
    match n1, n2 with
    | 0, 0 => (0, 0)
    | S n, 0 => (S n, 0)
    | 0, S m => (0, S m)
    | S n, S m => canonicalize' n m
    end.

  Definition canonicalize (z : Z) :=
    match z with
    | (a1, a2) => canonicalize' a1 a2
    end.
  Print sumbool.

  Theorem canonicalize'Respectful : forall (n1 n2 n3 n4 : nat),
      eq_Z (n1, n2) (n3, n4) -> canonicalize' n1 n2 = canonicalize' n3 n4.
  Proof.
    induction n1; induction n2; induction n3; induction n4; try (unfold eq_Z; lia); intros.
    - reflexivity.
    - simpl.
      rewrite <- IHn3.
      reflexivity.
      apply eq_Z_suc_redr.
      apply H.
    - unfold eq_Z in H.
      assert (n2 = n4).
      lia.
      rewrite H0.
      reflexivity.
    - apply IHn3.
      apply eq_Z_suc_redr.
      apply H.
    - assert (n1 = n3).
      unfold eq_Z in H.
      lia.
      rewrite H0.
      reflexivity.
    - rewrite (IHn3 n4).
      reflexivity.
      apply eq_Z_suc_redr.
      apply H.
    - apply IHn1.
      apply eq_Z_suc_redl.
      apply H.
    - simpl.
      apply (IHn1 n2 0 (S n4)).
      apply eq_Z_suc_redl.
      apply H.
    - simpl.
      apply (IHn1 n2 (S n3) 0).
      apply eq_Z_suc_redl.
      apply H.
    - simpl.
      apply IHn1.
      apply eq_Z_suc_redl.
      apply eq_Z_suc_redr.
      apply H.
  Defined.
      
  Instance canonicalizeProper : Proper (eq_Z ==> eq) canonicalize.
  Proof.
    intros z1 z2 H.
    destruct z1.
    destruct z2.
    unfold canonicalize.
    apply canonicalize'Respectful.
    apply H.
  Defined.

  Theorem canonicalize'SignDec : forall (n1 n2 : nat),
      { n : nat | (canonicalize' n1 n2 = (n, 0))} +
      { n : nat | (canonicalize' n1 n2 = (0, S n))}.
  Proof.
    induction n1; destruct n2.
    - left. exists 0. reflexivity.
    - right. exists n2. reflexivity.
    - left. exists (S n1). reflexivity.
    - specialize (IHn1 n2). simpl. apply IHn1.
  Defined.    

  Theorem canonicalizeSignDec : forall (z : Z),
      { n : nat | (canonicalize z = (n, 0))} +
      { n : nat | (canonicalize z = (0, S n))}.
  Proof.
    intros.
    destruct z.
    unfold canonicalize.
    apply canonicalize'SignDec.
  Defined.

  Theorem canonicalizePos : forall (n : nat),
      canonicalize (depConstrPos n) = depConstrPos n.
  Proof.
    intros.
    destruct n; reflexivity.
  Defined.

  Theorem canonicalizeSignDecPos : forall (n : nat),
      canonicalizeSignDec (depConstrPos n) =
      inl (exist (fun (x : nat) => canonicalize (depConstrPos n) = (x, 0)) n (canonicalizePos n)).
  Proof.
    intros.
    destruct n; reflexivity.
  Qed.

  Theorem canonicalizeNegSuc : forall (n : nat),
      canonicalize (depConstrNegSuc n) = depConstrNegSuc n.
  Proof.
    intros.
    destruct n; reflexivity.
  Defined.

  Theorem canonicalizeSignDecNegSuc : forall (n : nat),
      canonicalizeSignDec (depConstrNegSuc n) =
      inr (exist (fun (x : nat) => canonicalize (depConstrNegSuc n) = (0, S x)) n (canonicalizeNegSuc n)).
  Proof.
    intros.
    destruct n; reflexivity.
  Qed.

  Theorem canonicalize'Pres : forall (n1 n2 : nat),
      eq_Z (canonicalize (n1, n2)) (n1, n2).
  Proof.
    intros n1.
    induction n1; induction n2; try reflexivity.
    simpl.
    rewrite <- eq_Z_suc.
    apply IHn1.
  Defined.
  
  Theorem canonicalizePres : forall (z : Z),
      eq_Z (canonicalize z) z.
  Proof.
    intros.
    destruct z.
    apply canonicalize'Pres.
  Defined.

  Definition depRec (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (z : Z) :
    C :=
    match (canonicalizeSignDec z) with
    | inl s => posP (proj1_sig s)
    | inr s => negSucP (proj1_sig s)
    end.

  Definition iotaRecPosEq (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (n : nat) :
    forall (Q : C -> Type),
      (Q (depRec C posP negSucP (depConstrPos n))) = Q (posP n).
  Proof.
    intros.
    unfold depRec.
    rewrite canonicalizeSignDecPos.
    reflexivity.
  Qed.

  Definition iotaRecPos (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (n : nat) :
    forall (Q : C -> Type),
      (Q (depRec C posP negSucP (depConstrPos n))) -> Q (posP n).
  Proof.
    intros.
    rewrite <- (iotaRecPosEq C posP negSucP).
    apply X.
  Qed.

  Definition iotaRecPosRev (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (n : nat) :
    forall (Q : C -> Type),
      Q (posP n) -> (Q (depRec C posP negSucP (depConstrPos n))).
  Proof.
    intros.
    rewrite (iotaRecPosEq C posP negSucP).
    apply X.
  Qed.

  Definition iotaRecNegSucEq (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (n : nat) :
    forall (Q : C -> Type),
      (Q (depRec C posP negSucP (depConstrNegSuc n))) = Q (negSucP n).
  Proof.
    intros.
    unfold depRec.
    rewrite canonicalizeSignDecNegSuc.
    reflexivity.
  Qed.

  Definition iotaRecNegSuc (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (n : nat) :
    forall (Q : C -> Type),
      (Q (depRec C posP negSucP (depConstrNegSuc n))) -> Q (negSucP n).
  Proof.
    intros.
    rewrite <- (iotaRecNegSucEq C posP negSucP).
    apply X.
  Qed.

  Definition iotaRecNegSucRev (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (n : nat) :
    forall (Q : C -> Type),
      Q (negSucP n) -> (Q (depRec C posP negSucP (depConstrNegSuc n))).
  Proof.
    intros.
    rewrite (iotaRecNegSucEq C posP negSucP).
    apply X.
  Qed.

  Definition ZExtEqual (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) (f1 f2 : Z -> C) : Prop :=
    Proper (eq_Z ==> eq_C) f1 /\ Proper (eq_Z ==> eq_C) f2 /\
    forall (z1 z2 : Z), eq_Z z1 z2 -> eq_C (f1 z1) (f2 z2).

  (*Instance ZExtEqualRefl (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : Reflexive (ZExtEqual C eq_C eq_C_equiv).
  Proof.
    intros f fProper _ z1 z2 H.
    rewrite H.
    reflexivity.
  Qed.*)

  Instance ZExtEqualSym (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : Symmetric (ZExtEqual C eq_C eq_C_equiv).
  Proof.
    intros f1 f2 H.
    destruct H.
    destruct H0.
    split.
    apply H0.
    split.
    apply H.
    intros.
    symmetry.
    apply H1.
    symmetry.
    apply H2.
  Qed.

  Instance ZExtEqualTrans (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : Transitive (ZExtEqual C eq_C eq_C_equiv).
  Proof.
    intros f1 f2 f3 H1 H2.
    destruct H1.
    destruct H0.
    destruct H2.
    destruct H3.
    split.
    apply H.
    split.
    apply H3.
    intros.
    transitivity (f2 z1).
    apply H1; auto. reflexivity.
    apply H4; auto.
  Qed.

  Definition natExtEqual (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) (f1 f2 : nat -> C) : Prop :=
    Proper (eq ==> eq_C) f1 /\ Proper (eq ==> eq_C) f2 /\
    forall (n1 n2 : nat), n1 = n2 -> eq_C (f1 n1) (f2 n2).

  (*Instance ZExtEqualRefl (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : Reflexive (ZExtEqual C eq_C eq_C_equiv).
  Proof.
    intros f fProper _ z1 z2 H.
    rewrite H.
    reflexivity.
  Qed.*)

  Instance natExtEqualSym (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : Symmetric (natExtEqual C eq_C eq_C_equiv).
  Proof.
    intros f1 f2 H.
    destruct H.
    destruct H0.
    split.
    apply H0.
    split.
    apply H.
    intros.
    symmetry.
    apply H1.
    symmetry.
    apply H2.
  Qed.

  Instance natExtEqualTrans (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : Transitive (natExtEqual C eq_C eq_C_equiv).
  Proof.
    intros f1 f2 f3 H1 H2.
    destruct H1.
    destruct H0.
    destruct H2.
    destruct H3.
    split.
    apply H.
    split.
    apply H3.
    intros.
    transitivity (f2 n1).
    apply H1; auto.
    apply H4; auto.
  Qed.

  Instance natExtEqualPER (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) : PER (natExtEqual C eq_C eq_C_equiv).
  Proof.
    split.
    apply natExtEqualSym.
    apply natExtEqualTrans.
  Qed.

  Theorem depRecCanonical (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C)
    (z : Z) :
    depRec C posP negSucP z = depRec C posP negSucP (canonicalize z).
  Proof.
    unfold depRec.
    destruct z.
    generalize dependent n0.
    induction n; induction n0.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply IHn.
  Qed.    

  Instance depRecProper (C : Type)
    (posP : forall (n : nat), C)
    (negSucP : forall (n : nat), C) :
    Proper (eq_Z ==> eq) (depRec C posP negSucP).
  Proof.
    intros z1 z2 H.
    rewrite depRecCanonical.
    rewrite (depRecCanonical _ _ _ z2).
    rewrite H.
    reflexivity.
  Qed.

  Instance depRecProperMore (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) :
    Proper ((natExtEqual C eq_C eq_C_equiv) ==> (natExtEqual C eq_C eq_C_equiv) ==> eq_Z ==> eq_C) (depRec C).
  Proof.
    intros f1 f2 H1 f3 f4 H2 n1 n2 H3.
    rewrite depRecCanonical.
    rewrite (depRecCanonical _ _ _ n2).
    rewrite H3.
    unfold depRec.
    destruct (canonicalizeSignDec (canonicalize n2)).
    - destruct H1.
      destruct H0.
      apply H1.
      reflexivity.
    - destruct H2.
      destruct H0.
      apply H2.
      reflexivity.
  Qed.

  Instance depRecProperEqZ
    (posP : forall (n : nat), Z)
    (negSucP : forall (n : nat), Z) :
    Proper (eq_Z ==> eq_Z) (depRec Z posP negSucP).
  Proof.
    intros z1 z2 H.
    rewrite H.
    reflexivity.
  Qed.

  Theorem depElimProp (P : Z -> Prop)
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (z : Z) :
    P z.
  Proof.
    destruct (canonicalizeSignDec z).
    - destruct s.
      rewrite <- canonicalizePres.
      rewrite e.
      apply posP.
    - destruct s.
      rewrite <- canonicalizePres.
      rewrite e.
      apply negSucP.
  Defined.

  Print depElimProp.

  Definition isHProp (P : Type) : Prop :=
    forall p q : P, p = q.

  (* the HProp assumption is actually stronger than necessary;
     all we need is that rewriting via p is the identity *)
  
  Theorem transparency_axiom (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    (eq_Z : Z -> Z -> Prop)
    `(e : Equivalence Z eq_Z)
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (n : nat)
    (equ : eq_Z (depConstrPos n) (n, 0)):
    (subrelation_proper p tt
       (subrelation_respectful (subrelation_refl eq_Z) iff_flip_impl_subrelation)
       (depConstrPos n) (n, 0) (equ) 
       (posP n)) = (posP n).
  Proof.
    
  Admitted.

  Definition iotaPropPosEq (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (n : nat) :
      depElimProp P p posP negSucP (depConstrPos n) = posP n.
  Proof.
    apply prop.
  Qed.

  (*
    intros.
    unfold depElimProp.
    rewrite canonicalizeSignDecPos.
    unfold eq_ind_r.
    unfold eq_ind.
    unfold canonicalizePos.
    destruct n;
      simpl;
      apply transparency_axiom;
      (repeat (apply prop + apply eq_Z_equiv)).
  Qed.*)

  Definition iotaPropPos (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (n : nat) :
    forall (Q : (P (depConstrPos n)) -> Type),
      (Q (depElimProp P p posP negSucP (depConstrPos n))) -> Q (posP n).
  Proof.
    intros.
    rewrite <- (iotaPropPosEq P prop p posP negSucP).
    apply X.
  Qed.

  Definition iotaPropPosRev (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (n : nat) :
    forall (Q : (P (depConstrPos n)) -> Type),
      Q (posP n) -> (Q (depElimProp P p posP negSucP (depConstrPos n))).
  Proof.
    intros.
    rewrite (iotaPropPosEq P prop p posP negSucP).
    apply X.
  Qed.

  Definition iotaPropNegSucEq (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (n : nat) :
      depElimProp P p posP negSucP (depConstrNegSuc n) = negSucP n.
  Proof.
    apply prop.
  Qed.

  Definition iotaPropNegSuc (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (n : nat) :
    forall (Q : (P (depConstrNegSuc n)) -> Type),
      (Q (depElimProp P p posP negSucP (depConstrNegSuc n))) -> Q (negSucP n).
  Proof.
    intros.
    rewrite <- (iotaPropNegSucEq P prop p posP negSucP).
    apply X.
  Qed.

  Definition iotaPropNegSucRev (P : Z -> Prop)
    (prop : forall z : Z, isHProp (P z))
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (n : nat) :
    forall (Q : (P (depConstrNegSuc n)) -> Type),
      Q (negSucP n) -> (Q (depElimProp P p posP negSucP (depConstrNegSuc n))).
  Proof.
    intros.
    rewrite (iotaPropNegSucEq P prop p posP negSucP).
    apply X.
  Qed.

  (*
  Instance depElimPropProper (P : Z -> Prop)
    `(p : Proper (Z -> Prop) (eq_Z ==> iff) P)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n)) :
    Proper (eq_Z ==> iff) (depRec P p posP negSucP).*)
     
  (* need to use transport to do this correctly.
  Definition depElim (P : Z -> Type)
    (posP : forall (n : nat), P (depConstrPos n))
    (negSucP : forall (n : nat), P (depConstrNegSuc n))
    (z : Z) :
    P z :=
    match (canonicalizeSignDec z) with
    | inl s => posP (proj1_sig s)
    | inr s => negSucP (proj1_sig s)
    end.*)

  
  Definition constZ {A : Type} (a : A) := Z.

  Definition sucZ (z : Z) : Z :=
    depRec
      Z
      (fun (n : nat) => depConstrPos (S n))
      (fun (n : nat) => nat_rec constZ (depConstrPos 0) (fun (m : nat) _ => depConstrNegSuc m) n)
      z.

  Instance sucZProper :
    Proper (eq_Z ==> eq_Z) sucZ.
  Proof.
    intros z1 z2 H.
    unfold sucZ.
    apply depRecProperEqZ.
    apply H.
  Qed.

  Definition predZ (z : Z) : Z :=
    depRec
      Z
      (fun (n : nat) => nat_rec constZ (depConstrNegSuc 0) (fun (m : nat) _ => depConstrPos m) n)
      (fun (n : nat) => depConstrNegSuc (S n))
      z.

  Instance predZProper :
    Proper (eq_Z ==> eq_Z) predZ.
  Proof.
    intros z1 z2 H.
    unfold predZ.
    apply depRecProperEqZ.
    apply H.
  Qed.

  Definition add_posZ (z : Z) (n : nat) : Z :=
    nat_rec constZ z (fun _ (p : Z) => sucZ p) n.

  Instance add_posZProper :
    Proper (eq_Z ==> eq ==> eq_Z) add_posZ.
  Proof.
    intros z1 z2 H1 n1 n2 H2.
    unfold add_posZ.
    subst.
    induction n2.
    - simpl. apply H1.
    - simpl. f_equiv. apply IHn2.
  Qed.    

  Definition add_negsucZ (z : Z) (n : nat) : Z :=
    nat_rec constZ (predZ z) (fun _ (p : Z) => predZ p) n.

  Instance add_negsucZProper :
    Proper (eq_Z ==> eq ==> eq_Z) add_negsucZ.
  Proof.
    intros z1 z2 H1 n1 n2 H2.
    unfold add_negsucZ.
    subst.
    induction n2.
    - simpl. f_equiv. apply H1.
    - simpl. f_equiv. apply IHn2.
  Qed.  

  Definition addZ (z1 z2 : Z) : Z :=
    depRec
      Z
      (fun (p : nat) => add_posZ z1 p)
      (fun (p : nat) => add_negsucZ z1 p)
      z2.

  Instance addZProper :
    Proper (eq_Z ==> eq_Z ==> eq_Z) addZ.
  Proof.
    intros z1 z2 H1 z3 z4 H2.
    unfold addZ.
    apply (depRecProperMore Z eq_Z eq_Z_equiv).
    - split.
      apply add_posZProper.
      reflexivity.
      split.
      apply add_posZProper.
      reflexivity.
      intros.
      rewrite H.
      rewrite H1.
      reflexivity.
    - split.
      apply add_negsucZProper.
      reflexivity.
      split.
      apply add_negsucZProper.
      reflexivity.
      intros.
      rewrite H.
      rewrite H1.
      reflexivity.
    - apply H2.
Qed.    

  Definition eq_dec (A : Type) := forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.

  Theorem eq_dec_prod {A B : Type} :
    eq_dec A -> eq_dec B -> eq_dec (prod A B).
  Proof.
    unfold eq_dec.
    intros.
    destruct a1.
    destruct a2.
    specialize (X a a0).
    specialize (X0 b b0).
    destruct X.
    - destruct X0.
      + left. subst. reflexivity.
      + right. intros H. apply (f_equal snd) in H. simpl in H.
        contradiction.
    - right. intros H. apply (f_equal fst) in H. simpl in H.
      contradiction.
  Qed.
  
  Theorem isSetZ : UIP_ Z.
  Proof.
    intros z1 z2 H1 H2.
    apply UIP_dec.
    unfold Z.
    apply eq_dec_prod; unfold eq_dec; apply PeanoNat.Nat.eq_dec.
  Qed.

  Instance add0LZTypeProper (z : Z) :
      Proper (eq_Z ==> iff) (fun z1 : Z => eq_Z z1 (addZ (depConstrPos 0) z1)).
  Proof.
    intros z1 z2 H.
    transitivity (eq_Z z2 (addZ (depConstrPos 0) z1)).
    - rewrite H.
      reflexivity.
    - rewrite H.
      reflexivity.
  Qed.    

  Theorem add0LZ (z : Z) : eq_Z z (addZ (depConstrPos 0) z).
  Proof.
    eapply (depElimProp (fun (z1 : Z) => eq_Z z1 (addZ (depConstrPos 0) z1))).
    - apply add0LZTypeProper.
      apply z.
    - induction n.
      + reflexivity.
      + apply (iotaRecPos
                  Z
                  (fun q => depConstrPos (S q))
                  (fun q => nat_rec constZ (depConstrPos 0) (fun m _ => depConstrNegSuc m) q)
                  n
                  (fun s => eq_Z s (addZ (depConstrPos 0) (depConstrPos (S n))))).
        apply (iotaRecPosRev
                 Z
                 (fun q => add_posZ (depConstrPos 0) q)
                 (fun q => add_negsucZ (depConstrPos 0) q)
                 (S n)
                 (fun s => eq_Z (depRec
                             Z
                             (fun m => depConstrPos (S m))
                             (fun m => nat_rec
                                         constZ
                                         (depConstrPos 0)
                                         (fun p _ => depConstrNegSuc p)
                                         m)
                             (depConstrPos n)) s)).
        apply (iotaRecPos
                 Z
                 (fun q => add_posZ (depConstrPos 0) q)
                 (fun q => add_negsucZ (depConstrPos 0) q)
                 n
                 (fun s => eq_Z (depRec
                             Z
                             (fun m => depConstrPos (S m))
                             (fun m => nat_rec
                                         constZ
                                         (depConstrPos 0)
                                         (fun p _ => depConstrNegSuc p)
                                         m)
                             (depConstrPos n)) (sucZ s))).
        f_equiv.
        apply IHn.
    - induction n.
      + reflexivity.
      + apply (iotaRecNegSuc
                  Z
                  (fun q => nat_rec constZ (depConstrNegSuc 0) (fun m _ => depConstrPos m) q)
                  (fun q => depConstrNegSuc (S q))
                  n
                  (fun s => eq_Z s (addZ (depConstrPos 0) (depConstrNegSuc (S n))))).
        apply (iotaRecNegSucRev
                 Z
                 (fun q => add_posZ (depConstrPos 0) q)
                 (fun q => add_negsucZ (depConstrPos 0) q)
                 (S n)
                 (fun s => eq_Z (depRec
                             Z
                             (fun m => nat_rec
                                         constZ
                                         (depConstrNegSuc 0)
                                         (fun p _ => depConstrPos p)
                                         m)
                             (fun m => depConstrNegSuc (S m))
                             (depConstrNegSuc n)) s)).
        apply (iotaRecNegSuc
                 Z
                 (fun q => add_posZ (depConstrPos 0) q)
                 (fun q => add_negsucZ (depConstrPos 0) q)
                 n
                 (fun s => eq_Z (depRec
                             Z
                             (fun m => nat_rec
                                         constZ
                                         (depConstrNegSuc 0)
                                         (fun p _ => depConstrPos p)
                                         m)
                             (fun m => depConstrNegSuc (S m))
                             (depConstrNegSuc n)) (predZ s))).
        f_equiv.
        apply IHn.
  Qed.

End GInt.
