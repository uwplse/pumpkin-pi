Require Import Relation_Definitions Morphisms Setoid Lia.

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

Theorem iotaNeg (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrNegSuc n) -> Type),
  (Q (depElim P posP negSucP (depConstrNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaPosNegSuc (P : Z -> Type)
  (posP : forall (n : nat), P (depConstrPos n))
  (negSucP : forall (n : nat), P (depConstrNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrNegSuc n) -> Type),
  Q (negSucP n) -> (Q (depElim P posP negSucP (depConstrNegSuc n))).
Proof.
  intros.
  apply X.
Qed.
       
End IndInt.

Module GInt.

  Definition Z := (prod nat nat).
  Definition eq_Z (z1 z2 : Z) : Prop :=
    match z1, z2 with
    | (a1, a2), (b1, b2) => a1 + b2 = a2 + b1
    end.

  Theorem eq_Z_refl : Reflexive eq_Z.
  Proof.
    intros z.
    destruct z.
    unfold eq_Z.
    lia.
  Qed.

  Theorem eq_Z_sym : Symmetric eq_Z.
  Proof.
    unfold eq_Z.
    intros z1 z2 H.
    destruct z1.
    destruct z2.
    lia.
  Qed.

  Theorem eq_Z_trans : Transitive eq_Z.
  Proof.
    unfold eq_Z.
    intros z1 z2 z3 H1 H2.
    destruct z1.
    destruct z2.
    destruct z3.
    lia.
  Qed.

  Theorem eq_Z_equiv : Equivalence eq_Z.
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
  Qed.
      
  Instance canonicalizeProper : Proper (eq_Z ==> eq) canonicalize.
  Proof.
    intros z1 z2 H.
    destruct z1.
    destruct z2.
    unfold canonicalize.
    apply canonicalize'Respectful.
    apply H.
  Qed.

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
    

End GInt.
