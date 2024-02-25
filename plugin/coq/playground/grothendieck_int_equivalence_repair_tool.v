Require Import Relation_Definitions Morphisms Lia.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.

Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.

Module IndInt.

Inductive Z : Set :=
| pos : nat -> Z
| negsuc : nat -> Z.
       
End IndInt.

Preprocess Module IndInt as IndInt_p.

Definition depConstrIndIntPos (n : nat) : IndInt_p.Z := IndInt_p.pos n.
Definition depConstrIndIntNegSuc (n : nat) : IndInt_p.Z := IndInt_p.negsuc n.

Definition depRecIndInt (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : IndInt_p.Z) :
  C :=
  match z with
  | IndInt_p.pos n => posP n
  | IndInt_p.negsuc n => negSucP n
  end.

Definition depElimPropIndInt (P : IndInt_p.Z -> Prop)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (z : IndInt_p.Z) :
  P z :=
  match z with
  | IndInt_p.pos n => posP n
  | IndInt_p.negsuc n => negSucP n
  end.

Theorem iotaIndIntPos (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  (Q (depRecIndInt C posP negSucP (depConstrIndIntPos n))) -> Q (posP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaIndIntPosRev (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  Q (posP n) -> (Q (depRecIndInt C posP negSucP (depConstrIndIntPos n))).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaIndIntNegSuc (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  (Q (depRecIndInt C posP negSucP (depConstrIndIntNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaIndIntNegSucRev (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  Q (negSucP n) -> (Q (depRecIndInt C posP negSucP (depConstrIndIntNegSuc n))).
Proof.
  intros.
  apply X.
Qed.

Definition constIndIntZ (A : Type) (a : A) := IndInt_p.Z.

Definition sucIndIntZ (z : IndInt_p.Z) : IndInt_p.Z :=
  depRecIndInt
    IndInt_p.Z
    (fun (n : nat) => depConstrIndIntPos (S n))
    (fun (n : nat) => nat_rec (constIndIntZ _) (depConstrIndIntPos 0) (fun (m : nat) _ => depConstrIndIntNegSuc m) n)
    z.

Definition predIndIntZ (z : IndInt_p.Z) : IndInt_p.Z :=
  depRecIndInt
    IndInt_p.Z
    (fun (n : nat) => nat_rec (constIndIntZ _) (depConstrIndIntNegSuc 0) (fun (m : nat) _ => depConstrIndIntPos m) n)
    (fun (n : nat) => depConstrIndIntNegSuc (S n))
    z.

Definition add_posIndIntZ (z : IndInt_p.Z) (n : nat) : IndInt_p.Z :=
  nat_rec (constIndIntZ _) z (fun _ (p : IndInt_p.Z) => sucIndIntZ p) n.

Definition add_negsucIndIntZ (z : IndInt_p.Z) (n : nat) : IndInt_p.Z :=
  nat_rec (constIndIntZ _) (predIndIntZ z) (fun _ (p : IndInt_p.Z) => predIndIntZ p) n.

Definition addIndIntZ (z1 z2 : IndInt_p.Z) : IndInt_p.Z :=
  depRecIndInt
    IndInt_p.Z
    (fun (p : nat) => add_posIndIntZ z1 p)
    (fun (p : nat) => add_negsucIndIntZ z1 p)
    z2.

Theorem add0LIndIntZ (z : IndInt_p.Z) : z = addIndIntZ (depConstrIndIntPos 0) z.
Proof.
  eapply (depElimPropIndInt (fun (z1 : IndInt_p.Z) => z1 = addIndIntZ (depConstrIndIntPos 0) z1)).
  - induction n.
    + reflexivity.
    + apply (iotaIndIntPos
                IndInt_p.Z
                (fun q => depConstrIndIntPos (S q))
                (fun q => nat_rec (constIndIntZ _) (depConstrIndIntPos 0) (fun m _ => depConstrIndIntNegSuc m) q)
                n
                (fun s => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos (S n)))).
      apply (iotaIndIntPosRev
               IndInt_p.Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               (S n)
               (fun s => depRecIndInt
                           IndInt_p.Z
                           (fun m => depConstrIndIntPos (S m))
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntPos 0)
                                       (fun p _ => depConstrIndIntNegSuc p)
                                       m)
                           (depConstrIndIntPos n) = s)).
      apply (iotaIndIntPos
               IndInt_p.Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               n
               (fun s => depRecIndInt
                           IndInt_p.Z
                           (fun m => depConstrIndIntPos (S m))
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntPos 0)
                                       (fun p _ => depConstrIndIntNegSuc p)
                                       m)
                           (depConstrIndIntPos n) = sucIndIntZ s)).
      apply (@eq_rect_r
                IndInt_p.Z
                (addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n))
                (fun x => depRecIndInt _ _ _ x = _)).
      reflexivity.
      apply IHn.
  - induction n.
    + reflexivity.
    + apply (iotaIndIntNegSuc
                IndInt_p.Z
                (fun q => nat_rec (constIndIntZ _) (depConstrIndIntNegSuc 0) (fun m _ => depConstrIndIntPos m) q)
                (fun q => depConstrIndIntNegSuc (S q))
                n
                (fun s => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc (S n)))).
      apply (iotaIndIntNegSucRev
               IndInt_p.Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               (S n)
               (fun s => depRecIndInt
                           IndInt_p.Z
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntNegSuc 0)
                                       (fun p _ => depConstrIndIntPos p)
                                       m)
                           (fun m => depConstrIndIntNegSuc (S m))
                           (depConstrIndIntNegSuc n) = s)).
      apply (iotaIndIntNegSuc
               IndInt_p.Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               n
               (fun s => depRecIndInt
                           IndInt_p.Z
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntNegSuc 0)
                                       (fun p _ => depConstrIndIntPos p)
                                       m)
                           (fun m => depConstrIndIntNegSuc (S m))
                           (depConstrIndIntNegSuc n) = predIndIntZ s)).
      apply (@eq_rect_r
                IndInt_p.Z
                (addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc n))
                (fun x => depRecIndInt _ _ _ x = _)).
      reflexivity.
      apply IHn.
Qed.

Theorem add0RIndIntZ : forall (z : IndInt_p.Z), z = (addIndIntZ z (depConstrIndIntPos 0)).
  intros.
  unfold addIndIntZ.
  apply (iotaIndIntPosRev
    IndInt_p.Z
    (fun (p : nat) => add_posIndIntZ z p)
    (fun (p : nat) => add_negsucIndIntZ z p)
    0).
  reflexivity.
Qed.

Module GInt.

  Definition Z := (prod nat nat).

End GInt.

Preprocess Module GInt as GInt_p.

Definition eq_GZ (z1 z2 : GInt_p.Z) : Prop :=
  match z1, z2 with
  | (a1, a2), (b1, b2) => a1 + b2 = a2 + b1
  end.

Instance eq_GZ_refl : Reflexive eq_GZ.
Proof.
  intros z.
  destruct z.
  unfold eq_GZ.
  lia.
Qed.

Instance eq_GZ_sym : Symmetric eq_GZ.
Proof.
  unfold eq_GZ.
  intros z1 z2 H.
  destruct z1.
  destruct z2.
  lia.
Qed.

Instance eq_GZ_trans : Transitive eq_GZ.
Proof.
  unfold eq_GZ.
  intros z1 z2 z3 H1 H2.
  destruct z1.
  destruct z2.
  destruct z3.
  lia.
Qed.

Instance eq_GZ_equiv : Equivalence eq_GZ.
Proof.
  split.
  - apply eq_GZ_refl.
  - apply eq_GZ_sym.
  - apply eq_GZ_trans.
Qed.

Theorem eq_GZ_suc : forall (n1 n2 : nat),
    eq_GZ (n1, n2) (S n1, S n2).
Proof.
  intros.
  unfold eq_GZ.
  lia.
Qed.

Theorem eq_GZ_suc_redl : forall (z : GInt_p.Z) (n1 n2 : nat),
    eq_GZ (S n1, S n2) z -> eq_GZ (n1, n2) z.
Proof.
  unfold eq_GZ.
  intros.
  destruct z.
  lia.
Qed.

Theorem eq_GZ_suc_redr : forall (z : GInt_p.Z) (n1 n2 : nat),
    eq_GZ z (S n1, S n2) -> eq_GZ z (n1, n2).
Proof.
  unfold eq_GZ.
  intros.
  destruct z.
  lia.
Qed.

Definition depConstrGZPos (n : nat) : GInt_p.Z := (n, 0).
Definition depConstrGZNegSuc (n : nat) : GInt_p.Z := (0, S n).

Fixpoint canonicalize' (n1 n2 : nat) :=
  match n1, n2 with
  | 0, 0 => (0, 0)
  | S n, 0 => (S n, 0)
  | 0, S m => (0, S m)
  | S n, S m => canonicalize' n m
  end.

Definition canonicalize (z : GInt_p.Z) :=
  match z with
  | (a1, a2) => canonicalize' a1 a2
  end.
Print sumbool.

Theorem canonicalize'Respectful : forall (n1 n2 n3 n4 : nat),
    eq_GZ (n1, n2) (n3, n4) -> canonicalize' n1 n2 = canonicalize' n3 n4.
Proof.
  induction n1; induction n2; induction n3; induction n4; try (unfold eq_GZ; lia); intros.
  - reflexivity.
  - simpl.
    rewrite <- IHn3.
    reflexivity.
    apply eq_GZ_suc_redr.
    apply H.
  - unfold eq_GZ in H.
    assert (n2 = n4).
    lia.
    rewrite H0.
    reflexivity.
  - apply IHn3.
    apply eq_GZ_suc_redr.
    apply H.
  - assert (n1 = n3).
    unfold eq_GZ in H.
    lia.
    rewrite H0.
    reflexivity.
  - rewrite (IHn3 n4).
    reflexivity.
    apply eq_GZ_suc_redr.
    apply H.
  - apply IHn1.
    apply eq_GZ_suc_redl.
    apply H.
  - simpl.
    apply (IHn1 n2 0 (S n4)).
    apply eq_GZ_suc_redl.
    apply H.
  - simpl.
    apply (IHn1 n2 (S n3) 0).
    apply eq_GZ_suc_redl.
    apply H.
  - simpl.
    apply IHn1.
    apply eq_GZ_suc_redl.
    apply eq_GZ_suc_redr.
    apply H.
Defined.

Instance canonicalizeProper : Proper (eq_GZ ==> eq) canonicalize.
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

Theorem canonicalizeSignDec : forall (z : GInt_p.Z),
    { n : nat | (canonicalize z = (n, 0))} +
    { n : nat | (canonicalize z = (0, S n))}.
Proof.
  intros.
  destruct z.
  unfold canonicalize.
  apply canonicalize'SignDec.
Defined.

Print canonicalizeSignDec.

Theorem canonicalizePos : forall (n : nat),
    canonicalize (depConstrGZPos n) = depConstrGZPos n.
Proof.
  intros.
  destruct n; reflexivity.
Defined.

Theorem canonicalizeSignDecPos : forall (n : nat),
    canonicalizeSignDec (depConstrGZPos n) =
    inl (exist (fun (x : nat) => canonicalize (depConstrGZPos n) = (x, 0)) n (canonicalizePos n)).
Proof.
  intros.
  destruct n; reflexivity.
Qed.

Theorem canonicalizeNegSuc : forall (n : nat),
    canonicalize (depConstrGZNegSuc n) = depConstrGZNegSuc n.
Proof.
  intros.
  destruct n; reflexivity.
Defined.

Theorem canonicalizeSignDecNegSuc : forall (n : nat),
    canonicalizeSignDec (depConstrGZNegSuc n) =
    inr (exist (fun (x : nat) => canonicalize (depConstrGZNegSuc n) = (0, S x)) n (canonicalizeNegSuc n)).
Proof.
  intros.
  destruct n; reflexivity.
Qed.

Theorem canonicalize'Pres : forall (n1 n2 : nat),
    eq_GZ (canonicalize (n1, n2)) (n1, n2).
Proof.
  intros n1.
  induction n1; induction n2; try reflexivity.
  simpl.
  rewrite <- eq_GZ_suc.
  apply IHn1.
Defined.

Theorem canonicalizePres : forall (z : GInt_p.Z),
    eq_GZ (canonicalize z) z.
Proof.
  intros.
  destruct z.
  apply canonicalize'Pres.
Defined.

Print eq_rect.

Definition depRecGZ (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : GInt_p.Z) :
  C :=
  match (canonicalizeSignDec z) with
  | inl x => posP (proj1_sig x)
  | inr x => negSucP (proj1_sig x)                     
  end.

Theorem depRecCanonical (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : GInt_p.Z) :
  depRecGZ C posP negSucP z = depRecGZ C posP negSucP (canonicalize z).
Proof.
  unfold depRecGZ.
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
  Proper (eq_GZ ==> eq) (depRecGZ C posP negSucP).
Proof.
  intros z1 z2 H.
  rewrite depRecCanonical.
  rewrite (depRecCanonical _ _ _ z2).
  rewrite H.
  reflexivity.
Qed.

Instance depRecProperEqGZ
  (posP : forall (n : nat), GInt.Z)
  (negSucP : forall (n : nat), GInt.Z) :
  Proper (eq_GZ ==> eq_GZ) (depRecGZ GInt.Z posP negSucP).
Proof.
  intros z1 z2 H.
  rewrite H.
  reflexivity.
Qed.

  Definition ZExtEqual (C : Type) (eq_C : C -> C -> Prop)
    `(eq_C_equiv : Equivalence _ (eq_C)) (f1 f2 : GInt.Z -> C) : Prop :=
    Proper (eq_GZ ==> eq_C) f1 /\ Proper (eq_GZ ==> eq_C) f2 /\
    forall (z1 z2 : GInt.Z), eq_GZ z1 z2 -> eq_C (f1 z1) (f2 z2).

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

Instance depRecGZProperMore (C : Type) (eq_C : C -> C -> Prop)
  `(eq_C_equiv : Equivalence _ (eq_C)) :
  Proper ((natExtEqual C eq_C eq_C_equiv) ==> (natExtEqual C eq_C eq_C_equiv) ==> eq_GZ ==> eq_C) (depRecGZ C).
Proof.
  intros f1 f2 H1 f3 f4 H2 n1 n2 H3.
  rewrite depRecCanonical.
  rewrite (depRecCanonical _ _ _ n2).
  rewrite H3.
  unfold depRecGZ.
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

Definition iotaRecGZPosEq (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
    (Q (depRecGZ C posP negSucP (depConstrGZPos n))) = Q (posP n).
Proof.
  intros.
  unfold depRecGZ.
  rewrite canonicalizeSignDecPos.
  reflexivity.
Qed.

Definition iotaRecGZPos (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
    (Q (depRecGZ C posP negSucP (depConstrGZPos n))) -> Q (posP n).
Proof.
  intros.
  rewrite <- (iotaRecGZPosEq C posP negSucP).
  apply X.
Qed.

Definition iotaRecGZPosRev (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
    Q (posP n) -> (Q (depRecGZ C posP negSucP (depConstrGZPos n))).
Proof.
  intros.
  rewrite (iotaRecGZPosEq C posP negSucP).
  apply X.
Qed.

Definition iotaRecGZNegSucEq (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
    (Q (depRecGZ C posP negSucP (depConstrGZNegSuc n))) = Q (negSucP n).
Proof.
  intros.
  unfold depRecGZ.
  rewrite canonicalizeSignDecNegSuc.
  reflexivity.
Qed.

Definition iotaRecGZNegSuc (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
    (Q (depRecGZ C posP negSucP (depConstrGZNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  rewrite <- (iotaRecGZNegSucEq C posP negSucP).
  apply X.
Qed.

Definition iotaRecGZNegSucRev (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
    Q (negSucP n) -> (Q (depRecGZ C posP negSucP (depConstrGZNegSuc n))).
Proof.
  intros.
  rewrite (iotaRecGZNegSucEq C posP negSucP).
  apply X.
Qed.

Theorem depElimPropGZ (P : GInt.Z -> Prop)
  `(p : Proper (GInt.Z -> Prop) (eq_GZ ==> iff) P)
  (posP : forall (n : nat), P (depConstrGZPos n))
  (negSucP : forall (n : nat), P (depConstrGZNegSuc n))
  (z : GInt.Z) :
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

Definition etaIndInt (z : IndInt_p.Z) := z.

Definition etaGZ (z : GInt_p.Z) := z.

Definition p (x : IndInt_p.Z) : GInt_p.Z :=
  match x with
  | IndInt_p.pos n => (n, 0)
  | IndInt_p.negsuc n => (0, S n)
  end.

Definition f (z : GInt_p.Z) : IndInt_p.Z :=
  match canonicalizeSignDec z with
  | inl x => IndInt_p.pos (proj1_sig x)
  | inr x => IndInt_p.negsuc (proj1_sig x)
  end.

Print tt.

Save setoid IndInt_p.Z GInt_p.Z { promote = p ; forget = f ; types = GInt.Z ; rels = eq_GZ ; equiv_proofs = eq_GZ_equiv }.

Print tt.

Configure Lift IndInt_p.Z GInt_p.Z {
    constrs_a = depConstrIndIntPos depConstrIndIntNegSuc ;
    constrs_b = depConstrGZPos depConstrGZNegSuc ;
    elim_a = depRecIndInt ;
    elim_b = depRecGZ ;
    eta_a = etaIndInt ;
    eta_b = etaGZ ;
    iota_a = iotaIndIntPos iotaIndIntPosRev iotaIndIntNegSuc iotaIndIntNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

Lift IndInt_p.Z GInt_p.Z in depRecIndInt as depRecLifted.

Print depRecLifted.

Print sucIndIntZ.

Configure Lift IndInt_p.Z GInt_p.Z { opaque nat_rec nat_ind }.

(*Lift IndInt_p.Z GInt_p.Z in depConstrIndIntPos as depConstrIndIntPosLifted.

Print depConstrIndIntPosLifted.

Lift IndInt_p.Z GInt_p.Z in depConstrIndIntNegSuc as depConstrIndIntNegSucLifted.

Print depConstrIndIntNegSucLifted.*)

Lift IndInt_p.Z GInt_p.Z in constIndIntZ as constGZ.

Print constGZ.

(*sucIndIntZ = 
fun z : IndInt_p.Z =>
depElimIndInt (constIndIntZ _)
  (fun n : nat =>
   nat_rec (constIndIntZ _) (depConstrIndIntPos 0)
     (fun (m : nat) (_ : constIndIntZ m) => depConstrIndIntNegSuc m) n) z
     : IndInt_p.Z -> IndInt_p.Z*)

Definition base_case := (fun n : nat => depConstrIndIntPos (S n)).

Lift IndInt_p.Z GInt_p.Z in base_case as base_case_lifted.

Print base_case_lifted.

Definition ind_case := (fun n : nat =>
   nat_rec (constIndIntZ _) (depConstrIndIntPos 0)
           (fun (m : nat) (_ : constIndIntZ _ m) => depConstrIndIntNegSuc m) n).

Lift IndInt_p.Z GInt_p.Z in ind_case as lifted_ind_case.

Print lifted_ind_case.

Definition constIndIntZIndInt := constIndIntZ IndInt_p.Z.

Definition sucIndIntZ2 := 
fun z : IndInt_p.Z =>
  depRecIndInt
    IndInt_p.Z
    base_case
    ind_case
    z.

(*Lift IndInt_p.Z GInt_p.Z in depRecIndInt as depRecLifted.

Print depElimLifted.*)

Lift IndInt_p.Z GInt_p.Z in sucIndIntZ2 as sucGZ2.

Print sucIndIntZ2.

Print sucGZ2.

Lift IndInt_p.Z GInt_p.Z in sucIndIntZ as sucGZ.

Print sucIndIntZ.

Print sucGZ.

Instance sucGZProper :
  Proper (eq_GZ ==> eq_GZ) sucGZ.
Proof.
  intros z1 z2 H.
  unfold sucGZ.
  apply depRecProperEqGZ.
  apply H.
Qed.

Lift IndInt_p.Z GInt_p.Z in predIndIntZ as predGZ.

Print predIndIntZ.

Print predGZ.

Instance predGZProper :
  Proper (eq_GZ ==> eq_GZ) predGZ.
Proof.
  intros z1 z2 H.
  unfold predGZ.
  apply depRecProperEqGZ.
  apply H.
Qed.

Lift IndInt_p.Z GInt_p.Z in add_posIndIntZ as add_posGZ.

Print add_posIndIntZ.

Print add_posGZ.

Instance add_posGZProper :
  Proper (eq_GZ ==> eq ==> eq_GZ) add_posGZ.
Proof.
  intros z1 z2 H1 n1 n2 H2.
  unfold add_posGZ.
  subst.
  induction n2.
  - simpl. apply H1.
  - simpl. f_equiv. apply IHn2.
Qed.   

Lift IndInt_p.Z GInt_p.Z in add_negsucIndIntZ as add_negsucGZ.

Print add_negsucIndIntZ.

Print add_negsucGZ.

Instance add_negsucGZProper :
  Proper (eq_GZ ==> eq ==> eq_GZ) add_negsucGZ.
Proof.
  intros z1 z2 H1 n1 n2 H2.
  unfold add_negsucGZ.
  subst.
  induction n2.
  - simpl. f_equiv. apply H1.
  - simpl. f_equiv. apply IHn2.
Qed.  

Lift IndInt_p.Z GInt_p.Z in addIndIntZ as addGZ.

Print addIndIntZ.

Print addGZ.

Instance addGZProper :
  Proper (eq_GZ ==> eq_GZ ==> eq_GZ) addGZ.
Proof.
  intros z1 z2 H1 z3 z4 H2.
  unfold addGZ.
  apply (depRecGZProperMore GInt.Z eq_GZ eq_GZ_equiv).
  - split.
    apply add_posGZProper.
    reflexivity.
    split.
    apply add_posGZProper.
    reflexivity.
    intros.
    rewrite H.
    apply add_posGZProper;
    auto.
  - split.
    apply add_negsucGZProper.
    reflexivity.
    split.
    apply add_negsucGZProper.
    reflexivity.
    intros.
    rewrite H.
    apply add_negsucGZProper;
    auto.
  - apply H2.
Qed.

Lift IndInt_p.Z GInt_p.Z in add0RIndIntZ as add0RGZ.

Print add0RGZ.

Print add0LIndIntZ.

Definition add0LMotiveIndInt := fun z1 : IndInt_p.Z => z1 = addIndIntZ (depConstrIndIntPos 0) z1.

Lift IndInt_p.Z GInt_p.Z in add0LMotiveIndInt as add0LMotiveGZ.

Definition nat_ind_pos_motive :=
  (fun n0 : nat =>
      depConstrIndIntPos n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n0)).

Definition add0LPosCaseIndInt :=
    (fun n : nat =>
   nat_ind
     (fun n0 : nat =>
      depConstrIndIntPos n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n0)) eq_refl
     (fun (n0 : nat)
        (IHn : depConstrIndIntPos n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n0)) =>
      iotaIndIntPos IndInt_p.Z (fun q : nat => depConstrIndIntPos (S q))
        (fun q : nat =>
         nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
           (fun (m : nat) (_ : constIndIntZ nat m) => depConstrIndIntNegSuc m) q) n0
        (fun s : IndInt_p.Z => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos (S n0)))
        (iotaIndIntPosRev IndInt_p.Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
           (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) (S n0)
           (fun s : IndInt_p.Z =>
            depRecIndInt IndInt_p.Z (fun m : nat => depConstrIndIntPos (S m))
              (fun m : nat =>
               nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
                 (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntNegSuc p) m)
              (depConstrIndIntPos n0) = s)
           (iotaIndIntPos IndInt_p.Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
              (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) n0
              (fun s : IndInt_p.Z =>
               depRecIndInt IndInt_p.Z (fun m : nat => depConstrIndIntPos (S m))
                 (fun m : nat =>
                  nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
                    (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntNegSuc p) m)
                 (depConstrIndIntPos n0) = sucIndIntZ s)
              (eq_rect_r
                 (fun x : IndInt_p.Z =>
                  depRecIndInt IndInt_p.Z (fun m : nat => depConstrIndIntPos (S m))
                    (fun m : nat =>
                     nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
                       (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntNegSuc p) m) x =
                  sucIndIntZ
                    (depRecIndInt IndInt_p.Z
                       (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
                       (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q)
                       (depConstrIndIntPos n0))) eq_refl IHn)))) n).  

Lift IndInt_p.Z GInt_p.Z in add0LPosCaseIndInt as add0LPosCaseGZ.

Definition add0LNegSucCaseIndInt := (fun n : nat =>
   nat_ind
     (fun n0 : nat =>
      depConstrIndIntNegSuc n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc n0))
     eq_refl
     (fun (n0 : nat)
        (IHn : depConstrIndIntNegSuc n0 =
               addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc n0)) =>
      iotaIndIntNegSuc IndInt_p.Z
        (fun q : nat =>
         nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
           (fun (m : nat) (_ : constIndIntZ nat m) => depConstrIndIntPos m) q)
        (fun q : nat => depConstrIndIntNegSuc (S q)) n0
        (fun s : IndInt_p.Z => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc (S n0)))
        (iotaIndIntNegSucRev IndInt_p.Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
           (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) (S n0)
           (fun s : IndInt_p.Z =>
            depRecIndInt IndInt_p.Z
              (fun m : nat =>
               nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
                 (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntPos p) m)
              (fun m : nat => depConstrIndIntNegSuc (S m)) (depConstrIndIntNegSuc n0) = s)
           (iotaIndIntNegSuc IndInt_p.Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
              (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) n0
              (fun s : IndInt_p.Z =>
               depRecIndInt IndInt_p.Z
                 (fun m : nat =>
                  nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
                    (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntPos p) m)
                 (fun m : nat => depConstrIndIntNegSuc (S m)) (depConstrIndIntNegSuc n0) =
               predIndIntZ s)
              (eq_rect_r
                 (fun x : IndInt_p.Z =>
                  depRecIndInt IndInt_p.Z
                    (fun m : nat =>
                     nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
                       (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntPos p) m)
                    (fun m : nat => depConstrIndIntNegSuc (S m)) x =
                  predIndIntZ
                    (depRecIndInt IndInt_p.Z
                       (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
                       (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q)
                       (depConstrIndIntNegSuc n0))) eq_refl IHn)))) n).

Lift IndInt_p.Z GInt_p.Z in add0LNegSucCaseIndInt as add0LNecSucCaseGZ.

Instance add0LMotiveProper :
  Proper (eq_GZ ==> iff) add0LMotiveGZ.
Proof.
  intros z1 z2 H.
  unfold add0LMotiveGZ.
  rewrite H.
  reflexivity.
Qed.

Definition appliedDepElimPropIndInt := depElimPropIndInt add0LMotiveIndInt.
Definition appliedDepElimPropGZ := depElimPropGZ add0LMotiveGZ add0LMotiveProper.

Configure Lift IndInt_p.Z GInt_p.Z {
    constrs_a = depConstrIndIntPos depConstrIndIntNegSuc ;
    constrs_b = depConstrGZPos depConstrGZNegSuc ;
    elim_a = appliedDepElimPropIndInt ;
    elim_b = appliedDepElimPropGZ ;
    eta_a = etaIndInt ;
    eta_b = etaGZ ;
    iota_a = iotaIndIntPos iotaIndIntPosRev iotaIndIntNegSuc iotaIndIntNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

Print appliedDepElimPropGZ.

Theorem add0LIndIntZ' (z : IndInt_p.Z) : z = addIndIntZ (depConstrIndIntPos 0) z.
Proof.
  apply appliedDepElimPropIndInt.
  apply add0LPosCaseIndInt.
  apply add0LNegSucCaseIndInt.
Qed.
  
Lift IndInt_p.Z GInt_p.Z in add0LIndIntZ' as add0LGZ.

Print add0LMotiveGZ.
Print add0LGZ.
