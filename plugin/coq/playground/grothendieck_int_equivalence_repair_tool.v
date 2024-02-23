Require Import Relation_Definitions Morphisms Setoid Lia.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.

Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.
Set DEVOID lift type.

Module IndInt.

Inductive Z : Set :=
| pos : nat -> Z
| negsuc : nat -> Z.
       
End IndInt.

Preprocess Module IndInt as IndInt_p.

Definition depConstrIndIntPos (n : nat) : IndInt_p.Z := IndInt_p.pos n.
Definition depConstrIndIntNegSuc (n : nat) : IndInt_p.Z := IndInt_p.negsuc n.

Definition depElimIndInt (P : IndInt_p.Z -> Type)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (z : IndInt_p.Z) :
  P z :=
  match z with
  | IndInt_p.pos n => posP n
  | IndInt_p.negsuc n => negSucP n
  end.

Theorem iotaIndIntPos (P : IndInt_p.Z -> Type)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrIndIntPos n) -> Type),
  (Q (depElimIndInt P posP negSucP (depConstrIndIntPos n))) -> Q (posP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaIndIntPosRev (P : IndInt_p.Z -> Type)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrIndIntPos n) -> Type),
  Q (posP n) -> (Q (depElimIndInt P posP negSucP (depConstrIndIntPos n))).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaIndIntNegSuc (P : IndInt_p.Z -> Type)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrIndIntNegSuc n) -> Type),
  (Q (depElimIndInt P posP negSucP (depConstrIndIntNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaIndIntNegSucRev (P : IndInt_p.Z -> Type)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (n : nat) :
  forall (Q : P (depConstrIndIntNegSuc n) -> Type),
  Q (negSucP n) -> (Q (depElimIndInt P posP negSucP (depConstrIndIntNegSuc n))).
Proof.
  intros.
  apply X.
Qed.

Definition constIndIntZ {A : Type} (a : A) := IndInt_p.Z.

Definition sucIndIntZ (z : IndInt_p.Z) : IndInt_p.Z :=
  depElimIndInt
    constIndIntZ
    (fun (n : nat) => depConstrIndIntPos (S n))
    (fun (n : nat) => nat_rec constIndIntZ (depConstrIndIntPos 0) (fun (m : nat) _ => depConstrIndIntNegSuc m) n)
    z.

Definition predIndIntZ (z : IndInt_p.Z) : IndInt_p.Z :=
  depElimIndInt
    constIndIntZ
    (fun (n : nat) => nat_rec constIndIntZ (depConstrIndIntNegSuc 0) (fun (m : nat) _ => depConstrIndIntPos m) n)
    (fun (n : nat) => depConstrIndIntNegSuc (S n))
    z.

Definition add_posIndIntZ (z : IndInt_p.Z) (n : nat) : IndInt_p.Z :=
  nat_rec constIndIntZ z (fun _ (p : IndInt_p.Z) => sucIndIntZ p) n.

Definition add_negsucIndIntZ (z : IndInt_p.Z) (n : nat) : IndInt_p.Z :=
  nat_rec constIndIntZ (predIndIntZ z) (fun _ (p : IndInt_p.Z) => predIndIntZ p) n.

Definition addIndIntZ (z1 z2 : IndInt_p.Z) : IndInt_p.Z :=
  depElimIndInt
    constIndIntZ
    (fun (p : nat) => add_posIndIntZ z1 p)
    (fun (p : nat) => add_negsucIndIntZ z1 p)
    z2.

Theorem add0LIndIntZ (z : IndInt_p.Z) : z = addIndIntZ (depConstrIndIntPos 0) z.
Proof.
  eapply (depElimIndInt (fun (z1 : IndInt_p.Z) => z1 = addIndIntZ (depConstrIndIntPos 0) z1)).
  - induction n.
    + reflexivity.
    + apply (iotaIndIntPos
                constIndIntZ
                (fun q => depConstrIndIntPos (S q))
                (fun q => nat_rec constIndIntZ (depConstrIndIntPos 0) (fun m _ => depConstrIndIntNegSuc m) q)
                n
                (fun s => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos (S n)))).
      apply (iotaIndIntPosRev
               constIndIntZ
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               (S n)
               (fun s => depElimIndInt
                           constIndIntZ
                           (fun m => depConstrIndIntPos (S m))
                           (fun m => nat_rec
                                       constIndIntZ
                                       (depConstrIndIntPos 0)
                                       (fun p _ => depConstrIndIntNegSuc p)
                                       m)
                           (depConstrIndIntPos n) = s)).
      apply (iotaIndIntPos
               constIndIntZ
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               n
               (fun s => depElimIndInt
                           constIndIntZ
                           (fun m => depConstrIndIntPos (S m))
                           (fun m => nat_rec
                                       constIndIntZ
                                       (depConstrIndIntPos 0)
                                       (fun p _ => depConstrIndIntNegSuc p)
                                       m)
                           (depConstrIndIntPos n) = sucIndIntZ s)).
      apply (f_equal sucIndIntZ).
      apply IHn.
  - induction n.
    + reflexivity.
    + apply (iotaIndIntNegSuc
                constIndIntZ
                (fun q => nat_rec constIndIntZ (depConstrIndIntNegSuc 0) (fun m _ => depConstrIndIntPos m) q)
                (fun q => depConstrIndIntNegSuc (S q))
                n
                (fun s => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc (S n)))).
      apply (iotaIndIntNegSucRev
               constIndIntZ
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               (S n)
               (fun s => depElimIndInt
                           constIndIntZ
                           (fun m => nat_rec
                                       constIndIntZ
                                       (depConstrIndIntNegSuc 0)
                                       (fun p _ => depConstrIndIntPos p)
                                       m)
                           (fun m => depConstrIndIntNegSuc (S m))
                           (depConstrIndIntNegSuc n) = s)).
      apply (iotaIndIntNegSuc
               constIndIntZ
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               n
               (fun s => depElimIndInt
                           constIndIntZ
                           (fun m => nat_rec
                                       constIndIntZ
                                       (depConstrIndIntNegSuc 0)
                                       (fun p _ => depConstrIndIntPos p)
                                       m)
                           (fun m => depConstrIndIntNegSuc (S m))
                           (depConstrIndIntNegSuc n) = predIndIntZ s)).
      apply (f_equal predIndIntZ).
      apply IHn.
Qed.

Theorem add0RIndIntZ : forall (z : IndInt_p.Z), z = (addIndIntZ z (depConstrIndIntPos 0)).
  intros.
  unfold addIndIntZ.
  apply (iotaIndIntPosRev
    constIndIntZ
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
  C.
Proof.
  pose (canonicalizeSignDec z).
  apply sig_rect.
  destruct (canonicalizeSignDec z).
  - apply proj1_sig in s.
    apply posP in s.
    apply s.
  - apply proj1_sig in s.
    apply negSucP in s.
    apply s.
Defined.

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
    elim_a = depElimIndInt ;
    elim_b = depRecGZ ;
    eta_a = etaIndInt ;
    eta_b = etaGZ ;
    iota_a = iotaIndIntPos iotaIndIntPosRev iotaIndIntNegSuc iotaIndIntNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

Lift IndInt_p.Z GInt_p.Z in constIndIntZ as constGZ.

Lift IndInt_p.Z GInt_p.Z in sucIndIntZ as sucGZ.
