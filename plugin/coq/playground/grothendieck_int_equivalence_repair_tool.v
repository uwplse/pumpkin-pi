Require Import Relation_Definitions Morphisms Lia.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.
Require Import SetoidClass.

(* 
 * In this file, we define two representations of integers.
 * The first is as an inductive type with two constructors,
 * representing adjoining two copies of nat to form the 
 * number line.
 *)

Inductive Z : Set :=
| pos : nat -> Z
| negsuc : nat -> Z.


(* 
 * We define the side of the configuration corresponding to this type.
 *)

Definition depConstrIndIntPos (n : nat) : Z := pos n.
Definition depConstrIndIntNegSuc (n : nat) : Z := negsuc n.

(*
 * Notice that we have two eliminators. The first is not dependently typed,
 * but eliminates into Type, while the second is dependently typed but eliminates
 * into Prop. While we could write a single eliminator for Z, we need
 * two for our repair target GZ, and the eliminators used for both the source
 * and target need their types to match.
 *)

Definition depRecIndInt (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : Z) :
  C :=
  match z with
  | pos n => posP n
  | negsuc n => negSucP n
  end.

Definition depElimPropIndInt (P : Z -> Prop)
  (posP : forall (n : nat), P (depConstrIndIntPos n))
  (negSucP : forall (n : nat), P (depConstrIndIntNegSuc n))
  (z : Z) :
  P z :=
  match z with
  | pos n => posP n
  | negsuc n => negSucP n
  end.

(* 
 * Below, we define the iota reduction rules. We only define them
 * for depRecIndInt, as we will not need to reduce applications of
 * depElimPropIndInt.
 *)

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

(* 
 * We define eta, because the repair tool requires it,
 * but it is not used when transforming these terms,
 * so we just set it to the identity.
 *)

Definition etaIndInt (z : Z) := z.

(* 
 * Now, we define functions and theorems on this type,
 * explicitly using the constructors, eliminators,
 * and iota reduction rules we defined above,
 * and not the ones Coq generates automatically for the 
 * inductive type. This style of annotation is consistent with
 * prior work.
 *)

Definition constIndIntZ (A : Type) (a : A) := Z.

Definition sucIndIntZ (z : Z) : Z :=
  depRecIndInt
    Z
    (fun (n : nat) => depConstrIndIntPos (S n))
    (fun (n : nat) => nat_rec (constIndIntZ _) (depConstrIndIntPos 0) (fun (m : nat) _ => depConstrIndIntNegSuc m) n)
    z.

Definition predIndIntZ (z : Z) : Z :=
  depRecIndInt
    Z
    (fun (n : nat) => nat_rec (constIndIntZ _) (depConstrIndIntNegSuc 0) (fun (m : nat) _ => depConstrIndIntPos m) n)
    (fun (n : nat) => depConstrIndIntNegSuc (S n))
    z.

Definition add_posIndIntZ (z : Z) (n : nat) : Z :=
  nat_rec (constIndIntZ _) z (fun _ (p : Z) => sucIndIntZ p) n.

Definition add_negsucIndIntZ (z : Z) (n : nat) : Z :=
  nat_rec (constIndIntZ _) (predIndIntZ z) (fun _ (p : Z) => predIndIntZ p) n.

Definition addIndIntZ (z1 z2 : Z) : Z :=
  depRecIndInt
    Z
    (fun (p : nat) => add_posIndIntZ z1 p)
    (fun (p : nat) => add_negsucIndIntZ z1 p)
    z2.

Theorem add0LIndIntZ (z : Z) : z = addIndIntZ (depConstrIndIntPos 0) z.
Proof.
  eapply (depElimPropIndInt (fun (z1 : Z) => z1 = addIndIntZ (depConstrIndIntPos 0) z1)).
  - induction n.
    + reflexivity.
    + apply (iotaIndIntPos
                Z
                (fun q => depConstrIndIntPos (S q))
                (fun q => nat_rec (constIndIntZ _) (depConstrIndIntPos 0) (fun m _ => depConstrIndIntNegSuc m) q)
                n
                (fun s => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos (S n)))).
      apply (iotaIndIntPosRev
               Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               (S n)
               (fun s => depRecIndInt
                           Z
                           (fun m => depConstrIndIntPos (S m))
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntPos 0)
                                       (fun p _ => depConstrIndIntNegSuc p)
                                       m)
                           (depConstrIndIntPos n) = s)).
      apply (iotaIndIntPos
               Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               n
               (fun s => depRecIndInt
                           Z
                           (fun m => depConstrIndIntPos (S m))
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntPos 0)
                                       (fun p _ => depConstrIndIntNegSuc p)
                                       m)
                           (depConstrIndIntPos n) = sucIndIntZ s)).
      apply (@eq_rect_r
                Z
                (addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n))
                (fun x => depRecIndInt _ _ _ x = _)).
      reflexivity.
      apply IHn.
  - induction n.
    + reflexivity.
    + apply (iotaIndIntNegSuc
                Z
                (fun q => nat_rec (constIndIntZ _) (depConstrIndIntNegSuc 0) (fun m _ => depConstrIndIntPos m) q)
                (fun q => depConstrIndIntNegSuc (S q))
                n
                (fun s => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc (S n)))).
      apply (iotaIndIntNegSucRev
               Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               (S n)
               (fun s => depRecIndInt
                           Z
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntNegSuc 0)
                                       (fun p _ => depConstrIndIntPos p)
                                       m)
                           (fun m => depConstrIndIntNegSuc (S m))
                           (depConstrIndIntNegSuc n) = s)).
      apply (iotaIndIntNegSuc
               Z
               (fun q => add_posIndIntZ (depConstrIndIntPos 0) q)
               (fun q => add_negsucIndIntZ (depConstrIndIntPos 0) q)
               n
               (fun s => depRecIndInt
                           Z
                           (fun m => nat_rec
                                       (constIndIntZ _)
                                       (depConstrIndIntNegSuc 0)
                                       (fun p _ => depConstrIndIntPos p)
                                       m)
                           (fun m => depConstrIndIntNegSuc (S m))
                           (depConstrIndIntNegSuc n) = predIndIntZ s)).
      apply (@eq_rect_r
                Z
                (addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc n))
                (fun x => depRecIndInt _ _ _ x = _)).
      reflexivity.
      apply IHn.
Qed.

Theorem add0RIndIntZ : forall (z : Z), z = (addIndIntZ z (depConstrIndIntPos 0)).
  intros.
  unfold addIndIntZ.
  apply (iotaIndIntPosRev
    Z
    (fun (p : nat) => add_posIndIntZ z p)
    (fun (p : nat) => add_negsucIndIntZ z p)
    0).
  reflexivity.
Qed.

(*
 * Here, we define a second representation of the integers.
 * The pair (n1, n2) represents the integer n1 - n2.
 * Multiple elements of this type represent the same integer, so 
 * we would want to think of it as a quotient, with 
 * [(n1, n2)] = [(n3, n4)] if n1 + n4 = n2 + n3.
 * Coq does not support quotient types, so instead we represent
 * this using a setoid.
 *)

Module GInt.

  Definition GZ := (prod nat nat).

End GInt.

Definition GZ := GInt.GZ.

(*
 * Here, we define the equivalence relation on GZ,
 * and register it as an instance of the Equivalence typeclass
 * with Coq.
 *)

Definition eq_GZ (z1 z2 : GZ) : Prop :=
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

(*
 * We can officially declare an instance showing that GZ forms a setoid
 * with GZ as the equivalence relation. However, this is not necessary
 * for any of our repair work. The automation we need derives from instances of
 * Equivalence and Proper, not Setoid.
 *)

Instance GZ_setoid : Setoid GZ := {equiv := eq_GZ ; setoid_equiv := eq_GZ_equiv}.

(* 
 * Now, we define the side of the configuration for GZ.
 * We define several other theorems along the way to help define
 * the needed eliminators and iota-reduction rules.
 *)

Theorem eq_GZ_suc : forall (n1 n2 : nat),
    eq_GZ (n1, n2) (S n1, S n2).
Proof.
  intros.
  unfold eq_GZ.
  lia.
Qed.

Theorem eq_GZ_suc_redl : forall (z : GZ) (n1 n2 : nat),
    eq_GZ (S n1, S n2) z -> eq_GZ (n1, n2) z.
Proof.
  unfold eq_GZ.
  intros.
  destruct z.
  lia.
Qed.

Theorem eq_GZ_suc_redr : forall (z : GZ) (n1 n2 : nat),
    eq_GZ z (S n1, S n2) -> eq_GZ z (n1, n2).
Proof.
  unfold eq_GZ.
  intros.
  destruct z.
  lia.
Qed.

Definition depConstrGZPos (n : nat) : GZ := (n, 0).
Definition depConstrGZNegSuc (n : nat) : GZ := (0, S n).

Fixpoint canonicalize' (n1 n2 : nat) :=
  match n1, n2 with
  | 0, 0 => (0, 0)
  | S n, 0 => (S n, 0)
  | 0, S m => (0, S m)
  | S n, S m => canonicalize' n m
  end.

Definition canonicalize (z : GZ) :=
  match z with
  | (a1, a2) => canonicalize' a1 a2
  end.

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

Theorem canonicalizeSignDec : forall (z : GZ),
    { n : nat | (canonicalize z = (n, 0))} +
    { n : nat | (canonicalize z = (0, S n))}.
Proof.
  intros.
  destruct z.
  unfold canonicalize.
  apply canonicalize'SignDec.
Defined.

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

Theorem canonicalizePres : forall (z : GZ),
    eq_GZ (canonicalize z) z.
Proof.
  intros.
  destruct z.
  apply canonicalize'Pres.
Defined.

Definition depRecGZ (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : GZ) :
  C :=
  match (canonicalizeSignDec z) with
  | inl x => posP (proj1_sig x)
  | inr x => negSucP (proj1_sig x)                     
  end.

Theorem depRecCanonical (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : GZ) :
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

(*
 * Notice that we prove an instance of the Proper
 * typeclass showing that depRecGZ is proper with respect to
 * our equivalence relations. This is important to allow
 * the setoid automation to automatically produce rewrite proofs.
 * In general, we should prove that all functions we define are Proper, 
 * but which functions must be proven proper for the automation
 * to function will vary on a case-by-case basis.
 *)

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
  (posP : forall (n : nat), GZ)
  (negSucP : forall (n : nat), GZ) :
  Proper (eq_GZ ==> eq_GZ) (depRecGZ GZ posP negSucP).
Proof.
  intros z1 z2 H.
  rewrite H.
  reflexivity.
Qed.

(*
 * We would like to be able to rewrite the function arguments to depRec, 
 * but we can't actually prove functions are equal without some form of 
 * extensionality. Instead, we define extensional equality as a relation. 
 * It isn't an equivalence relation, because it isn't reflexive; not all 
 * functions are proper morphisms. It is symmetric and transitive, though,
 * so it forms a partial equivalence relation, which is good enough to 
 * do rewriting.
 *)

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

(*
 * We have that depRec is proper with respect to the function arguments
 * as a separate instance from our other proof. This is because the lack
 * of reflexivity on natExtEqual means that we would need to manually
 * prove that the function arguments are related to themselves when
 * rewriting other arguments to depRec. Having both instances means that
 * rewriting the non-function argument does not generate these extra
 * obligations.
 *)

Instance depRecGZCasesProper (C : Type) (eq_C : C -> C -> Prop)
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

(*
 * Notice that we de not prove that depElimPropGZ is proper.
 * This is because its motive is dependently typed, and thus
 * not compatible with the built in setoid automation.
 * This is the primary reason for having two eliminators;
 * we need a dependent eliminator to Prop to prove theorems,
 * but a nondependent one to Type to easily do rewriting.
 *)

Theorem depElimPropGZ (P : GZ -> Prop)
  `(p : Proper (GZ -> Prop) (eq_GZ ==> iff) P)
  (posP : forall (n : nat), P (depConstrGZPos n))
  (negSucP : forall (n : nat), P (depConstrGZNegSuc n))
  (z : GZ) :
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

Definition iotaRecGZPosEq (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  depRecGZ C posP negSucP (depConstrGZPos n) = posP n.
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
  depRecGZ C posP negSucP (depConstrGZNegSuc n) = negSucP n.
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

(* Again, this eta is required as an input by the tool, but will not be used. *)

Definition etaGZ (z : GZ) := z.

(* We define the setoid equivalence between Z and GZ here.
 * We don't strictly need to have it defined to do the transformation,
 * but the existing repair tool currently uses the functions internally 
 * as a key for caching.
 *)
Definition p (x : Z) : GZ :=
  match x with
  | pos n => (n, 0)
  | negsuc n => (0, S n)
  end.

Definition f (z : GZ) : Z :=
  depRecGZ Z (fun n => pos n) (fun n => negsuc n) z.

(*
 * Here, we prove that these functions actually form an equivalence.
 * The proofs are not actually used in the transformation, but it 
 * demonstrates the condition we require to hold for the transformation
 * to be valid.
 *)

Theorem section : forall (x : Z), f (p x) = x.
Proof.
  intros.
  destruct x.
  - unfold f.
    simpl.
    rewrite <- (iotaRecGZPosEq Z (fun n => pos n) (fun n => negsuc n)).
    reflexivity.
  - unfold f.
    simpl.
    rewrite <- (iotaRecGZNegSucEq Z (fun n => pos n) (fun n => negsuc n)).
    reflexivity.
Qed.

Theorem retraction : forall (x : GZ), eq_GZ (p (f x)) x.
Proof.
  apply depElimPropGZ.
  - intros z1 z2 H.
    rewrite H.
    reflexivity.
  - intros.
    unfold f.
    rewrite (iotaRecGZPosEq Z _ _).
    reflexivity.
  - intros.
    unfold f.
    rewrite (iotaRecGZNegSucEq Z _ _).
    reflexivity.
Qed.

(*
 * Now, we specify our setoid to the automation. Types contains a list of
 * the types with specified equivalence relations, rels contains the equivalence
 * relations, and equiv_proofs contains the proofs that the relations are 
 * instances of Equvialence. They must be provided in the same order; that is,
 * the nth element of types, rels, and equiv_proofs should all correspond to the
 * same type.
 *)

Save setoid Z GZ { promote = p ; forget = f ; types = GZ ; rels = eq_GZ ; equiv_proofs = eq_GZ_equiv }.

(*
 * Next, we register the configuration we defined with Pumpkin Pi.
 * We can currently only provide one kind of eliminator at a time to the repair tool,
 * so we need to ensure that the terms we lift only have one kind of eliminator in them.
 * We will see how work around this to lift a term with multiple kinds of eliminators later.
 *)

Configure Lift Z GZ {
    constrs_a = depConstrIndIntPos depConstrIndIntNegSuc ;
    constrs_b = depConstrGZPos depConstrGZNegSuc ;
    elim_a = depRecIndInt ;
    elim_b = depRecGZ ;
    eta_a = etaIndInt ;
    eta_b = etaGZ ;
    iota_a = iotaIndIntPos iotaIndIntPosRev iotaIndIntNegSuc iotaIndIntNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

(*
 * We first lift the dependent eliminator, which prevents the tool from
 * unfolding the definition of the repaired eliminator. This helds the 
 * setoid automation successfully discover proofs.
 *)

Lift Z GZ in depRecIndInt as depRecLifted.

(* Now, we begin lifting the functions we defined over Z. *)

Lift Z GZ in constIndIntZ as constGZ.

Lift Z GZ in sucIndIntZ as sucGZ.

(* At present, Pumpkin Pi will not generate proofs that the
 * functions we define are Proper, so we need to do this manually.
 * In the future, we can automatically discover many of these 
 * proofs using tactics for proof search, such as the one below.
 *)

Instance sucGZProper :
  Proper (eq_GZ ==> eq_GZ) sucGZ.
Proof.
  solve_proper.
Qed.

Lift Z GZ in predIndIntZ as predGZ.

Instance predGZProper :
  Proper (eq_GZ ==> eq_GZ) predGZ.
Proof.
  solve_proper.
Qed.

Lift Z GZ in add_posIndIntZ as add_posGZ.

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

Lift Z GZ in add_negsucIndIntZ as add_negsucGZ.

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

Lift Z GZ in addIndIntZ as addGZ.

Instance addGZProper :
  Proper (eq_GZ ==> eq_GZ ==> eq_GZ) addGZ.
Proof.
  intros z1 z2 H1 z3 z4 H2.
  unfold addGZ.
  apply (depRecGZCasesProper GZ eq_GZ eq_GZ_equiv).
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

Lift Z GZ in add0RIndIntZ as add0RGZ.

(* 
 * Now, we will lift add0LIndIntZ. This theorem uses both depRecGZ and
 * depElimPropGZ in its proof. As such, we cannot directly lift it,
 * because we can't provide Pumpkin Pi with both eliminators at once.
 * Instead, we first decompose the term into subterms which only 
 * contain depRecGZ, and lift all of those terms.
 *)

Definition add0LMotiveIndInt := fun z1 : Z => z1 = addIndIntZ (depConstrIndIntPos 0) z1.

Lift Z GZ in add0LMotiveIndInt as add0LMotiveGZ.

(*
 * These terms are large, but are directly copied and pasted from
 * printing add0LIndIntZ, so they aren't hard to obtain. We could also
 * generate these terms in proof mode instead if the terms
 * become too large to handle manually.
 *)

Definition add0LPosCaseIndInt :=
  (fun n : nat =>
   nat_ind
     (fun n0 : nat =>
      depConstrIndIntPos n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n0)) eq_refl
     (fun (n0 : nat)
        (IHn : depConstrIndIntPos n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos n0)) =>
      iotaIndIntPos Z (fun q : nat => depConstrIndIntPos (S q))
        (fun q : nat =>
         nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
           (fun (m : nat) (_ : constIndIntZ nat m) => depConstrIndIntNegSuc m) q) n0
        (fun s : Z => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntPos (S n0)))
        (iotaIndIntPosRev Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
           (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) (S n0)
           (fun s : Z =>
            depRecIndInt Z (fun m : nat => depConstrIndIntPos (S m))
              (fun m : nat =>
               nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
                 (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntNegSuc p) m)
              (depConstrIndIntPos n0) = s)
           (iotaIndIntPos Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
              (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) n0
              (fun s : Z =>
               depRecIndInt Z (fun m : nat => depConstrIndIntPos (S m))
                 (fun m : nat =>
                  nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
                    (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntNegSuc p) m)
                 (depConstrIndIntPos n0) = sucIndIntZ s)
              (eq_rect_r
                 (fun x : Z =>
                  depRecIndInt Z (fun m : nat => depConstrIndIntPos (S m))
                    (fun m : nat =>
                     nat_rec (constIndIntZ nat) (depConstrIndIntPos 0)
                       (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntNegSuc p) m) x =
                  sucIndIntZ
                    (depRecIndInt Z
                       (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
                       (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q)
                       (depConstrIndIntPos n0))) eq_refl IHn)))) n).  

Lift Z GZ in add0LPosCaseIndInt as add0LPosCaseGZ.

Definition add0LNegSucCaseIndInt :=
  (fun n : nat =>
   nat_ind
     (fun n0 : nat =>
      depConstrIndIntNegSuc n0 = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc n0))
     eq_refl
     (fun (n0 : nat)
        (IHn : depConstrIndIntNegSuc n0 =
               addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc n0)) =>
      iotaIndIntNegSuc Z
        (fun q : nat =>
         nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
           (fun (m : nat) (_ : constIndIntZ nat m) => depConstrIndIntPos m) q)
        (fun q : nat => depConstrIndIntNegSuc (S q)) n0
        (fun s : Z => s = addIndIntZ (depConstrIndIntPos 0) (depConstrIndIntNegSuc (S n0)))
        (iotaIndIntNegSucRev Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
           (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) (S n0)
           (fun s : Z =>
            depRecIndInt Z
              (fun m : nat =>
               nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
                 (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntPos p) m)
              (fun m : nat => depConstrIndIntNegSuc (S m)) (depConstrIndIntNegSuc n0) = s)
           (iotaIndIntNegSuc Z (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
              (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q) n0
              (fun s : Z =>
               depRecIndInt Z
                 (fun m : nat =>
                  nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
                    (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntPos p) m)
                 (fun m : nat => depConstrIndIntNegSuc (S m)) (depConstrIndIntNegSuc n0) =
               predIndIntZ s)
              (eq_rect_r
                 (fun x : Z =>
                  depRecIndInt Z
                    (fun m : nat =>
                     nat_rec (constIndIntZ nat) (depConstrIndIntNegSuc 0)
                       (fun (p : nat) (_ : constIndIntZ nat p) => depConstrIndIntPos p) m)
                    (fun m : nat => depConstrIndIntNegSuc (S m)) x =
                  predIndIntZ
                    (depRecIndInt Z
                       (fun q : nat => add_posIndIntZ (depConstrIndIntPos 0) q)
                       (fun q : nat => add_negsucIndIntZ (depConstrIndIntPos 0) q)
                       (depConstrIndIntNegSuc n0))) eq_refl IHn)))) n).

Lift Z GZ in add0LNegSucCaseIndInt as add0LNecSucCaseGZ.

(*
 * depElimPropGZ requires as an argument that the motive is Proper,
 * so we need to write this proof.
 *)

Instance add0LMotiveProper :
  Proper (eq_GZ ==> iff) add0LMotiveGZ.
Proof.
  intros z1 z2 H.
  unfold add0LMotiveGZ.
  rewrite H.
  reflexivity.
Qed.

(* 
 * To account for that depElimPropGZ requires a proof of Proper as an
 * argument, we specialize our eliminator to this motive, so that the types
 * align.
 *)

Definition appliedDepElimPropIndInt := depElimPropIndInt add0LMotiveIndInt.
Definition appliedDepElimPropGZ := depElimPropGZ add0LMotiveGZ add0LMotiveProper.

(*
 * Now, we configure Pumpkin Pi to use these eliminators.
 * We never defined iotas for these eliminators, nor do we 
 * need them, so we just keep the olds ones; they will not
 * be used.
 *)

Configure Lift Z GZ {
    constrs_a = depConstrIndIntPos depConstrIndIntNegSuc ;
    constrs_b = depConstrGZPos depConstrGZNegSuc ;
    elim_a = appliedDepElimPropIndInt ;
    elim_b = appliedDepElimPropGZ ;
    eta_a = etaIndInt ;
    eta_b = etaGZ ;
    iota_a = iotaIndIntPos iotaIndIntPosRev iotaIndIntNegSuc iotaIndIntNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

(*
 * We now redefine add0LIndIntZ using only these
 * subterms and appliedDepElimPropGZ Because Pumpkin Pi 
 * already has lifted add0LPosCaseIndInt and add0LNegSucCaseIndInt,
 * it has the results of lifting them cached, and can lift them
 * without seeing the call to depRecIndInt in it.
 * This allows the lifting to go through.
 * Eventually, Pumpkin Pi will support providing multiple eliminators
 * at once, and this process will become unnecessary.
 *)

Theorem add0LIndIntZ' (z : Z) : z = addIndIntZ (depConstrIndIntPos 0) z.
Proof.
  apply appliedDepElimPropIndInt.
  apply add0LPosCaseIndInt.
  apply add0LNegSucCaseIndInt.
Qed.
  
Lift Z GZ in add0LIndIntZ' as add0LGZ.

(*
 * The types of add0LGZ' and add0RGZ' are superficially different from the 
 * types we would get by lifting the types of the theorems in IndInt, 
 * but these types are convertible, which we can see by proving manually lifted
 * theorem statemets by applying add0LGZ' and add0RGZ'.
 *)

Theorem add0RGZ' (z : GZ) : eq_GZ z (addGZ z (depConstrGZPos 0)).
Proof.
  apply add0RGZ.
Qed.

Theorem add0LGZ' (z : GZ) : eq_GZ z (addGZ (depConstrGZPos 0) z).
Proof.
  apply add0LGZ.
Qed.

(*
 * The repaired addition function we have is correct, and comes with many theorems,
 * but it is not especially efficient, because it require computing a canonical
 * element of the equivalence class of its inputs. 
 * Now, we see how we can define a more efficient addition function, and prove
 * that it produces the same output as the lifted addition function.
 * First, we define our fast addition function. Notice that it can directly
 * add the elements of the input pairs. In a setting where we extract this code
 * to another language, addition can be significantly faster than canonicalizing,
 * since addition can be done directly by hardware.
 *)

Definition fastAddGZ (a b : GZ) : GZ :=
  match b with
  | (b1, b2) => match a with
                | (a1, a2) => (a1 + b1, a2 + b2)
                end
  end.

Instance fastAddGZProper : Proper (eq_GZ ==> eq_GZ ==> eq_GZ) fastAddGZ.
Proof.
  unfold eq_GZ.
  intros z1 z2 H1 z3 z4 H2.
  destruct z1.
  destruct z2.
  destruct z3.
  destruct z4.
  simpl.
  lia.
Qed.

(*
 * Next, we prove several theorems to show that 
 * fastAddGZ and addGZ are extensionally equal.
 *)

Theorem reduceSucGZ : forall (n m : nat), eq_GZ (sucGZ (n, m)) (S n, m).
Proof.
  intros.
  pose proof (canonicalizePres (n, m)).
  rewrite <- H.
  pose proof (canonicalizeSignDec (n, m)).
  destruct H0.
  - destruct s.
    rewrite e.
    apply (iotaRecGZPosRev
      GZ
      (fun (n : nat) => depConstrGZPos (S n))
      (fun (n : nat) => nat_rec (constGZ nat) (depConstrGZPos 0) (fun (m : nat) _ => depConstrGZNegSuc m) n)
      x
      (fun s => eq_GZ s (S n, m))).
    simpl.
    f_equal.
    rewrite e in H.
    apply H.
  - destruct s.
    rewrite e.
    apply (iotaRecGZNegSucRev
      GZ
      (fun (n : nat) => depConstrGZPos (S n))
      (fun (n : nat) => nat_rec (constGZ nat) (depConstrGZPos 0) (fun (m : nat) _ => depConstrGZNegSuc m) n)
      x
      (fun s => eq_GZ s (S n, m))).
    destruct x.
    + simpl.
      rewrite e in H.
      unfold eq_GZ in H.
      lia.
    + simpl.
      rewrite e in H.
      unfold eq_GZ in H.
      lia.      
Qed.

Theorem reduceAddZPos : forall (z : GZ) (n : nat), eq_GZ (addGZ z (depConstrGZPos (S n))) (sucGZ (addGZ z (depConstrGZPos n))).
Proof.
  intros.
  unfold addGZ.
  apply (iotaRecGZPosRev
    GZ
    (fun (p : nat) => add_posGZ z p)
    (fun (p : nat) => add_negsucGZ z p)).
  simpl.
  apply (iotaRecGZPos
    GZ
    (fun (p : nat) => add_posGZ z p)
    (fun (p : nat) => add_negsucGZ z p)).
  reflexivity.
Qed.

Theorem reduceFastAddZPos : forall (z : GZ) (n : nat), eq_GZ (fastAddGZ z (depConstrGZPos (S n))) (sucGZ (fastAddGZ z (depConstrGZPos n))).
Proof.
  intros.
  generalize dependent z.
  apply depElimPropGZ.
  - intros z1 z2 H.
    rewrite H.
    reflexivity.
  - intros.
    simpl.
    rewrite (surjective_pairing (sucGZ (n0 + n, 0))).
    pose proof (reduceSucGZ (n0 + n) 0).
    destruct (sucGZ (n0 + n, 0)).
    unfold eq_GZ in H.
    simpl.
    lia.
  - intros.
    simpl.
    rewrite (surjective_pairing (sucGZ (n, S (n0 + 0)))).
    pose proof (reduceSucGZ n (S (n0 + 0))).
    destruct (sucGZ (n, S (n0 + 0))).
    unfold eq_GZ in H.
    simpl.
    lia.
Qed.

Theorem fastAdd0RZ : forall (z : GZ), eq_GZ z (fastAddGZ z (depConstrGZPos 0)).
Proof.
  intros.
  simpl.
  destruct z.
  rewrite PeanoNat.Nat.add_0_r.
  rewrite PeanoNat.Nat.add_0_r.
  reflexivity.
Qed.

Theorem reducePredZ : forall (n m : nat), eq_GZ (predGZ (n, m)) (n, S m).
Proof.
  intros.
  pose proof (canonicalizePres (n, m)).
  rewrite <- H.
  pose proof (canonicalizeSignDec (n, m)).
  destruct H0.
  - destruct s.
    rewrite e.
    apply (iotaRecGZPosRev
      GZ
      (fun (n : nat) => nat_rec (constGZ nat) (depConstrGZNegSuc 0) (fun (m : nat) _ => depConstrGZPos m) n)
      (fun (n : nat) => depConstrGZNegSuc (S n))
      x
      (fun s => eq_GZ s (n, S m))).
    destruct x.
    + simpl.
      rewrite e in H.
      unfold eq_GZ in H.
      lia.
    + simpl.
      rewrite e in H.
      unfold eq_GZ in H.
      lia.    
  - destruct s.
    rewrite e.
    apply (iotaRecGZNegSucRev
      GZ
      (fun (n : nat) => nat_rec (constGZ nat) (depConstrGZNegSuc 0) (fun (m : nat) _ => depConstrGZPos m) n)
      (fun (n : nat) => depConstrGZNegSuc (S n))
      x
      (fun s => eq_GZ s (n, S m))).
    simpl.
    f_equal.
    rewrite e in H.
    apply H.
Qed.          

Theorem reduceFastAddZNegSuc : forall (z : GZ) (n : nat), eq_GZ (fastAddGZ z (depConstrGZNegSuc (S n))) (predGZ (fastAddGZ z (depConstrGZNegSuc n))).
Proof.
  intros.
  generalize dependent z.
  apply depElimPropGZ.
  - intros z1 z2 H.
    rewrite H.
    reflexivity.
  - intros.
    simpl.
    rewrite (surjective_pairing (predGZ (n0 + 0, S n))).
    pose proof (reducePredZ (n0 + 0) (S n)).
    destruct (predGZ (n0 + 0, (S n))).
    unfold eq_GZ in H.
    simpl.
    lia.
  - intros.
    simpl.
    lia.
Qed.

Theorem reduceAddZNegSuc : forall (z : GZ) (n : nat), eq_GZ (addGZ z (depConstrGZNegSuc (S n))) (predGZ (addGZ z (depConstrGZNegSuc n))).
Proof.
  intros.
  unfold addGZ.
  apply (iotaRecGZNegSucRev
    GZ
    (fun (p : nat) => add_posGZ z p)
    (fun (p : nat) => add_negsucGZ z p)).
  simpl.
  apply (iotaRecGZNegSuc
    GZ
    (fun (p : nat) => add_posGZ z p)
    (fun (p : nat) => add_negsucGZ z p)).
  reflexivity.
Qed.

Theorem fastAdd0RZNegSuc : forall (z : GZ), eq_GZ (predGZ z) (fastAddGZ z (depConstrGZNegSuc 0)).
Proof.
  intros.
  simpl.
  destruct z.
  rewrite PeanoNat.Nat.add_0_r.
  rewrite reducePredZ.
  rewrite PeanoNat.Nat.add_1_r.
  reflexivity.
Qed.

Theorem add0RZNegSuc : forall (z : GZ), eq_GZ (predGZ z) (addGZ z (depConstrGZNegSuc 0)).
Proof.
  intros.
  unfold addGZ.
  apply (iotaRecGZNegSucRev
    GZ
    (fun (p : nat) => add_posGZ z p)
    (fun (p : nat) => add_negsucGZ z p)).
  reflexivity.
Qed.

(*
 * Finally, we see that addGZ and fastAddGZ are extensionally equal.
 * This theorem allows us to translate theorems about addGZ
 * into theorems about fastAddGZ, so long as we can unfold definitions
 * to the point where addGZ is being applied to arguments.
 * If we could prove that addGZ = fastAddGZ, that restriction would not
 * apply, and we could just rewrite terms by that equality. 
 * However, we cannot prove that the functions themselves are equal, because
 * we do not assume functional extensionality.
 *)

Theorem addEqualFastAdd : forall (a b : GZ), eq_GZ (addGZ a b) (fastAddGZ a b).
Proof.
  intros a.
  apply depElimPropGZ.
  - intros z1 z2 H. rewrite H. reflexivity.
  - induction n.
    + unfold addGZ.
      rewrite <- add0RGZ.
      rewrite <- fastAdd0RZ.
      reflexivity.
    + rewrite (reduceFastAddZPos a n).
      rewrite (reduceAddZPos a n).
      f_equiv.
      apply IHn.
  - induction n.
    + rewrite <- add0RZNegSuc.
      rewrite <- fastAdd0RZNegSuc.
      reflexivity.
    + rewrite (reduceFastAddZNegSuc a n).
      rewrite (reduceAddZNegSuc a n).
      f_equiv.
      apply IHn.
Qed.

(*
 * Here, we use the above theorem to translate a proof 
 * on addGZ to a proof on fastAddGZ. This proof is
 * easy because we can access all the sites where 
 * fastAddGZ is applied in the theorem, but opaque 
 * definitions could block this in general.
 *)

Theorem fastAdd0LGZ : forall (z : GZ), eq_GZ z (fastAddGZ (depConstrGZPos 0) z).
Proof.
  intros.
  rewrite <- addEqualFastAdd.
  apply add0LGZ.
Qed.
