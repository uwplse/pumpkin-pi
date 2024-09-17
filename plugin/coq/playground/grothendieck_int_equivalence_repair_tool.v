Require Import Relation_Definitions Morphisms Lia.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.
Require Import SetoidClass.

Set DEVOID lift type.

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

Definition depConstrZPos (n : nat) : Z := pos n.
Definition depConstrZNegSuc (n : nat) : Z := negsuc n.

(*
 * Notice that we have two eliminators. The first is not dependently typed,
 * but eliminates into Type, while the second is dependently typed but eliminates
 * into Prop. While we could write a single eliminator for Z, we need
 * two for our repair target GZ, and the eliminators used for both the source
 * and target need their types to match.
 *)

Definition depRecZ (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (z : Z) :
  C :=
  match z with
  | pos n => posP n
  | negsuc n => negSucP n
  end.

Definition depElimPropZ (P : Z -> Prop)
  (posP : forall (n : nat), P (depConstrZPos n))
  (negSucP : forall (n : nat), P (depConstrZNegSuc n))
  (z : Z) :
  P z :=
  match z with
  | pos n => posP n
  | negsuc n => negSucP n
  end.

(* 
 * Below, we define the iota reduction rules. We only define them
 * for depRecZ, as we will not need to iota reduce applications of
 * depElimPropZ.
 *)

Theorem iotaZPos (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  (Q (depRecZ C posP negSucP (depConstrZPos n))) -> Q (posP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaZPosRev (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  Q (posP n) -> (Q (depRecZ C posP negSucP (depConstrZPos n))).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaZNegSuc (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  (Q (depRecZ C posP negSucP (depConstrZNegSuc n))) -> Q (negSucP n).
Proof.
  intros.
  apply X.
Qed.

Theorem iotaZNegSucRev (C : Type)
  (posP : forall (n : nat), C)
  (negSucP : forall (n : nat), C)
  (n : nat) :
  forall (Q : C -> Type),
  Q (negSucP n) -> (Q (depRecZ C posP negSucP (depConstrZNegSuc n))).
Proof.
  intros.
  apply X.
Qed.

(* 
 * We define eta, because the repair tool requires it,
 * but it is not used when transforming these terms,
 * so we just set it to the identity.
 *)

Definition etaZ (z : Z) := z.

(* 
 * Now, we define functions and theorems on this type,
 * explicitly using the constructors, eliminators,
 * and iota reduction rules we defined above,
 * and not the ones Coq generates automatically for the 
 * inductive type. This style of annotation is consistent with
 * prior work.
 *)

Definition constZ (A : Type) (a : A) := Z.

Definition sucZ (z : Z) : Z :=
  depRecZ
    Z
    (fun (n : nat) => depConstrZPos (S n))
    (fun (n : nat) => nat_rec (constZ _) (depConstrZPos 0) (fun (m : nat) _ => depConstrZNegSuc m) n)
    z.

Definition predZ (z : Z) : Z :=
  depRecZ
    Z
    (fun (n : nat) => nat_rec (constZ _) (depConstrZNegSuc 0) (fun (m : nat) _ => depConstrZPos m) n)
    (fun (n : nat) => depConstrZNegSuc (S n))
    z.

Definition add_posZ (z : Z) (n : nat) : Z :=
  nat_rec (constZ _) z (fun _ (p : Z) => sucZ p) n.

Definition add_negsucZ (z : Z) (n : nat) : Z :=
  nat_rec (constZ _) (predZ z) (fun _ (p : Z) => predZ p) n.

Definition addZ (z1 z2 : Z) : Z :=
  depRecZ
    Z
    (fun (p : nat) => add_posZ z1 p)
    (fun (p : nat) => add_negsucZ z1 p)
    z2.

(*
 * Here, we specialize depElimPropZ to use the motive we need for
 * add0LZ. Then, when we go to lift this term, we can supply the 
 * specialized version of the corresponding depElimPropGZ to the
 * repair tool and repair the term.
 *)

Definition add0LZMotive := fun (z1 : Z) => z1 = addZ (depConstrZPos 0) z1.

Definition depElimPropZAdd0LZ := depElimPropZ add0LZMotive.

Theorem add0LZ (z : Z) : z = addZ (depConstrZPos 0) z.
Proof.
  eapply depElimPropZAdd0LZ.
  - induction n.
    + reflexivity.
    + apply (iotaZPos
                Z
                (fun q => depConstrZPos (S q))
                (fun q => nat_rec (constZ _) (depConstrZPos 0) (fun m _ => depConstrZNegSuc m) q)
                n
                (fun s => s = addZ (depConstrZPos 0) (depConstrZPos (S n)))).
      apply (iotaZPosRev
               Z
               (fun q => add_posZ (depConstrZPos 0) q)
               (fun q => add_negsucZ (depConstrZPos 0) q)
               (S n)
               (fun s => depRecZ
                           Z
                           (fun m => depConstrZPos (S m))
                           (fun m => nat_rec
                                       (constZ _)
                                       (depConstrZPos 0)
                                       (fun p _ => depConstrZNegSuc p)
                                       m)
                           (depConstrZPos n) = s)).
      apply (iotaZPos
               Z
               (fun q => add_posZ (depConstrZPos 0) q)
               (fun q => add_negsucZ (depConstrZPos 0) q)
               n
               (fun s => depRecZ
                           Z
                           (fun m => depConstrZPos (S m))
                           (fun m => nat_rec
                                       (constZ _)
                                       (depConstrZPos 0)
                                       (fun p _ => depConstrZNegSuc p)
                                       m)
                           (depConstrZPos n) = sucZ s)).
      apply (@eq_rect_r
                Z
                (addZ (depConstrZPos 0) (depConstrZPos n))
                (fun x => depRecZ _ _ _ x = _)).
      reflexivity.
      apply IHn.
  - induction n.
    + reflexivity.
    + apply (iotaZNegSuc
                Z
                (fun q => nat_rec (constZ _) (depConstrZNegSuc 0) (fun m _ => depConstrZPos m) q)
                (fun q => depConstrZNegSuc (S q))
                n
                (fun s => s = addZ (depConstrZPos 0) (depConstrZNegSuc (S n)))).
      apply (iotaZNegSucRev
               Z
               (fun q => add_posZ (depConstrZPos 0) q)
               (fun q => add_negsucZ (depConstrZPos 0) q)
               (S n)
               (fun s => depRecZ
                           Z
                           (fun m => nat_rec
                                       (constZ _)
                                       (depConstrZNegSuc 0)
                                       (fun p _ => depConstrZPos p)
                                       m)
                           (fun m => depConstrZNegSuc (S m))
                           (depConstrZNegSuc n) = s)).
      apply (iotaZNegSuc
               Z
               (fun q => add_posZ (depConstrZPos 0) q)
               (fun q => add_negsucZ (depConstrZPos 0) q)
               n
               (fun s => depRecZ
                           Z
                           (fun m => nat_rec
                                       (constZ _)
                                       (depConstrZNegSuc 0)
                                       (fun p _ => depConstrZPos p)
                                       m)
                           (fun m => depConstrZNegSuc (S m))
                           (depConstrZNegSuc n) = predZ s)).
      apply (@eq_rect_r
                Z
                (addZ (depConstrZPos 0) (depConstrZNegSuc n))
                (fun x => depRecZ _ _ _ x = _)).
      reflexivity.
      apply IHn.
Qed.

Theorem add0RZ : forall (z : Z), z = (addZ z (depConstrZPos 0)).
  intros.
  unfold addZ.
  apply (iotaZPosRev
    Z
    (fun (p : nat) => add_posZ z p)
    (fun (p : nat) => add_negsucZ z p)
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

Module GZ.

  Definition GZ := (prod nat nat).

End GZ.

Definition GZ := GZ.GZ.

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

(* With those theorems defined, we can define depRecGZ. *)

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

(*
 * We would like to be able to rewrite the function arguments to depRec, 
 * but we can't actually prove functions are equal without some form of 
 * extensionality. Instead, we use Coq's built in notion of a
 * pointwise relation, which says that two functions are related
 * if their outputs at each point are related. This relies on that
 * the posP and negSucP cases for depRec are functions from nat, which 
 * we are using strict equality for and not an equivalence relation.
 * pointwise_relation does not support the case where the domain is a
 * setoid and we wish to require that for related elements of the domain,
 * the output is related. 
 *
 * We have that depRec is proper with respect to the function arguments
 * as a separate instance from our other proof. Some rewrites will fail
 * if only the following instance is present. I don't know the exact reason
 * for this, but my assumption is that the type class search becomes too hard.
 *)

Instance depRecGZProper' (C : Type) (eq_C : C -> C -> Prop)
  `(eq_C_equiv : Equivalence _ (eq_C)) :
  Proper
    (pointwise_relation nat eq_C ==>
       pointwise_relation nat eq_C ==>
       eq_GZ ==>
       eq_C)
    (depRecGZ C).
Proof.
  intros f1 f2 H1 f3 f4 H2 n1 n2 H3.
  rewrite depRecCanonical.
  rewrite (depRecCanonical _ _ _ n2).
  rewrite H3.
  unfold depRecGZ.
  destruct (canonicalizeSignDec (canonicalize n2)).
  - apply H1.
  - apply H2.
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

(* Now, we define our iota reduction rules. *)

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
 * Now, we specify our setoid to the automation. types_b contains a list of
 * the types with specified equivalence relations, rels_b contains the equivalence
 * relations, and equiv_proofs_b contains the proofs that the relations are 
 * instances of Equvialence. They must be provided in the same order; that is,
 * the nth element of types_b, rels_b, and equiv_proofs_b should all correspond to the
 * same type. types_a, rels_a, and equiv_proofs_a are empty because we don't specify 
 * any types in the source to be setoids.
 *)

Save setoid Z GZ { promote = p ; forget = f ; types_a = ; rels_a = ; equiv_proofs_a = ; types_b = GZ ; rels_b = eq_GZ ; equiv_proofs_b = eq_GZ_equiv }.

(*
 * Next, we register the configuration we defined with Pumpkin Pi.
 * We can currently only provide one kind of eliminator at a time to the repair tool,
 * so we need to ensure that the terms we lift only have one kind of eliminator in them.
 * We will see how work around this to lift a term with multiple kinds of eliminators later.
 *)

Configure Lift Z GZ {
    constrs_a = depConstrZPos depConstrZNegSuc ;
    constrs_b = depConstrGZPos depConstrGZNegSuc ;
    elim_a = depRecZ ;
    elim_b = depRecGZ ;
    eta_a = etaZ ;
    eta_b = etaGZ ;
    iota_a = iotaZPos iotaZPosRev iotaZNegSuc iotaZNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

Set DEVOID lift type.

(*
 * We first call lift on the dependent eliminator, which prevents the tool from
 * unfolding the definition of the repaired eliminator. This helds the 
 * setoid automation successfully discover proofs.
 *)

Lift Z GZ in depRecZ as depRecLifted.

(* Now, we begin lifting the functions we defined over Z. *)

Lift Z GZ in constZ as constGZ.

Print constGZ.

Lift Z GZ in sucZ as sucGZ.

Print sucGZ.

Lift Z GZ in predZ as predGZ.

Print predGZ.
  
Lift Z GZ in add_posZ as add_posGZ.

Print add_posGZ.

Lift Z GZ in add_negsucZ as add_negsucGZ.

Print add_negsucGZ.

Lift Z GZ in addZ as addGZ.

Print addGZ.

Lift Z GZ in add0RZ as add0RGZ.

Print add0RGZ.

(* 
 * Now, we will lift add0LZ. This theorem uses depElimPropGZ in its proof. 
 * As such, we cannot immediately repair it. Instead, we need to specialize
 * depElimPropGZ to use the lifted motive for the specialized depElimPropZ
 * we defined earlier, and then provide it with a proof that the repaired motive
 * is proper. In this case, the proper proof is automatically generated by
 * Pumpkin Pi. Then, we reconfigure the tool to use the specialized depElimProps,
 * and can repair add0LZ.
 *
 * A bug in Pumpkin Pi which only surfaces in this case study is causing 
 * repairing calls to eq_rect_r to fail if Configure is called again, even
 * when configuring with the same arguments as to the first call. 
 * To circumvent this bug, we first repair each branch we pass to depElimProp, 
 * then reconfigure with our specialized eliminators. Then, we can repair a version
 * of add0LZ which is defined using these repaired branches. In addition, we need to
 * repair the branches before repairing the motive, or the repair fails.
 *)

Definition add0LPosCaseZ :=
  (fun n : nat =>
   nat_ind
     (fun n0 : nat => add0LZMotive (depConstrZPos n0)) eq_refl
     (fun (n0 : nat)
        (IHn : add0LZMotive (depConstrZPos n0)) =>
      iotaZPos Z (fun q : nat => depConstrZPos (S q))
        (fun q : nat =>
         nat_rec (constZ nat) (depConstrZPos 0)
           (fun (m : nat) (_ : constZ nat m) => depConstrZNegSuc m) q) n0
        (fun s : Z => s = addZ (depConstrZPos 0) (depConstrZPos (S n0)))
        (iotaZPosRev Z (fun q : nat => add_posZ (depConstrZPos 0) q)
           (fun q : nat => add_negsucZ (depConstrZPos 0) q) (S n0)
           (fun s : Z =>
            depRecZ Z (fun m : nat => depConstrZPos (S m))
              (fun m : nat =>
               nat_rec (constZ nat) (depConstrZPos 0)
                 (fun (p : nat) (_ : constZ nat p) => depConstrZNegSuc p) m)
              (depConstrZPos n0) = s)
           (iotaZPos Z (fun q : nat => add_posZ (depConstrZPos 0) q)
              (fun q : nat => add_negsucZ (depConstrZPos 0) q) n0
              (fun s : Z =>
               depRecZ Z (fun m : nat => depConstrZPos (S m))
                 (fun m : nat =>
                  nat_rec (constZ nat) (depConstrZPos 0)
                    (fun (p : nat) (_ : constZ nat p) => depConstrZNegSuc p) m)
                 (depConstrZPos n0) = sucZ s)
              (eq_rect_r
                 (fun x : Z =>
                  depRecZ Z (fun m : nat => depConstrZPos (S m))
                    (fun m : nat =>
                     nat_rec (constZ nat) (depConstrZPos 0)
                       (fun (p : nat) (_ : constZ nat p) => depConstrZNegSuc p) m) x =
                  sucZ
                    (depRecZ Z
                       (fun q : nat => add_posZ (depConstrZPos 0) q)
                       (fun q : nat => add_negsucZ (depConstrZPos 0) q)
                       (depConstrZPos n0))) eq_refl IHn)))) n).

Lift Z GZ in add0LPosCaseZ as add0LPosCaseGZ.

Print add0LPosCaseGZ.

Definition add0LNegSucCaseZ :=
  (fun n : nat =>
   nat_ind (fun n0 : nat => add0LZMotive (depConstrZNegSuc n0)) eq_refl
     (fun (n0 : nat) (IHn : add0LZMotive (depConstrZNegSuc n0)) =>
      iotaZNegSuc Z
        (fun q : nat =>
         nat_rec (constZ nat) (depConstrZNegSuc 0)
           (fun (m : nat) (_ : constZ nat m) => depConstrZPos m) q)
        (fun q : nat => depConstrZNegSuc (S q)) n0
        (fun s : Z => s = addZ (depConstrZPos 0) (depConstrZNegSuc (S n0)))
        (iotaZNegSucRev Z (fun q : nat => add_posZ (depConstrZPos 0) q)
           (fun q : nat => add_negsucZ (depConstrZPos 0) q) (S n0)
           (fun s : Z =>
            depRecZ Z
              (fun m : nat =>
               nat_rec (constZ nat) (depConstrZNegSuc 0)
                 (fun (p : nat) (_ : constZ nat p) => depConstrZPos p) m)
              (fun m : nat => depConstrZNegSuc (S m)) (depConstrZNegSuc n0) = s)
           (iotaZNegSuc Z (fun q : nat => add_posZ (depConstrZPos 0) q)
              (fun q : nat => add_negsucZ (depConstrZPos 0) q) n0
              (fun s : Z =>
               depRecZ Z
                 (fun m : nat =>
                  nat_rec (constZ nat) (depConstrZNegSuc 0)
                    (fun (p : nat) (_ : constZ nat p) => depConstrZPos p) m)
                 (fun m : nat => depConstrZNegSuc (S m)) (depConstrZNegSuc n0) = 
               predZ s)
              (eq_rect_r
                 (fun x : Z =>
                  depRecZ Z
                    (fun m : nat =>
                     nat_rec (constZ nat) (depConstrZNegSuc 0)
                       (fun (p : nat) (_ : constZ nat p) => depConstrZPos p) m)
                    (fun m : nat => depConstrZNegSuc (S m)) x =
                  predZ
                    (depRecZ Z (fun q : nat => add_posZ (depConstrZPos 0) q)
                       (fun q : nat => add_negsucZ (depConstrZPos 0) q) 
                       (depConstrZNegSuc n0))) eq_refl IHn)))) n).

Lift Z GZ in add0LNegSucCaseZ as add0LNegSucCaseGZ.

Print add0LNegSucCaseGZ.

Lift Z GZ in add0LZMotive as add0LGZMotive.

Print add0LGZMotive.

Definition depElimPropGZAdd0LGZ := depElimPropGZ add0LGZMotive add0LGZMotive_proper.

Configure Lift Z GZ {
    constrs_a = depConstrZPos depConstrZNegSuc ;
    constrs_b = depConstrGZPos depConstrGZNegSuc ;
    elim_a = depRecZ depElimPropZAdd0LZ ;
    elim_b = depRecGZ depElimPropGZAdd0LGZ ;
    eta_a = etaZ ;
    eta_b = etaGZ ;
    iota_a = iotaZPos iotaZPosRev iotaZNegSuc iotaZNegSucRev ;
    iota_b = iotaRecGZPos iotaRecGZPosRev iotaRecGZNegSuc iotaRecGZNegSucRev
  }.

Definition add0LZ' (z : Z) : z = addZ (depConstrZPos 0) z := depElimPropZAdd0LZ add0LPosCaseZ add0LNegSucCaseZ z.

Lift Z GZ in add0LZ' as add0LGZ.

Print add0LGZ.

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
    + rewrite <- add0RGZ.
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
  Check add0LGZ.
  apply add0LGZ.
Qed.
