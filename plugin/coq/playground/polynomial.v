(* list, grammar, list of coeff + exp pairs *)
Require Import Nat.
Require Import List.
Import ListNotations.
Require Import UIPList.
Require Import EqdepFacts.
Require Import Eqdep_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Ornaments.
Require Import RelationClasses Morphisms.
Require Import Permutation Sorting Sorted Orders.
Require Import Lia.

Fixpoint removeLeadingZeros (l : list nat) :=
  match l with
  | [] => []
  | h :: t =>
      match eqb h 0 with
      | false => l
      | true => removeLeadingZeros t
      end
  end.

Definition noLeadingZeros (l : list nat) :=
  l = removeLeadingZeros l.

Theorem noLeadingZerosProofIrr : forall (l : list nat) (p1 p2 : noLeadingZeros l),
    p1 = p2.
Proof.
  intros.
  unfold noLeadingZeros in p1, p2.
  Print UIP_.
  enough (UIP_ (list nat)).
  unfold UIP_ in H.
  unfold UIP_on_ in H.
  apply H.
  apply UIP_to_list.
  Print UIP_nat.
  unfold UIP_.
  unfold UIP_on_.
  apply UIP_nat.
Qed.

Definition removeTrailingZeros (l : list nat) :=
  rev (removeLeadingZeros (rev l)).

Definition noTrailingZeros (l : list nat) :=
  l = removeTrailingZeros l.

Theorem noTrailingZerosProofIrr : forall (l : list nat) (p1 p2 : noTrailingZeros l),
    p1 = p2.
Proof.
  intros.
  unfold noTrailingZeros in p1, p2.
  Print UIP_.
  enough (UIP_ (list nat)).
  unfold UIP_ in H.
  unfold UIP_on_ in H.
  apply H.
  apply UIP_to_list.
  Print UIP_nat.
  unfold UIP_.
  unfold UIP_on_.
  apply UIP_nat.
Qed.

Definition CLPoly := {l : list nat | noTrailingZeros l}.

Theorem CLPolyProofIrr : forall (s1 s2 : CLPoly),
    s1 = s2 <-> proj1_sig s1 = proj1_sig s2.
Proof.
  intros.
  split.
  - intros.
    rewrite H.
    reflexivity.
  - intros.
    apply eq_sig_hprop.
    + apply noTrailingZerosProofIrr.
    + apply H.
Qed.

Check CLPoly.

Module CLPoly.

  Definition CLPoly := list nat.

  Definition canonicalize (l : CLPoly) :=
    removeLeadingZeros l.

  Definition eq_CLPoly (l1 l2 : CLPoly) :=
    canonicalize l1 = canonicalize l2.

  Instance eq_CLPoly_refl : Reflexive eq_CLPoly.
  Proof.
    intros x.
    reflexivity.
  Qed.

  Instance eq_CLPoly_sym : Symmetric eq_CLPoly.
  Proof.
    unfold eq_CLPoly.
    intros x y H.
    symmetry.
    apply H.
  Qed.

  Instance eq_CLPoly_trans : Transitive eq_CLPoly.
  Proof.
    unfold eq_CLPoly.
    intros x y z H1 H2.
    rewrite H1.
    apply H2.
  Qed.

  Instance eq_CLPoly_equiv : Equivalence eq_CLPoly.
  Proof.
    split.
    - apply eq_CLPoly_refl.
    - apply eq_CLPoly_sym.
    - apply eq_CLPoly_trans.
  Qed.

  Definition depConstr (l : list nat) (p : noLeadingZeros l) := l.

  Theorem noLeadingZerosCanonical (p : CLPoly) : noLeadingZeros (canonicalize p).
  Proof.
    unfold noLeadingZeros.
    unfold canonicalize.
    induction p.
    reflexivity.
    simpl.
    destruct a; simpl.
    - apply IHp.
    - reflexivity.
  Defined.

  Definition depRec (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (p : CLPoly) : C :=
    X (canonicalize p) (noLeadingZerosCanonical p).

  Instance canonicalIsCanonical : Proper (eq_CLPoly ==> eq) canonicalize.
  Proof.
    intros x1 x2 H.
    unfold canonicalize.
    apply H.
  Qed.

  Import EqNotations.

  Instance depRecProper (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C) :
    Proper (eq_CLPoly ==> eq) (depRec C X).
  Proof.
    intros p1 p2 H.
    apply canonicalIsCanonical in H.
    unfold depRec.
    assert (eq_rect (canonicalize p1) (fun x => noLeadingZeros x) (noLeadingZerosCanonical p1) (canonicalize p2) H = noLeadingZerosCanonical p2).
    apply noLeadingZerosProofIrr.
    destruct H0.
    destruct H.
    reflexivity.
  Qed.

  Theorem canonicalizePres (p : CLPoly) :
    eq_CLPoly p (canonicalize p).
  Proof.
    unfold eq_CLPoly.
    unfold canonicalize.
    apply noLeadingZerosCanonical.
  Qed.

  Theorem depElimProp (P : CLPoly -> Prop)
    `(proper : Proper _ (eq_CLPoly ==> iff) P)
    (X : forall (l : list nat) (proof : noLeadingZeros l), P (depConstr l proof))
    (p : CLPoly) :
    P p.
  Proof.
    rewrite canonicalizePres.
    apply (X (canonicalize p) (noLeadingZerosCanonical p)).
  Qed.

  Theorem alreadyCanonical (l : CLPoly) (proof : noLeadingZeros l) :
    l = canonicalize l.
  Proof.
    apply proof.
  Qed.

  Definition iotaRecEq (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    depRec C X (depConstr l proof) = X l proof.
  Proof.
    unfold depRec.
    unfold depConstr.
    pose proof (alreadyCanonical l proof).
    symmetry in H.
    assert (eq_rect (canonicalize l) (fun x => noLeadingZeros x) (noLeadingZerosCanonical l) (l) H = proof).
    apply noLeadingZerosProofIrr.
    destruct H0.
    pose (match
               H as e in (eq _ y) return
               eq (X (canonicalize l) (noLeadingZerosCanonical l)) (X y (eq_rect (canonicalize l) (fun x : list nat => noLeadingZeros x) (noLeadingZerosCanonical l) y e))
             with
             | eq_refl => eq_refl
           end).
    apply e.
  Qed.

  Definition iotaRec (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    forall (Q : C -> Type),
      (Q (depRec C X (depConstr l proof))) -> Q (X l proof).
  Proof.
    intros.
    rewrite <- iotaRecEq.
    assumption.
  Qed.

  Definition iotaRecRev (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    forall (Q : C -> Type),
      Q (X l proof) -> (Q (depRec C X (depConstr l proof))).
  Proof.
    intros.
    rewrite iotaRecEq.
    assumption.
  Qed.

  Print list_rec.

  Theorem addListsHelp :
    forall (l1 l2 : list nat), list nat.
  Proof.
    intro l1.
    induction l1.
    - intro l2.
      apply l2.
    - intro l2.
      induction l2.
      + apply (a :: l1).
      + apply ((a + a0) :: (IHl1 l2)).
  Defined.

    Theorem noLeadingZerosRemoveLeadingZeros :
    forall (l l1 : list nat),
      0 :: l1 <> removeLeadingZeros l.
  Proof.
    induction l.
    - intros.
      simpl.
      discriminate.
    - intros.
      unfold removeLeadingZeros.
      destruct (PeanoNat.Nat.eqb_spec a 0).
      + simpl.
        apply IHl.
      + intros H.
        inversion H.
        symmetry in H1.
        contradiction.
  Qed.

  Theorem noLeadingZerosHead :
    forall (l : list nat),
      noLeadingZeros l ->
      l = [] \/ exists (l1 : list nat) (n : nat), n <> 0 /\ l = n :: l1.
  Proof.
    destruct l.
    - intros.
      left.
      reflexivity.
    - intros.
      right.
      unfold noLeadingZeros in H.
      destruct n.
      + apply noLeadingZerosRemoveLeadingZeros in H.
        contradiction.
      + exists l.
        exists (S n).
        split.
        intros H1.
        discriminate.
        reflexivity.
  Qed.

  Theorem removeLeadingZerosEnd :
    forall (l l1 : list nat) (n : nat),
      n <> 0 ->
      (removeLeadingZeros l) ++ (n :: l1) = removeLeadingZeros (l ++ (n :: l1)).
  Proof.
    intros.
    induction l.
    - simpl.
      destruct (PeanoNat.Nat.eqb_spec n 0).
      + contradiction.
      + reflexivity.
    - simpl.
      destruct (PeanoNat.Nat.eqb_spec a 0).
      + apply IHl.
      + reflexivity.
  Qed.

  Theorem noLeadingZerosEnd :
    forall (l l1 : list nat) (n : nat),
      n <> 0 ->
      noLeadingZeros l <-> noLeadingZeros (l ++ (n :: l1)).
  Proof.
    intros.
    unfold noLeadingZeros.
    rewrite <- removeLeadingZerosEnd; auto.
    split.
    - intros.
      rewrite <- H0.
      reflexivity.
    - intros.
      apply app_inv_tail in H0.
      apply H0.
  Qed.

  Theorem addListsHelpEqualLength :
    forall (l1 l2 : list nat) (n1 n2 : nat),
      length l1 = length l2 ->
      addListsHelp (l1 ++ [n1]) (l2 ++ [n2]) = addListsHelp l1 l2 ++ [n1 + n2].
  Proof.
    induction l1.
    - intros.
      simpl in H.
      symmetry in H.
      apply length_zero_iff_nil in H.
      rewrite H.
      reflexivity.
    - intros.
      destruct l2.
      + inversion H.
      + simpl in H.
        inversion H.
        simpl.
        f_equal.
        apply IHl1.
        apply H1.
  Qed.

  Theorem addListsHelpFirstLonger :
    forall (l1 l2 : list nat) (n : nat),
      length l2 < S (length l1) ->
      addListsHelp (l1 ++ [n]) l2 = addListsHelp l1 l2 ++ [n].
  Proof.
    induction l1.
    - intros.
      simpl in H.
      unfold lt in H.
      apply Le.le_S_n in H.
      apply Le.le_n_0_eq in H.
      symmetry in H.
      apply length_zero_iff_nil in H.
      rewrite H.
      reflexivity.
    - intros.
      destruct l2.
      + reflexivity.
      + simpl.
        f_equal.
        apply IHl1.
        simpl in H.
        apply Lt.lt_S_n.
        apply H.
  Qed.

  Theorem addListsHelpSecondLonger :
    forall (l1 l2 : list nat) (n : nat),
      length l1 < S (length l2) ->
      addListsHelp l1 (l2 ++ [n]) = addListsHelp l1 l2 ++ [n].
  Proof.
    induction l1.
    - intros.
      reflexivity.
    - intros.
      destruct l2.
      + simpl in H.
        apply Lt.lt_S_n in H.
        apply PeanoNat.Nat.nlt_0_r in H.
        contradiction.
      + simpl.
        f_equal.
        apply IHl1.
        simpl in H.
        apply Lt.lt_S_n.
        apply H.
  Qed.

  (*Theorem noTrailingZerosTail :
    forall (l : list nat) (n : nat),
      noTrailingZeros l ->
      n <> 0 ->
      noTrailingZeros (n :: l).
  Proof.
    induction l.
    - intros.
      unfold noTrailingZeros.
      unfold removeTrailingZeros.
      simpl.
      destruct (PeanoNat.Nat.eqb_spec n 0).
      + contradiction.
      + reflexivity.
    - unfold noTrailingZeros.
      unfold removeTrailingZeros.
      intros.
      simpl.
      simpl in H.*)     

  (*Theorem addListsHelpNoTrailingZeros :
    forall (l1 l2 : list nat),
      noTrailingZeros l1 ->
      noTrailingZeros l2 ->
      noTrailingZeros (addListsHelp l1 l2).
  Proof.
    unfold noTrailingZeros.
    unfold removeTrailingZeros.
    induction l1.
    - intros.
      simpl.
      apply H0.
    - intros.
      induction l2.
      + simpl.
        apply H.
      + simpl.
        unfold noTrailingZeros.
        unfold removeTrailingZeros.
        simpl.*)

  Definition addLists (l1 l2 : list nat) :=
    let l1 := rev l1 in
    let l2 := rev l2 in
    let add_l := addListsHelp l1 l2 in
    rev add_l.

  Theorem addListsEqualLength :
    forall (l1 l2 : list nat) (n1 n2 : nat),
      length l1 = length l2 ->
      addLists (n1 :: l1) (n2 :: l2) = (n1 + n2) :: addLists l1 l2.
    Proof.
      unfold addLists.
      simpl.
      intros.
      rewrite addListsHelpEqualLength.
      rewrite rev_unit.
      reflexivity.
      rewrite rev_length.
      rewrite rev_length.
      apply H.
  Qed.

  Theorem addListsFirstLonger :
    forall (l1 l2 : list nat) (n : nat),
      length l2 < S (length l1) ->
      addLists (n :: l1) l2 = n :: addLists l1 l2.
  Proof.
    unfold addLists.
    intros.
    simpl.
    rewrite addListsHelpFirstLonger.
    rewrite rev_unit.
    reflexivity.
    rewrite rev_length.
    rewrite rev_length.
    apply H.
  Qed.

  Theorem addListsSecondLonger :
    forall (l1 l2 : list nat) (n : nat),
      length l1 < S (length l2) ->
      addLists l1 (n :: l2) = n :: addLists l1 l2.
  Proof.
    unfold addLists.
    intros.
    simpl.
    rewrite addListsHelpSecondLonger.
    rewrite rev_unit.
    reflexivity.
    rewrite rev_length.
    rewrite rev_length.
    apply H.
  Qed.

  Theorem app_end_nonempty (l1 : list nat) (n : nat) :
    exists (l2 : list nat) (m : nat),
      l1 ++ [n] = m :: l2.
  Proof.
    destruct l1.
    - simpl.
      exists [].
      exists n.
      reflexivity.
    - simpl.
      exists (l1 ++ [n]).
      exists n0.
      reflexivity.
  Qed.

  Theorem rev_append_list_end :
    forall (l1 l2 : list nat) (x1 x2 : nat),
      rev l1 ++ [x1] = x2 :: l2 ->
      rev l2 ++ [x2] = x1 :: l1.
  Proof.
    intros.
    apply (f_equal (@rev nat)) in H.
    simpl in H.
    rewrite rev_app_distr in H.
    rewrite rev_involutive in H.
    simpl in H.
    symmetry.
    apply H.
  Qed.

  Theorem addListsFirstEntry :
    forall (l1 l2 : list nat) (n1 n2 : nat),
      addLists (n1 :: l1) (n2 :: l2) = n1 :: addLists l1 (n2 :: l2) \/
      addLists (n1 :: l1) (n2 :: l2) = n2 :: addLists (n1 :: l1) l2 \/
      addLists (n1 :: l1) (n2 :: l2) = (n1 + n2) :: addLists l1 l2.
  Proof.
    intros.
    pose proof (PeanoNat.Nat.lt_trichotomy (length l1) (length l2)).
    destruct H.
    - right.
      left.
      apply addListsSecondLonger.
      apply Lt.lt_n_S in H.
      apply H.
    - destruct H.
      + right.
        right.
        apply addListsEqualLength.
        apply H.
      + left.
        apply addListsFirstLonger.
        apply Lt.lt_n_S in H.
        apply H.
  Qed.

  Theorem addListsFirstEntryWithLength :
    forall (l1 l2 : list nat) (n1 n2 : nat),
      (addLists (n1 :: l1) (n2 :: l2) = n1 :: addLists l1 (n2 :: l2) /\ length l2 < length l1) \/
      (addLists (n1 :: l1) (n2 :: l2) = n2 :: addLists (n1 :: l1) l2 /\ length l1 < length l2) \/
      (addLists (n1 :: l1) (n2 :: l2) = (n1 + n2) :: addLists l1 l2 /\ length l1 = length l2).
  Proof.
    intros.
    pose proof (PeanoNat.Nat.lt_trichotomy (length l1) (length l2)).
    destruct H.
    - right.
      left.
      split.
      apply addListsSecondLonger.
      apply Lt.lt_n_S in H.
      apply H.
      assumption.
    - destruct H.
      + right.
        right.
        split.
        apply addListsEqualLength.
        apply H.
        assumption.
      + left.
        split.
        apply addListsFirstLonger.
        apply Lt.lt_n_S in H.
        apply H.
        assumption.
  Qed.

  Theorem noLeadingZerosHeadNonzero :
    forall (l : list nat) (n : nat),
      n <> 0 <-> noLeadingZeros (n :: l).
  Proof.
    unfold noLeadingZeros.
    simpl.
    split.
    - intros.
      rewrite <- PeanoNat.Nat.eqb_neq in H.
      rewrite H.
      reflexivity.
    - intros.
      intros H0.
      rewrite <- PeanoNat.Nat.eqb_eq in H0.
      rewrite H0 in H.
      assert (forall (l0 l1 : list nat) (n : nat), (n :: l1) ++ l0 <> removeLeadingZeros l0).
      induction l0.
      + intros.
        simpl.
        intros H1.
        inversion H1.
      + intros.
        intros H1.
        simpl in H1.
        destruct (PeanoNat.Nat.eqb_spec a 0).
        * specialize (IHl0 (l1 ++ [a]) n0).
          simpl in IHl0.
          rewrite <- app_assoc in IHl0.
          simpl in IHl0.
          contradiction.
        * inversion H1.
          assert (length (l1 ++ a :: l0) = length l0).
          f_equal.
          apply H4.
          rewrite app_length in H2.
          simpl in H2.
          lia.
      + specialize (H1 l [] n).
        contradiction.
  Qed.

  Theorem noLeadingZerosSameHead :
    forall (l1 l2 : list nat) (n : nat),
      noLeadingZeros (n :: l1) -> noLeadingZeros (n :: l2).
  Proof.
    intros.
    apply noLeadingZerosHead in H.
    destruct H.
    - inversion H.
    - destruct H, H, H.
      apply noLeadingZerosHeadNonzero.
      inversion H0.
      apply H.
  Qed.
      
  Theorem addListsNoLeadingZeros :
    forall (l1 l2 : list nat),
      noLeadingZeros l1 ->
      noLeadingZeros l2 ->
      noLeadingZeros (addLists l1 l2).
  Proof.
    induction l1.
    - intros.
      unfold addLists.
      simpl.
      rewrite rev_involutive.
      apply H0.
    - induction l2.
      + intros.
        unfold addLists.
        simpl.
        pose proof (app_end_nonempty (rev l1) a).
        destruct H1.
        destruct H1.
        rewrite H1.
        simpl.
        apply rev_append_list_end in H1.
        rewrite H1.
        apply H.
      + intros.
        pose proof (addListsFirstEntry l1 l2 a a0).
        destruct H1.
        * rewrite H1.
          apply (noLeadingZerosSameHead l1).
          apply H.
        * destruct H1.
          -- rewrite H1.
             apply (noLeadingZerosSameHead l2).
             apply H0.
          -- rewrite H1.
             apply noLeadingZerosHeadNonzero in H.
             apply noLeadingZerosHeadNonzero.
             lia.
  Qed.
    
  Theorem add (p1 p2 : CLPoly) : CLPoly.
  Proof.
    apply depRec.
    - intros.
      apply depRec.
      + intros.
        apply (depConstr (addLists l l0) (addListsNoLeadingZeros l l0 p p0)).
      + apply p2.
    - apply p1.
  Defined.

  Instance addProper : Proper (eq_CLPoly ==> eq_CLPoly ==> eq_CLPoly) add.
  Proof.
    unfold add.
    intros p1 p2 H0 p3 p4 H1.
    rewrite H0.
    unfold depRec.
    unfold depConstr.
    rewrite H1.
    reflexivity.
  Qed.

  Theorem evalList (l : list nat) (n : nat) : nat.
  Proof.
    induction l.
    - apply 0.
    - apply (a * (pow n (length l)) + IHl).
  Defined.

  Definition evalDepRecArg := (fun n l (proof : noLeadingZeros l) => evalList l n).

  Definition eval (p : CLPoly) (n : nat) :=
    depRec nat (evalDepRecArg n) p.

  Instance evalProper : Proper (eq_CLPoly ==> eq ==> eq) eval.
  Proof.
    unfold eval.
    solve_proper2.
  Qed.

  Theorem addListsFirstEmpty :
    forall (l : list nat),
      addLists [] l = l.
  Proof.
    unfold addLists.
    simpl.
    intros.
    apply rev_involutive.
  Qed.

  Theorem addListsSecondEmpty :
    forall (l : list nat),
      addLists l [] = l.
  Proof.
    induction l.
    - reflexivity.
    - rewrite addListsFirstLonger.
      + rewrite IHl.
        reflexivity.
      + apply PeanoNat.Nat.lt_0_succ.
  Qed.

  Theorem addListsLength :
    forall (l1 l2 : list nat),
      length (addLists l1 l2) = max (length l1) (length l2).
  Proof.
    induction l1.
    - intros.
      rewrite (addListsFirstEmpty l2).
      reflexivity.
    - induction l2.
      + rewrite addListsSecondEmpty.
        reflexivity.
      + pose proof (addListsFirstEntryWithLength l1 l2 a a0).
        destruct H.
        * destruct H.
          rewrite H.
          simpl.
          rewrite IHl1.
          apply Lt.lt_le_S in H0.
          pose proof H0.
          apply max_l in H0.
          simpl.
          rewrite H0.
          apply Le.le_Sn_le in H1.
          apply max_l in H1.
          rewrite H1.
          reflexivity.
        * destruct H, H; rewrite H; simpl.
          -- rewrite IHl2.
             apply Lt.lt_le_S in H0.
             pose proof H0.
             apply max_r in H0.
             apply Le.le_Sn_le in H1.
             apply max_r in H1.
             rewrite H1.
             rewrite <- H0 at 2.
             reflexivity.
          -- rewrite IHl1.
             reflexivity.
  Qed.

  Theorem evalListRespectsAddLists :
    forall (l1 l2 : list nat) (n : nat),
      evalList (addLists l1 l2) n = evalList l1 n + evalList l2 n.
  Proof.
    induction l1.
    - intros.
      rewrite addListsFirstEmpty.
      reflexivity.
    - induction l2.
      + rewrite addListsSecondEmpty.
        intros.
        rewrite PeanoNat.Nat.add_0_r.
        reflexivity.
      + pose proof (addListsFirstEntryWithLength l1 l2 a a0).
        destruct H; destruct H.
        * rewrite H.
          simpl.
          intros.
          rewrite (IHl1 (a0 :: l2) n).
          rewrite addListsLength.
          apply Lt.lt_le_S in H0.
          apply max_l in H0.
          simpl.
          rewrite H0.
          rewrite PeanoNat.Nat.add_assoc.
          reflexivity.
        * destruct H.
          intros n.
          rewrite H.
          simpl.
          rewrite IHl2.
          rewrite addListsLength.
          apply Lt.lt_le_S in H0.
          apply max_r in H0.
          rewrite <- H0 at 2.
          simpl.
          lia.
        * destruct H.
          intros n.
          rewrite H.
          simpl.
          rewrite IHl1.
          rewrite addListsLength.
          rewrite H0.
          rewrite Max.max_idempotent.
          lia.
  Qed.

  Definition evalRespectsAddFirstMotive (p2 : CLPoly) (n : nat) := (fun p => eval (add p p2) n = eval p n + eval p2 n).

  Theorem evalRespectsAddFirstProperGoal : forall (p2 : CLPoly) (n : nat),
      Proper (eq_CLPoly ==> iff) (fun p : CLPoly => eval (add p p2) n = eval p n + eval p2 n).
  Proof.
    intros.
    solve_proper.
  Qed.

  Theorem evalRespectsAddSecondProperGoal : forall (l1 : list nat) (proof1 : noLeadingZeros l1) (n : nat),
      Proper (eq_CLPoly ==> iff)
        (fun p : CLPoly =>
           eval (add (depConstr l1 proof1) p) n
           = eval (depConstr l1 proof1) n + eval p n).
  Proof.
    intros.
    solve_proper.
  Qed.

  Definition evalRespectsAddFirstDepElimProp := (fun (p1 : CLPoly) p2 n => depElimProp (evalRespectsAddFirstMotive p2 n) (evalRespectsAddFirstProperGoal p2 n)).

  Definition evalRespectsAddSecondMotive l1 proof1 n :=
    (fun p : CLPoly =>
           eval (add (depConstr l1 proof1) p) n
           = eval (depConstr l1 proof1) n + eval p n).

  Definition evalRespectsAddSecondDepElimProp := (fun l1 proof1 n => depElimProp (evalRespectsAddSecondMotive l1 proof1 n) (evalRespectsAddSecondProperGoal l1 proof1 n)).
  
  Theorem evalRespectsAdd :
    forall (p1 p2 : CLPoly) (n : nat),
      eval (add p1 p2) n = (eval p1 n) + (eval p2 n).
  Proof.
    intros.
    apply (evalRespectsAddFirstDepElimProp p1).
    - intros l1 proof1.
      apply (evalRespectsAddSecondDepElimProp l1 proof1 n).
      + intros l2 proof2.
        unfold evalRespectsAddSecondMotive.
        unfold add.
        apply iotaRecRev.
        apply iotaRecRev.
        unfold eval.
        apply iotaRecRev.
        apply iotaRecRev.
        apply iotaRecRev.
        apply evalListRespectsAddLists.
  Qed.

  Theorem addListsHelpSecondEmpty :
    forall (l : list nat),
      addListsHelp l [] = l.
  Proof.
    destruct l.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Theorem addListsHelpComm :
    forall (l1 l2 : list nat),
      addListsHelp l1 l2 = addListsHelp l2 l1.
  Proof.
    induction l1.
    - intros.
      rewrite addListsHelpSecondEmpty.
      reflexivity.
    - induction l2.
      + reflexivity.
      + simpl.
        rewrite IHl1.
        rewrite PeanoNat.Nat.add_comm.
        reflexivity.
  Qed.

  Theorem addListsComm :
    forall (l1 l2 : list nat),
      addLists l1 l2 = addLists l2 l1.
  Proof.
    unfold addLists.
    intros.
    rewrite addListsHelpComm.
    reflexivity.
  Qed.

  Theorem addComm :
    forall (p1 p2 : CLPoly),
      eq_CLPoly (add p1 p2) (add p2 p1).
  Proof.
    intros.
    eapply (depElimProp (fun p => eq_CLPoly (add p p2) (add p2 p))).
    - solve_proper.
    - intros.
      eapply (depElimProp (fun p => eq_CLPoly (add _ p) (add p _))).
      + solve_proper.
      + intros.
        unfold add.
        repeat (apply iotaRecRev).
        pose proof (addListsComm l l0).
        assert (eq_rect (addLists l l0) (fun x => noLeadingZeros x) (addListsNoLeadingZeros l l0 proof proof0) (addLists l0 l) H = addListsNoLeadingZeros l0 l proof0 proof).
        apply noLeadingZerosProofIrr.
        destruct H0.
        destruct H.
        simpl.
        reflexivity.
  Qed.

  Theorem addListsHelpAssoc :
    forall (l1 l2 l3 : list nat),
      addListsHelp l1 (addListsHelp l2 l3) = addListsHelp (addListsHelp l1 l2) l3.
  Proof.
    induction l1; destruct l2; destruct l3; try reflexivity.
    simpl.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite IHl1.
    reflexivity.
  Qed.

  Theorem addListsAssoc :
    forall (l1 l2 l3 : list nat),
      addLists l1 (addLists l2 l3) = addLists (addLists l1 l2) l3.
  Proof.
    intros.
    unfold addLists.
    rewrite rev_involutive.
    rewrite rev_involutive.
    rewrite addListsHelpAssoc.
    reflexivity.
  Qed.

  Theorem addAssoc :
    forall (p1 p2 p3 : CLPoly),
      eq_CLPoly (add p1 (add p2 p3)) (add (add p1 p2) p3).
  Proof.
    intros.
    eapply (depElimProp (fun p => eq_CLPoly (add p (add p2 p3)) (add (add p p2) p3))).
    solve_proper.
    intros.
    eapply (depElimProp (fun p => eq_CLPoly (add (depConstr l proof) (add p p3)) (add (add (depConstr l proof) p) p3))).
    solve_proper.
    intros.
    eapply (depElimProp (fun p => eq_CLPoly (add (depConstr l proof) (add (depConstr l0 proof0) p)) (add (add (depConstr l proof) (depConstr l0 proof0)) p))).
    solve_proper.
    intros.
    unfold add.
    repeat (apply iotaRecRev).
    pose proof (addListsAssoc l l0 l1).
    assert
      (eq_rect
         (addLists l (addLists l0 l1))
         (fun x => noLeadingZeros x)
         (addListsNoLeadingZeros l (addLists l0 l1) proof (addListsNoLeadingZeros l0 l1 proof0 proof1))
         (addLists (addLists l l0) l1)
         H
       = addListsNoLeadingZeros (addLists l l0) l1 (addListsNoLeadingZeros l l0 proof proof0) proof1).
    apply noLeadingZerosProofIrr.
    destruct H0.
    destruct H.
    reflexivity.
  Qed.

  Theorem multListByConstant (l : list nat) (n : nat) : CLPoly.
  Proof.
    destruct n.
    - apply [].
    - induction l.
      + apply [].
      + apply (a * (S n) :: IHl).
  Defined.

  Theorem multListByConstantNoLeadingZeros :
    forall (l : list nat) (proof : noLeadingZeros l) (n : nat),
      noLeadingZeros (multListByConstant l n).
  Proof.
    intros l proof n.
    destruct n.
    - intros.
      reflexivity.
    - induction l.
      + intros.
        simpl.
        reflexivity.
      + intros.
        simpl.
        rewrite <- noLeadingZerosHeadNonzero in proof.
        rewrite <- noLeadingZerosHeadNonzero.
        intros H.
        apply PeanoNat.Nat.eq_mul_0 in H.
        destruct H; lia.
  Qed.
      
  Definition multByConstant (p : CLPoly) (n : nat) :=
    depRec CLPoly (fun l proof => depConstr (multListByConstant l n) (multListByConstantNoLeadingZeros l proof n)) p.

  Instance multByConstantProper : Proper (eq_CLPoly ==> eq ==> eq_CLPoly) multByConstant.
  Proof.
    unfold multByConstant.
    solve_proper2.
  Qed.

  Theorem lengthMultListByConstant :
    forall (l : list nat) (n : nat),
      length l = length (multListByConstant l (S n)).
  Proof.
    induction l.
    - intros.
      reflexivity.
    - intros.
      simpl.
      rewrite (IHl n).
      reflexivity.
  Qed.    

  Theorem evalListRespectsMultListByConstant :
    forall (l : list nat) (n1 n2 : nat),
      evalList (multListByConstant l n1) n2 = n1 * evalList l n2.
  Proof.
    destruct n1.
    - simpl.
      intros.
      reflexivity.
    - induction l.
      + intros.
        simpl.
        lia.
      + intros.
        remember (S n1) as m.
        simpl.
        rewrite PeanoNat.Nat.mul_add_distr_l.
        rewrite <- IHl.
        rewrite Heqm.
        simpl.
        f_equal.
        rewrite (lengthMultListByConstant l n1).
        unfold multListByConstant.
        lia.
  Qed.

  Theorem evalRespectsMultByConstant :
    forall (p : CLPoly) (n1 n2 : nat),
      eval (multByConstant p n1) n2 = n1 * eval p n2.
  Proof.
    intros.
    apply (depElimProp (fun x => eval (multByConstant x n1) n2 = n1 * eval x n2)).
    - solve_proper.
    - intros.
      unfold multByConstant.
      apply iotaRecRev.
      unfold eval.
      apply iotaRecRev.
      apply iotaRecRev.
      apply evalListRespectsMultListByConstant.
  Qed.

  Definition multListByXToN (l : list nat) (n : nat) :=
    list_rec (fun _ => list nat) [] (fun a l _ => (a :: l) ++ (repeat 0 n)) l.

  Theorem multListByXToNNoLeadingZeros :
    forall (l : list nat) (proof : noLeadingZeros l) (n : nat),
      noLeadingZeros (multListByXToN l n).
  Proof.
    intros.
    destruct l.
    - reflexivity.
    - simpl.
      apply (noLeadingZerosSameHead l).
      apply proof.
  Qed.

  Theorem evalListApp :
    forall (l1 l2 : list nat) (n : nat),
      evalList (l1 ++ l2) n = pow n (length l2) * evalList l1 n + evalList l2 n.
  Proof.
    induction l1.
    - intros.
      simpl.
      lia.
    - intros.
      simpl.
      rewrite IHl1.
      rewrite app_length.
      rewrite PeanoNat.Nat.pow_add_r.
      lia.
  Qed.

  Theorem evalListZeros :
    forall (n1 n2 : nat),
      evalList (repeat 0 n1) n2 = 0.
  Proof.
    intros.
    induction n1.
    - reflexivity.
    - simpl.
      apply IHn1.
  Qed.

  Theorem evalListRespectsMultListByXToN :
    forall (l : list nat) (n1 n2 : nat),
      evalList (multListByXToN l n1) n2 = (pow n2 n1) * evalList l n2.
  Proof.
    induction l.
    intros.
    - rewrite PeanoNat.Nat.mul_0_r.
      reflexivity.
    - intros.
      simpl.
      rewrite evalListApp.
      rewrite app_length.
      rewrite repeat_length.
      rewrite PeanoNat.Nat.pow_add_r.
      rewrite evalListZeros.
      lia.
  Qed.

  Definition multByXToN (p : CLPoly) (n : nat) :=
    depRec
      CLPoly
      (fun l proof =>
         depConstr
           (multListByXToN l n)
           (multListByXToNNoLeadingZeros l proof n))
      p.

  Instance multByXToNProper : Proper (eq_CLPoly ==> eq ==> eq) multByXToN.
  Proof.
    unfold multByXToN.
    solve_proper2.
  Qed.

  Theorem evalRespectsMultByXToN :
    forall (p : CLPoly) (n1 n2 : nat),
      eval (multByXToN p n1) n2 = (pow n2 n1) * eval p n2.
  Proof.
    intros.
    eapply (depElimProp (fun x => eval (multByXToN x n1) n2 = (pow n2 n1) * eval x n2)).
    - solve_proper.
    - intros.
      unfold multByXToN.
      apply iotaRecRev.
      unfold eval.
      apply iotaRecRev.
      apply iotaRecRev.
      apply evalListRespectsMultListByXToN.
  Qed.

  Theorem multLists :
    forall (l1 l2 : list nat), list nat.
  Proof.
    intros l1.
    induction l1.
    - intros l2.
      apply [].
    - intros l2.
      apply (addLists (IHl1 l2) (multListByXToN (multListByConstant l2 a) (length l1))).
  Defined.

  Theorem multListByXTo0 :
    forall (l : list nat),
      multListByXToN l 0 = l.
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      rewrite app_nil_r.
      reflexivity.
  Qed.

  Theorem multListsSecondEmpty :
    forall (l : list nat),
      multLists l [] = [].
  Proof.
    induction l.
    - reflexivity.
    - destruct a.
      + simpl.
        rewrite IHl.
        reflexivity.
      + simpl.
        rewrite IHl.
        reflexivity.
  Qed.

  (*Theorem multListsComm :
    forall (l1 l2 : list nat),
      removeLeadingZeros (multLists l1 l2) = removeLeadingZeros (multLists l2 l1).
  Proof.
    induction l1.
    - induction l2.
      + reflexivity.
      + destruct a.
        * simpl.
          rewrite multListsSecondEmpty.
          reflexivity.
        * simpl.
          rewrite multListsSecondEmpty.
          reflexivity.
    - induction l2.
      + simpl.
        rewrite multListsSecondEmpty.
        rewrite addListsFirstEmpty.
        destruct a; reflexivity.
      + simpl.
        rewrite <- IHl2.
        rewrite IHl1.
        simpl.
        destruct a, a0.
        * simpl.
          rewrite IHl1.
          reflexivity.
        * simpl.
          rewrite addListsSecondEmpty.
          rewrite addListsSecondEmpty.
          rewrite IHl1.
          f_equal.
          rewrite multListByXTo0.

  Theorem lengthMultLists :
    forall (l1 l2 : list nat) (n1 n2 : nat),
      noLeadingZeros (n1 :: l1) ->
      noLeadingZeros (n2 :: l2) ->
      length (multLists (n1 :: l1) (n2 :: l2)) = length (n1 :: l1) + length (n2 :: l2) - 1.
  Proof.
    induction l1.
    - induction l2.
      + intros.
        apply noLeadingZerosHeadNonzero in H.
        destruct n1.
        * contradiction.
        * reflexivity.
      + intros.
        apply noLeadingZerosHeadNonzero in H.
        destruct n1.
        * contradiction.
        * apply (noLeadingZerosHeadNonzero [] (S n1)) in H.
          apply (noLeadingZerosSameHead (a :: l2) l2 n2) in H0.
          specialize (IHl2 (S n1) n2 H H0). 
          simpl in IHl2.
          rewrite addListsFirstEmpty in IHl2.
          simpl.
          rewrite addListsFirstEmpty.
          rewrite <- IHl2.
          reflexivity.
    - induction l2.
      Focus 2.
      intros.
      simpl.
      + intros.
        destruct n1.
        * apply noLeadingZerosHeadNonzero in H.
          contradiction.
        * simpl.
          destruct a.
          Focus 2.
          simpl.
          -- simpl.
             rewrite addListsSecondEmpty.
             apply (noLeadingZerosSameHead (0 :: l1) l1) in H.
             specialize (IHl1 [] (S n1) n2 H H0).
             simpl in IHl1.
             rewrite PeanoNat.Nat.sub_0_r in IHl1.
             rewrite <- IHl1.
             
        simpl.*)

  Theorem multListByXToNLength :
    forall (l : list nat) (n1 n2 : nat),
      length (multListByXToN (n1 :: l) n2) = length (n1 :: l) + n2.
  Proof.
    destruct l.
    - intros.
      simpl.
      rewrite repeat_length.
      reflexivity.
    - intros.
      simpl.
      rewrite app_length.
      rewrite repeat_length.
      reflexivity.
  Qed.

  Theorem multEmptyListByConstant :
    forall (n : nat),
      multListByConstant [] n = [].
  Proof.
    destruct n; reflexivity.
  Qed.

  (*Theorem multListsLength :
    forall (l1 l2 : list nat),
      length (multLists l1 l2) <= length l1 + length l2 - 1.
  Proof.
    induction l1.
    - intros.
      simpl.
      lia.
    - simpl.
      intros l2.
      destruct l1.
      + simpl.
        rewrite addListsFirstEmpty.
        rewrite multListByXTo0.
        destruct a.
        * simpl.
          apply le_0_n.
        * rewrite <- lengthMultListByConstant.
          rewrite PeanoNat.Nat.sub_0_r.
          reflexivity.
      + assert (length (multLists (n :: l1) l2) <= length (multListByXToN (multListByConstant l2 a) (length (n :: l1)))).
        * apply (PeanoNat.Nat.le_trans _ (length (n :: l1) + length l2 - 1)).
          -- apply IHl1.
          -- destruct l2.
             ++ simpl.
                rewrite multEmptyListByConstant.
                simpl. rewrite multListByXToNLength.

  Theorem multListsNoLeadingZeros :
    forall (l1 l2 : list nat),
      noLeadingZeros l1 ->
      noLeadingZeros l2 ->
      noLeadingZeros (multLists l1 l2).
  Proof.
    induction l1.
    - intros.
      reflexivity.
    - intros.
      simpl.
      apply IHl1.
      + apply noLeadingZerosTail.*)
  
End CLPoly.

Module CEPPoly.

  Definition CEPPoly := list (nat * nat).

  Fixpoint get_max_degree (l: CEPPoly) : nat :=
    match l with
      | [] => 0
      | (coe, exp) :: xs => match coe with
        | 0 => get_max_degree xs
        | _ => max exp (get_max_degree xs)
        end
    end.

  Fixpoint get_combined_nth_degree_coes (l: CEPPoly) (deg : nat) : nat :=
    match l with
      | [] => 0
      | (coe, exp) :: xs =>
      if eqb coe deg then
        coe + get_combined_nth_degree_coes xs deg
      else
        get_combined_nth_degree_coes xs deg
    end.

  Definition get_combined_nth_degree (l: CEPPoly) (deg : nat) : (nat * nat) :=
    let coe : nat := get_combined_nth_degree_coes l deg in
    (coe, deg).

  Fixpoint iter_coes (max_deg : nat) : list nat :=
    match max_deg with
      | 0 => []
      | S new_deg => max_deg :: iter_coes new_deg
    end.

  Fixpoint canonicalize_max (l: CEPPoly) : CEPPoly :=
    let max_deg : nat := get_max_degree l in
    map (get_combined_nth_degree l) (iter_coes (get_max_degree l)).


  Inductive eq_CEPPoly : CEPPoly -> CEPPoly -> Prop :=
  | Sym x y : eq_CEPPoly x y -> eq_CEPPoly y x
  | Trans x y z : eq_CEPPoly x y -> eq_CEPPoly y z -> eq_CEPPoly x z
  | Perm x y : Permutation x y -> eq_CEPPoly x y
  | Add x c1 c2 e : eq_CEPPoly ((c1, e) :: (c2, e) :: x) (((c1 + c2), e) :: x)
  | Append x y p : eq_CEPPoly x y -> eq_CEPPoly (p :: x) (p :: y)
  | Remove x y p : eq_CEPPoly (p :: x) (p :: y) -> eq_CEPPoly x y
  | Remove_Zero x e : eq_CEPPoly ((0, e) :: x) x.

  Instance eq_CEPPoly_refl : Reflexive eq_CEPPoly.
  Proof.
    intros x.
    apply Perm.
    reflexivity.
  Qed.

  Instance eq_CEPPoly_sym : Symmetric eq_CEPPoly.
  Proof.
    unfold Symmetric.
    apply Sym.
  Qed.

  Instance eq_CEPPoly_trans : Transitive eq_CEPPoly.
  Proof.
    unfold Transitive.
    apply Trans.
  Qed.

  Instance eq_CEPPoly_equiv : Equivalence eq_CEPPoly.
  Proof.
    split.
    - apply eq_CEPPoly_refl.
    - apply eq_CEPPoly_sym.
    - apply eq_CEPPoly_trans.
  Qed.

  Fixpoint get_leading_same_exp_help (l : CEPPoly) (exp : nat) : CEPPoly :=
    match l with
    | [] => []
    | (n1, e1) :: t =>
        if eqb e1 exp then
          (n1, e1) :: get_leading_same_exp_help t exp
        else
          get_leading_same_exp_help t exp
    end.

  Fixpoint combine_adjacent_help (l : CEPPoly) (exp : nat) (total : nat) :=
    match l with
    | [] => [(total, exp)]
    | (n1, e1) :: t =>
        if eqb e1 exp then
          combine_adjacent_help t exp (n1 + total)
        else
          (total, exp) :: combine_adjacent_help t e1 n1
    end.

  Definition combine_adjacent (l : CEPPoly) :=
    match l with
    | [] => []
    | (n1, e1) :: t => combine_adjacent_help t e1 n1
    end.

  (*Fixpoint combine_adjacent (l : CEPPoly) : CEPPoly :=
    match l with
    | (c1, e1) :: t1 =>
        match t1 with
        | (c2, e2) :: t2 => 
            match (eqb e1 e2) with
            | false => (c1, e1) :: (combine_adjacent t1)
            | true => (c1 + c2, e1) :: (combine_adjacent t2)
            end
        | [] => (c1, e1) :: []
        end
    | [] => []
    end.*)

  Local Coercion is_true : bool >-> Sortclass.

  Module DegreeOrder <: TotalLeBool.
    Definition t := (prod nat nat).
    Definition leb (p1 p2 : nat * nat) : bool :=
      match p1, p2 with
      | (c1, e1), (c2, e2) => leb e2 e1
      end.
    Theorem leb_total : forall a1 a2,
        (leb a1 a2 = true) \/ (leb a2 a1 = true).
    Proof.
      intros.
      destruct a1, a2.
      simpl.
      pose proof (PeanoNat.Nat.le_ge_cases n2 n0).
      destruct H.
      - left.
        apply PeanoNat.Nat.leb_le.
        apply H.
      - right.
        apply PeanoNat.Nat.leb_le.
        apply H.
    Qed.
    Theorem leb_trans : Transitive leb.
    Proof.
      unfold leb.
      intros p1 p2 p3.
      destruct p1, p2, p3.
      unfold is_true.
      rewrite PeanoNat.Nat.leb_le.
      rewrite PeanoNat.Nat.leb_le.
      rewrite PeanoNat.Nat.leb_le.
      intros.
      rewrite H0.
      apply H.
    Qed.      
  End DegreeOrder.

  Module Import DegreeSort := Sort DegreeOrder.

  Theorem doubleListInduction {A : Type} (P : list A -> Prop) (pnil : P []) (pone : forall (a : A), P [ a ]) (pconscons : forall (a1 a2 : A) (l : list A), P l -> P (a2 :: l) -> P (a1 :: a2 :: l)) :
    forall (l : list A), P l.
  Proof.
    enough (forall (l : list A) (a : A), P l /\ P (a :: l)).
    destruct l.
    assumption.
    destruct (H l a).
    apply H1.
    induction l.
    - intros.
      split.
      assumption.
      apply pone.
    - intros.
      split.
      destruct l.
      apply pone.
      destruct (IHl a).
      apply H0.
      destruct (IHl a).
      apply pconscons; assumption.
  Qed.

  Theorem locally_sorted_tail (p : CEPPoly) (x : nat * nat) :
    LocallySorted DegreeOrder.leb (x :: p) ->
    LocallySorted DegreeOrder.leb p.
  Proof.
    intros.
    inversion H.
    constructor.
    apply H2.
  Qed.

  (*
  Theorem combine_adjacent_help_sorted (p : CEPPoly) :
    LocallySorted DegreeOrder.leb p ->
    forall (exp total : nat),
      LocallySorted DegreeOrder.leb (combine_adjacent_help p exp total).
  Proof.
    induction p.
    - intros.
      simpl.
      constructor.
    - intros.
      simpl.
      destruct a.
      destruct (PeanoNat.Nat.eqb_spec n0 exp).
      + subst.
        apply IHp.
        apply locally_sorted_tail in H.
        apply H.
      +
        inversion H.*)
      
  Theorem combine_adjacent_sorted (p : CEPPoly) :
    LocallySorted DegreeOrder.leb p -> LocallySorted DegreeOrder.leb (combine_adjacent p).
  Proof.
  Admitted.
    (*destruct p.
    - intros.
      constructor.
    - induction p0.
      + intros.
        simpl.
        destruct p.
        constructor.
      + intros.
        simpl.
        destruct p.
        destruct a.
        destruct (PeanoNatunfold combine_adjacent.

    
    induction p using doubleListInduction.
    - intros.
      simpl.
      constructor.
    - intros.
      simpl.
      destruct a.
      constructor.
    - intros.
      simpl.
      destruct a1, a2.
      destruct (PeanoNat.Nat.eqb_spec n0 n2).
      + rewrite <- e in H.
        rewrite <- e in IHp0.
        destruct l.
        * constructor.
        * destruct p.
          inversion H.
          specialize (IHp0 H2).
          simpl in IHp0.
          destruct (PeanoNat.Nat.eqb_spec n0 n4).
          simpl in IHp0.

          
        inversion H.
        specialize (IHp0 H2).
        constructor.
        remember (combine_adjacent l).
        destruct c.
        * constructor.
        * constructor.
          apply IHp.
          inversion H.
          inversion H2.
          -- constructor.
          -- apply H7.
          --
        destruct l.
        * constructor.
        * nstructor.*)
        
  Fixpoint remove_zeros (l : CEPPoly) : CEPPoly :=
    match l with
    | (c1, e1) :: t =>
        if eqb c1 0 then remove_zeros t else (c1, e1) :: remove_zeros t
    | [] => []
    end.

  Theorem remove_zeros_subset (p : CEPPoly) (a : nat * nat) :
    In a (remove_zeros p) -> In a p.
  Proof.
    induction p.
    - intros.
      inversion H.
    - intros.
      simpl in H.
      destruct a0.
      destruct (PeanoNat.Nat.eqb_spec n 0).
      + specialize (IHp H).
        right.
        apply IHp.
      + destruct H.
        * constructor.
          apply H.
        * right.
          apply IHp.
          apply H.
  Qed.

  Theorem remove_zeros_preserve_nonzeros (p : CEPPoly) (n e : nat) :
    In (n, e) p -> n <> 0 -> In (n, e) (remove_zeros p).
  Proof.
  Admitted.

  Theorem leb_head_sorted_list (p : CEPPoly) (a b c : nat * nat) :
    DegreeOrder.leb a b ->
    In c (b :: p) ->
    LocallySorted DegreeOrder.leb (b :: p) ->
    DegreeOrder.leb a c.
  Proof.
    intros.
    rewrite <- Sorted_LocallySorted_iff in H1.
    apply (Sorted_StronglySorted DegreeOrder.leb_trans) in H1.
    inversion H1.
    subst.
    rewrite Forall_forall in H5.
    destruct H0.
    + subst.
      apply H.
    + specialize (H5 c H0).
      apply (DegreeOrder.leb_trans _ b); auto.
  Qed.

  Theorem remove_zeros_sorted (p : CEPPoly) :
    LocallySorted DegreeOrder.leb p -> LocallySorted DegreeOrder.leb (remove_zeros p).
  Proof.
    intros.
    induction p.
    constructor.
    simpl.
    destruct a.
    destruct (PeanoNat.Nat.eqb_spec n 0).
    - apply IHp.
      apply locally_sorted_tail in H.
      apply H.
    - assert (StronglySorted DegreeOrder.leb ((n, n0) :: remove_zeros p)).
      constructor.
      + apply Sorted_StronglySorted.
        apply DegreeOrder.leb_trans.
        apply Sorted_LocallySorted_iff.
        apply IHp.
        apply locally_sorted_tail in H.
        apply H.
      + rewrite Forall_forall.
        intros x H1.
        apply remove_zeros_subset in H1.
        inversion H.
        * subst.
          contradiction.
        * subst.
          apply (leb_head_sorted_list l _ b); auto.
      + rewrite <- Sorted_LocallySorted_iff.
        apply StronglySorted_Sorted.
        apply H0.
  Qed.

  Definition canonicalize (l : CEPPoly) : CEPPoly :=
    remove_zeros (combine_adjacent (sort l)).

  Theorem sort_pres (l : CEPPoly) : eq_CEPPoly l (sort l).
  Proof.
    apply Perm.
    apply (Permuted_sort l).
  Qed.

  Theorem combine_adjacent_pres (l : CEPPoly) : eq_CEPPoly l (combine_adjacent l).
  Proof.
    (*
    enough (forall (l : CEPPoly) (p : nat * nat),
               eq_CEPPoly l (combine_adjacent l) /\ eq_CEPPoly (p :: l) (combine_adjacent (p :: l))).
    destruct (H l (0, 0)).
    apply H0.
    clear l.
    induction l.
    - intros.
      split.
      + reflexivity.
      + simpl.
        destruct p.
        reflexivity.
    - intro p.
      destruct p, a.
      split.
      destruct (IHl (n1, n2)).
      apply H0.
      simpl.
      pose proof (PeanoNat.Nat.eqb_spec n0 n2).
      inversion H.
      * rewrite H1.
        apply (Trans _ ((n + n1, n2) :: l)).
        apply Add.
        apply Append.
        destruct (IHl (n + n1, n2)).
        apply H2.
      * apply Append.
        destruct (IHl (n1, n2)).
        apply H3.*)
  Admitted.

  Theorem remove_zeros_pres (l : CEPPoly) : eq_CEPPoly l (remove_zeros l).
  Proof.
    induction l.
    - simpl.
      reflexivity.
    - simpl.
      destruct a.
      destruct n.
      + simpl.
        apply (Trans _ l).
        * apply Remove_Zero.
        * apply IHl.
      + simpl.
        apply Append.
        apply IHl.
  Qed.

  Theorem canonicalize_pres (l : CEPPoly) : eq_CEPPoly l (canonicalize l).
  Proof.
    unfold canonicalize.
    rewrite <- remove_zeros_pres.
    rewrite <- combine_adjacent_pres.
    rewrite <- sort_pres.
    reflexivity.
  Qed.

  Fixpoint CEPFromCoeffListHelp (l : list nat) (exp : nat) :=
    match l with
    | [] => []
    | h :: t =>
        (h, exp) :: (CEPFromCoeffListHelp t (S exp))
    end.

  Definition CEPFromCoeffList (l : list nat) := CEPFromCoeffListHelp l 0.

  Fixpoint coeff (p : CEPPoly) (exp : nat) :=
    match p with
    | [] => 0
    | (n, e) :: t => (if eqb exp e then n else 0) + (coeff t exp)
    end.

  Theorem coeffs_in_combined_adjacent (p : CEPPoly) :
    forall (exp : nat), (coeff p exp = 0) \/ In (coeff p exp, exp) (combine_adjacent p).
  Proof.
  Admitted.

  Theorem combine_adjacent_no_extra_coeffs (p : CEPPoly) :
    forall (n exp : nat), In (n, exp) (combine_adjacent p) -> coeff p exp = n.
  Proof.
  Admitted.
  
  Theorem coeffsSame (p1 p2 : CEPPoly) (H : eq_CEPPoly p1 p2) :
    forall (exp : nat), coeff p1 exp = coeff p2 exp.
  Proof.
    intros exp.
    induction H.
    - symmetry.
      assumption.
    - rewrite IHeq_CEPPoly1.
      assumption.
    - induction H.
      + reflexivity.
      + simpl.
        destruct x.
        f_equal.
        apply IHPermutation.
      + simpl.
        destruct y.
        destruct x.
        lia.
      + rewrite IHPermutation1.
        assumption.
    - simpl.
      destruct (exp =? e); lia.
    - simpl.
      destruct p.
      f_equal.
      apply IHeq_CEPPoly.
    - simpl in IHeq_CEPPoly.
      destruct p.
      lia.
    - simpl.
      destruct (exp =? e); reflexivity.
  Qed.

  Fixpoint zeros (n : nat) :=
    match n with
    | 0 => []
    | S m => 0 :: (zeros m)
    end.

  Fixpoint coeffListFromCEPHelp (p : CEPPoly) :=
    match p with
    | [] => []
    | h :: t =>
        match h with
          (n1, e1) =>
            match t with
            | [] => n1 :: (zeros e1)
            | h0 :: t0 =>
                match h0 with
                | (n2, e2) => (n1 :: (zeros (e1 - e2))) ++ (coeffListFromCEPHelp t)
                end
            end
        end
    end.
  
  Definition coeffListFromCEP (p : CEPPoly) :=
    coeffListFromCEPHelp (canonicalize p).
    
  Theorem canonicalizeNoZeroCoeffs (p : CEPPoly) (n e : nat) :
    In (n, e) (remove_zeros p) -> n <> 0.
  Proof.
    induction p.
    - intros.
      contradiction.
    - simpl.
      destruct a.
      destruct n0; simpl.
      + apply IHp.
      + intro H.
        destruct H.
        * apply (f_equal fst) in H.
          simpl in H.
          rewrite <- H.
          intros H0.
          inversion H0.
        * apply (IHp H).
  Qed.      

  Theorem coeffListFromCEPNoLeadingZeros (p : CEPPoly) :
    noLeadingZeros (coeffListFromCEP p).
  Proof.
    unfold coeffListFromCEP.
    unfold canonicalize.
    pose proof (canonicalizeNoZeroCoeffs (combine_adjacent (sort p))).
    induction (remove_zeros (combine_adjacent (sort p))).
    - unfold noLeadingZeros.
      reflexivity.
    - simpl.
      destruct a.
      destruct c.
      + unfold noLeadingZeros.
        simpl.
        specialize (H n n0).
        simpl in H.
        assert (n <> 0).
        apply H.
        left.
        reflexivity.
        rewrite <- PeanoNat.Nat.eqb_neq in H0.
        rewrite H0.
        reflexivity.
      + destruct p0.
        specialize (H n n0).
        assert (n <> 0).
        apply H.
        left.
        reflexivity.
        simpl.
        rewrite <- PeanoNat.Nat.eqb_neq in H0.
        unfold noLeadingZeros.
        unfold removeLeadingZeros.
        rewrite H0.
        reflexivity.
  Defined.

  Definition depConstr (l : list nat) (p : noLeadingZeros l) := CEPFromCoeffList l.

  Print sigT_rect.

  Definition depRec (C : Type) (X : forall (l : list nat) (p : noLeadingZeros l), C) (p : CEPPoly) : C :=
    X (coeffListFromCEP p) (coeffListFromCEPNoLeadingZeros p).

  Theorem canonicalizePermutationProper : Proper (eq_CEPPoly ==> (@Permutation (prod nat nat))) canonicalize.
  Proof.
  Admitted.

  Theorem canonicalizeSorted (p : CEPPoly) : LocallySorted DegreeOrder.leb (canonicalize p).
  Proof.
  Admitted.

  Inductive NoDupExp : CEPPoly -> Prop :=
  | NoDupExp_nil : NoDupExp []
  | NoDupExp_cons :
    forall p exp,
      (forall c, ~ In (c, exp) p) ->
      NoDupExp p ->
      forall c, NoDupExp ((c, exp) :: p).

  Theorem canonicalizeNoDupExp (p : CEPPoly) :
    NoDupExp (canonicalize p).
  Proof.
  Admitted.

  Theorem CEPPolyIdentical :
    forall (p1 p2 : CEPPoly),
      Permutation p1 p2 ->
      LocallySorted DegreeOrder.leb p1 ->
      LocallySorted DegreeOrder.leb p2 ->
      NoDupExp p1 ->
      NoDupExp p2 ->
      p1 = p2.
  Proof.
    induction p1.
    intros.
    apply Permutation_nil in H.
    symmetry.
    apply H.
    intros.
    destruct p2.
    symmetry in H.
    apply Permutation_nil in H.
    apply H.
    enough (a = p).
    subst.
    f_equal.
    apply IHp1.
    - apply Permutation_cons_inv in H.
      apply H.
    - apply locally_sorted_tail in H0.
      apply H0.
    - apply locally_sorted_tail in H1.
      apply H1.
    - inversion H2.
      apply H7.
    - inversion H3.
      apply H7.
    - destruct a, p.
      inversion H2.
      inversion H3.
      subst.
      assert (In (n, n0) ((n1, n2) :: p2)).
      apply (@Permutation_in (prod nat nat) ((n, n0) :: p1) ((n1, n2) :: p2)).
      assumption.
      left.
      reflexivity.
      destruct H4.
      symmetry.
      apply H4.
      rewrite <- Sorted_LocallySorted_iff in H1.
      apply (Sorted_extends DegreeOrder.leb_trans) in H1.
      rewrite Forall_forall in H1.
      pose proof H4 as H5.
      apply H1 in H4.
      unfold DegreeOrder.leb in H4.
      unfold is_true in H4.
      rewrite PeanoNat.Nat.leb_le in H4.
      assert (In (n1, n2) ((n, n0) :: p1)).
      symmetry in H.
      apply (@Permutation_in (prod nat nat) ((n1, n2) :: p2) ((n, n0) :: p1)).
      assumption.
      left.
      reflexivity.
      destruct H7.
      apply H7.
      rewrite <- Sorted_LocallySorted_iff in H0.
      apply (Sorted_extends DegreeOrder.leb_trans) in H0.
      rewrite Forall_forall in H0.
      pose proof H7 as H9.
      apply H0 in H7.
      unfold DegreeOrder.leb in H7.
      unfold is_true in H7.
      rewrite PeanoNat.Nat.leb_le in H7.
      apply (PeanoNat.Nat.le_antisymm n0 n2 H4) in H7.
      subst.
      specialize (H6 n1).
      contradiction.
  Admitted.

  Theorem eq_CEPPoly_respects_max_degree p q k:
    eq_CEPPoly p q -> forall n, n <= k -> n = get_max_degree p -> get_max_degree p = (get_max_degree q).
  Proof.
    intro.
    induction k.
    - intros. destruct n.
      * give_up.
      * give_up.
    - intros. destruct p.
      * pose proof H1 as H1'. simpl in H1.
        rewrite H1 in H0. rewrite H1 in H1'.
        assert (0 <= k). lia.
        apply (IHk 0 H2 H1').
      * assert (n <= k). give_up.
        apply (IHk n H2).
        exact H1.
  Admitted.

  Theorem eqb_refl n : n =? n = true.
  Proof.
    intros.
    induction n.
    * auto.
    * simpl. apply IHn.
  Qed.

  Instance canonicalIsCanonical' : Proper (eq_CEPPoly ==> eq) canonicalize_max.
  Proof.
    intros p1 p2 H.
    apply CEPPolyIdentical.
    induction p1.
    * destruct p2.
      - auto.
      - destruct p. destruct n.
        ** simpl. give_up.
        ** pose proof (coeffsSame [] ((S n, n0) :: p2) H n0).
           simpl in H0.
           rewrite eqb_refl in H0.
           discriminate.
    * induction p2.
      - destruct a. destruct n.
        assert (eq_CEPPoly p1 ((0, n0) :: p1)).
        apply Sym. apply Remove_Zero.
        Print Trans.
  Admitted.

  Instance canonicalIsCanonical : Proper (eq_CEPPoly ==> eq) canonicalize.
  Proof.
    intros p1 p2 H.
    apply CEPPolyIdentical.
    apply (canonicalizePermutationProper _ _ H).
    apply canonicalizeSorted.
    apply canonicalizeSorted.
    apply canonicalizeNoDupExp.
    apply canonicalizeNoDupExp.
  Qed.

  Instance coeffListFromCEPProper : Proper (eq_CEPPoly ==> eq) coeffListFromCEP.
  Proof.
    unfold coeffListFromCEP.
    solve_proper.
  Qed.

  Import EqNotations.

  Instance depRecProper (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C) :
    Proper (eq_CEPPoly ==> eq) (depRec C X).
  Proof.
    intros p1 p2 H.
    apply canonicalIsCanonical in H.
    unfold depRec.    
    unfold coeffListFromCEP.
    assert (eq_rect (canonicalize p1) (fun x => noLeadingZeros (coeffListFromCEPHelp x)) (coeffListFromCEPNoLeadingZeros p1) (canonicalize p2) H = coeffListFromCEPNoLeadingZeros p2).
    apply noLeadingZerosProofIrr.
    destruct H0.
    destruct H.
    reflexivity.
  Qed.

  Theorem coeffListCanonical (l : list nat) (proof : noLeadingZeros l) :
    coeffListFromCEPHelp (canonicalize (depConstr l proof)) = l.
  Proof.
    unfold depConstr.
    unfold CEPFromCoeffList.
  Admitted.

  Theorem CEPFromCoeffListInv (p : CEPPoly) :
    eq_CEPPoly (CEPFromCoeffList (coeffListFromCEP p)) p.
  Proof.
  Admitted.

  Theorem depElimProp (P : CEPPoly -> Prop)
    `(proper : Proper _ (eq_CEPPoly ==> iff) P)
    (X : forall (l : list nat) (proof : noLeadingZeros l), P (depConstr l proof))
    (p : CEPPoly) :
    P p.
  Proof.
    rewrite <- CEPFromCoeffListInv.
    apply (X (coeffListFromCEP p) (coeffListFromCEPNoLeadingZeros p)).
  Qed.

  Definition iotaRecEq (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    depRec C X (depConstr l proof) = X l proof.
  Proof.
    unfold depRec.
    unfold coeffListFromCEP.
    pose proof (coeffListCanonical l proof).
    assert (eq_rect (coeffListFromCEPHelp (canonicalize (depConstr l proof))) noLeadingZeros (coeffListFromCEPNoLeadingZeros (depConstr l proof)) l H = proof).
    apply noLeadingZerosProofIrr.
    rewrite <- H0 at 3.
    rewrite <- H.
    reflexivity.
  Qed.

  Definition iotaRec (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    forall (Q : C -> Type),
      (Q (depRec C X (depConstr l proof))) -> Q (X l proof).
  Proof.
    intros.
    rewrite <- iotaRecEq.
    assumption.
  Qed.

  Definition iotaRecRev (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    forall (Q : C -> Type),
      Q (X l proof) -> (Q (depRec C X (depConstr l proof))).
  Proof.
    intros.
    rewrite iotaRecEq.
    assumption.
  Qed.
  
End CEPPoly.

Module GPoly.
  
  Inductive GPoly : Set :=
  | Const : nat -> GPoly
  | x : GPoly
  | Add : GPoly -> GPoly -> GPoly
  | Mult : GPoly -> GPoly -> GPoly.

  (* eq rel idea suggested for a more general case here:
     https://www.andrew.cmu.edu/user/avigad/meetings/fomm2020/slides/fomm_simmons.pdf
   *)
  Inductive eq_GPoly : GPoly -> GPoly -> Prop :=
  | Refl x : eq_GPoly x x
  | Sym x y : eq_GPoly x y -> eq_GPoly y x
  | Trans x y z : eq_GPoly x y -> eq_GPoly y z -> eq_GPoly x z
  | Add_Assoc x y z : eq_GPoly (Add x (Add y z)) (Add (Add x y) z)
  | Add_Comm x y : eq_GPoly (Add x y) (Add y x)
  | Add_Consts n1 n2 : eq_GPoly (Add (Const n1) (Const n2)) (Const (n1 + n2))
  | Mult_Assoc x y z : eq_GPoly (Mult x (Mult y z)) (Mult (Mult x y) z)
  | Mult_Comm x y : eq_GPoly (Mult x y) (Mult y x)
  | Mult_Dist x y z : eq_GPoly (Mult x (Add y z)) (Add (Mult x y) (Mult x z))
  | Mult_Consts n1 n2 : eq_GPoly (Mult (Const n1) (Const n2)) (Const (n1 * n2))
  | Add_Id x : eq_GPoly (Add (Const 0) x) x
  | Mult_Id x : eq_GPoly (Mult (Const 1) x) x
  | Mult_Annihilator x : eq_GPoly (Mult (Const 0) x) (Const 0). 

  Instance eq_GPoly_refl : Reflexive eq_GPoly.
  Proof.
    unfold Reflexive.
    apply Refl.
  Qed.

  Instance eq_GPoly_sym : Symmetric eq_GPoly.
  Proof.
    unfold Symmetric.
    apply Sym.
  Qed.

  Instance eq_GPoly_trans : Transitive eq_GPoly.
  Proof.
    unfold Transitive.
    apply Trans.
  Qed.

  Instance eq_GPoly_equiv : Equivalence eq_GPoly.
  Proof.
    split.
    - apply eq_GPoly_refl.
    - apply eq_GPoly_sym.
    - apply eq_GPoly_trans.
  Qed.

End GPoly.

Definition p (p : CLPoly.CLPoly) := CLPoly.depRec CEPPoly.CEPPoly (fun l proof => CEPPoly.CEPFromCoeffList l) p.

Definition f (p : CEPPoly.CEPPoly) := CEPPoly.depRec CLPoly.CLPoly (fun l proof => CLPoly.depConstr (CEPPoly.coeffListFromCEP p) (CEPPoly.coeffListFromCEPNoLeadingZeros p)) p.

Save setoid CLPoly.CLPoly CEPPoly.CEPPoly { promote = p ; forget = f ; types_a = CLPoly.CLPoly; rels_a = CLPoly.eq_CLPoly; equiv_proofs_a = CLPoly.eq_CLPoly_equiv; types_b = CEPPoly.CEPPoly ; rels_b = CEPPoly.eq_CEPPoly ; equiv_proofs_b = CEPPoly.eq_CEPPoly_equiv }.

Definition etaCLPoly (x : CLPoly.CLPoly) := x.
Definition etaCEPPoly (x : CEPPoly.CEPPoly) := x.

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {
    constrs_a = CLPoly.depConstr ;
    constrs_b = CEPPoly.depConstr ;
    elim_a = CLPoly.depRec ;
    elim_b = CEPPoly.depRec ;
    eta_a = etaCLPoly ;
    eta_b = etaCEPPoly ;
    iota_a = CLPoly.iotaRec CLPoly.iotaRecRev ;
    iota_b = CEPPoly.iotaRec CEPPoly.iotaRecRev
  }.

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {opaque noLeadingZeros CLPoly.addLists CLPoly.addListsNoLeadingZeros noLeadingZerosProofIrr CLPoly.evalList CLPoly.evalDepRecArg CLPoly.evalListRespectsAddLists}.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.addLists as addListsCEP.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.add as addCEP.

Print CLPoly.add.
Print addCEP.

Instance addCEPProper : Proper (CEPPoly.eq_CEPPoly ==> CEPPoly.eq_CEPPoly ==> CEPPoly.eq_CEPPoly) addCEP.
Proof.
  unfold addCEP.
  intros p1 p2 H0 p3 p4 H1.
  unfold CEPPoly.depConstr.
  unfold CEPPoly.coeffListFromCEP.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.addComm as addCommCEP.

Print addCommCEP.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.eval as evalCEP.

Instance evalCEPProper : Proper (CEPPoly.eq_CEPPoly ==> eq ==> eq) evalCEP.
Proof.
  unfold evalCEP.
  unfold CLPoly.evalDepRecArg.
  solve_proper.
Qed.

Print evalCEP.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.evalRespectsAddFirstMotive as evalRespectsAddFirstMotiveCEP.

Print evalRespectsAddFirstMotiveCEP.

Theorem evalRespectsAddFirstCEPProperGoal (p2 : CEPPoly.CEPPoly) (n : nat) :
  Proper (CEPPoly.eq_CEPPoly ==> iff) (evalRespectsAddFirstMotiveCEP p2 n).
Proof.
  unfold evalRespectsAddFirstMotiveCEP.
  solve_proper2.
Qed.

Definition evalRespectsAddSecondMotiveCEP l1 proof1 n :=
    (fun p : CEPPoly.CEPPoly =>
       evalCEP (addCEP (CEPPoly.depConstr l1 proof1) p) n
       = evalCEP (CEPPoly.depConstr l1 proof1) n + evalCEP p n).

Theorem evalRespectsAddSecondMotiveCEPProper l1 proof1 n : Proper (CEPPoly.eq_CEPPoly ==> iff) (evalRespectsAddSecondMotiveCEP l1 proof1 n).
Proof.
  intros.
  unfold evalRespectsAddSecondMotiveCEP.
  solve_proper.
Qed.

Definition evalRespectsAddFirstDepElimPropCEP := (fun (p1 : CEPPoly.CEPPoly) p2 n => CEPPoly.depElimProp (evalRespectsAddFirstMotiveCEP p2 n) (evalRespectsAddFirstCEPProperGoal p2 n)).

Definition evalRespectsAddSecondDepElimPropCEP := (fun l1 proof1 n => CEPPoly.depElimProp (evalRespectsAddSecondMotiveCEP l1 proof1 n) (evalRespectsAddSecondMotiveCEPProper l1 proof1 n)).

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {
    constrs_a = CLPoly.depConstr ;
    constrs_b = CEPPoly.depConstr ;
    elim_a = CLPoly.depRec CLPoly.evalRespectsAddFirstDepElimProp CLPoly.evalRespectsAddSecondDepElimProp ;
    elim_b = CEPPoly.depRec evalRespectsAddFirstDepElimPropCEP evalRespectsAddSecondDepElimPropCEP ;
    eta_a = etaCLPoly ;
    eta_b = etaCEPPoly ;
    iota_a = CLPoly.iotaRec CLPoly.iotaRecRev ;
    iota_b = CEPPoly.iotaRec CEPPoly.iotaRecRev
  }.

Print CLPoly.evalRespectsAdd.

Print CLPoly.add.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.evalRespectsAdd as evalRespectsAddCEP.

Print evalRespectsAddCEP.

Print CLPoly.evalRespectsAdd.

(*Definition test := fun (l1 : list nat) (proof1 : noLeadingZeros l1) (l2 : list nat) (proof2 : noLeadingZeros l2) (n : nat) =>
      CLPoly.iotaRecRev CLPoly.CLPoly
        (fun (l : list nat) (p : noLeadingZeros l) =>
         CLPoly.depRec CLPoly.CLPoly
           (fun (l0 : list nat) (p0 : noLeadingZeros l0) =>
            CLPoly.depConstr (CLPoly.addLists l l0) (CLPoly.addListsNoLeadingZeros l l0 p p0))
           (CLPoly.depConstr l2 proof2)) l1 proof1
        (fun c : CLPoly.CLPoly =>
         CLPoly.eval c n =
         CLPoly.eval (CLPoly.depConstr l1 proof1) n + CLPoly.eval (CLPoly.depConstr l2 proof2) n)
        (CLPoly.iotaRecRev CLPoly.CLPoly
           (fun (l0 : list nat) (p0 : noLeadingZeros l0) =>
            CLPoly.depConstr (CLPoly.addLists l1 l0) (CLPoly.addListsNoLeadingZeros l1 l0 proof1 p0))
           l2 proof2
           (fun c : CLPoly.CLPoly =>
            CLPoly.eval c n =
            CLPoly.eval (CLPoly.depConstr l1 proof1) n + CLPoly.eval (CLPoly.depConstr l2 proof2) n)
           (CLPoly.iotaRecRev nat (fun (l : list nat) (_ : noLeadingZeros l) => CLPoly.evalList l n)
              (CLPoly.addLists l1 l2) (CLPoly.addListsNoLeadingZeros l1 l2 proof1 proof2)
              (fun n0 : nat =>
               n0 =
               CLPoly.depRec nat (fun (l : list nat) (_ : noLeadingZeros l) => CLPoly.evalList l n)
                 (CLPoly.depConstr l1 proof1) +
               CLPoly.depRec nat (fun (l : list nat) (_ : noLeadingZeros l) => CLPoly.evalList l n)
                 (CLPoly.depConstr l2 proof2))
              (CLPoly.iotaRecRev nat
                 (fun (l : list nat) (_ : noLeadingZeros l) => CLPoly.evalList l n) l1 proof1
                 (fun n0 : nat =>
                  CLPoly.evalList (CLPoly.addLists l1 l2) n =
                  n0 +
                  CLPoly.depRec nat
                    (fun (l : list nat) (_ : noLeadingZeros l) => CLPoly.evalList l n)
                    (CLPoly.depConstr l2 proof2))
                 (CLPoly.iotaRecRev nat
                    (fun (l : list nat) (_ : noLeadingZeros l) => CLPoly.evalList l n) l2 proof2
                    (fun n0 : nat =>
                     CLPoly.evalList (CLPoly.addLists l1 l2) n = CLPoly.evalList l1 n + n0)
                    (CLPoly.evalListRespectsAddLists l1 l2 n))))).*)

Definition test := fun l : list nat => 0.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in test as test_out.

Print test_out.

Print evalRespectsAddCEP.
