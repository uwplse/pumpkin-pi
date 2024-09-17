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
Require Import Wellfounded.

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

Definition opaque_list := list nat.

Module ListFns.

  Theorem noLeadingZerosHeadNonzero :
    forall (l : opaque_list) (n : nat),
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
      assert (forall (l0 l1 : opaque_list) (n : nat), (n :: l1) ++ l0 <> removeLeadingZeros l0).
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

  Theorem noLeadingZerosRemoveLeadingZeros :
    forall (l : opaque_list),
      noLeadingZeros (removeLeadingZeros l).
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      destruct (PeanoNat.Nat.eqb_spec a 0).
      + apply IHl.
      + apply noLeadingZerosHeadNonzero.
        apply n.
  Qed.

  Theorem addListsHelp :
    forall (l1 l2 : opaque_list), opaque_list.
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

  Theorem removeLeadingZerosHeadNotZero :
    forall (l l1 : opaque_list),
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
    forall (l : opaque_list),
      noLeadingZeros l ->
      l = [] \/ exists (l1 : opaque_list) (n : nat), n <> 0 /\ l = n :: l1.
  Proof.
    destruct l.
    - intros.
      left.
      reflexivity.
    - intros.
      right.
      unfold noLeadingZeros in H.
      destruct n.
      + apply removeLeadingZerosHeadNotZero in H.
        contradiction.
      + exists l.
        exists (S n).
        split.
        intros H1.
        discriminate.
        reflexivity.
  Qed.

  Theorem removeLeadingZerosEnd :
    forall (l l1 : opaque_list) (n : nat),
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
    forall (l l1 : opaque_list) (n : nat),
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
    forall (l1 l2 : opaque_list) (n1 n2 : nat),
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
    forall (l1 l2 : opaque_list) (n : nat),
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
    forall (l1 l2 : opaque_list) (n : nat),
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

  Definition addLists (l1 l2 : opaque_list) : opaque_list :=
    let l1 := rev l1 in
    let l2 := rev l2 in
    let add_l := addListsHelp l1 l2 in
    rev add_l.

  Theorem addListsEqualLength :
    forall (l1 l2 : opaque_list) (n1 n2 : nat),
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
    forall (l1 l2 : opaque_list) (n : nat),
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
    forall (l1 l2 : opaque_list) (n : nat),
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

  Theorem app_end_nonempty (l1 : opaque_list) (n : nat) :
    exists (l2 : opaque_list) (m : nat),
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
    forall (l1 l2 : opaque_list) (x1 x2 : nat),
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
    forall (l1 l2 : opaque_list) (n1 n2 : nat),
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
    forall (l1 l2 : opaque_list) (n1 n2 : nat),
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

  Theorem noLeadingZerosSameHead :
    forall (l1 l2 : opaque_list) (n : nat),
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
    forall (l1 l2 : opaque_list),
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

  Theorem evalList (l : opaque_list) (n : nat) : nat.
  Proof.
    induction l.
    - apply 0.
    - apply (a * (pow n (length l)) + IHl).
  Defined.

    Theorem addListsFirstEmpty :
    forall (l : opaque_list),
      addLists [] l = l.
  Proof.
    unfold addLists.
    simpl.
    intros.
    apply rev_involutive.
  Qed.

  Theorem addListsSecondEmpty :
    forall (l : opaque_list),
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
    forall (l1 l2 : opaque_list),
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
    forall (l1 l2 : opaque_list) (n : nat),
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

    Theorem addListsHelpSecondEmpty :
    forall (l : opaque_list),
      addListsHelp l [] = l.
  Proof.
    destruct l.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Theorem addListsHelpComm :
    forall (l1 l2 : opaque_list),
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
    forall (l1 l2 : opaque_list),
      addLists l1 l2 = addLists l2 l1.
  Proof.
    unfold addLists.
    intros.
    rewrite addListsHelpComm.
    reflexivity.
  Qed.

  Theorem addListsCommNoLeadingZerosProofIrr (l l0 : opaque_list) (proof : noLeadingZeros l) (proof0 : noLeadingZeros l0) :
    eq_rect (addLists l l0) (fun x => noLeadingZeros x) (addListsNoLeadingZeros l l0 proof proof0) (addLists l0 l) (addListsComm l l0) = addListsNoLeadingZeros l0 l proof0 proof.
  Proof.
    apply noLeadingZerosProofIrr.
  Qed.

  Theorem addListsHelpAssoc :
    forall (l1 l2 l3 : opaque_list),
      addListsHelp l1 (addListsHelp l2 l3) = addListsHelp (addListsHelp l1 l2) l3.
  Proof.
    induction l1; destruct l2; destruct l3; try reflexivity.
    simpl.
    rewrite PeanoNat.Nat.add_assoc.
    rewrite IHl1.
    reflexivity.
  Qed.

  Theorem addListsAssoc :
    forall (l1 l2 l3 : opaque_list),
      addLists l1 (addLists l2 l3) = addLists (addLists l1 l2) l3.
  Proof.
    intros.
    unfold addLists.
    rewrite rev_involutive.
    rewrite rev_involutive.
    rewrite addListsHelpAssoc.
    reflexivity.
  Qed.
  
End ListFns.



Module CLPoly.

  Definition CLPoly := list nat.

  Definition eq_CLPoly (l1 l2 : CLPoly) :=
    removeLeadingZeros l1 = removeLeadingZeros l2.

  Definition canonicalize (l : CLPoly) :=
    removeLeadingZeros l.

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

  Definition depConstr (l : opaque_list) (p : noLeadingZeros l) : CLPoly := l.

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
    (X : forall (l : opaque_list) (p : noLeadingZeros l), C)
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
    (X : forall (l : opaque_list) (p : noLeadingZeros l), C) :
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
    (X : forall (l : opaque_list) (proof : noLeadingZeros l), P (depConstr l proof))
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
    (X : forall (l : opaque_list) (p : noLeadingZeros l), C)
    (l : opaque_list) (proof : noLeadingZeros l) :
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
    (X : forall (l : opaque_list) (p : noLeadingZeros l), C)
    (l : opaque_list) (proof : noLeadingZeros l) :
    forall (Q : C -> Type),
      (Q (depRec C X (depConstr l proof))) -> Q (X l proof).
  Proof.
    intros.
    rewrite <- iotaRecEq.
    assumption.
  Qed.

  Definition iotaRecRev (C : Type)
    (X : forall (l : opaque_list) (p : noLeadingZeros l), C)
    (l : opaque_list) (proof : noLeadingZeros l) :
    forall (Q : C -> Type),
      Q (X l proof) -> (Q (depRec C X (depConstr l proof))).
  Proof.
    intros.
    rewrite iotaRecEq.
    assumption.
  Qed.

  Import ListFns.
    
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

  Definition eval (p : CLPoly) (n : nat) :=
    depRec nat (fun (l : opaque_list) (proof : noLeadingZeros l) => evalList l n) p.

  Instance evalProper : Proper (eq_CLPoly ==> eq ==> eq) eval.
  Proof.
    unfold eval.
    solve_proper2.
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

  Definition addCommFirstDepElimMotive (p2 : CLPoly) :=
    fun p => eq_CLPoly (add p p2) (add p2 p).

  Definition addCommFirstProperGoal (p2 : CLPoly) :
    Proper (eq_CLPoly ==> iff) (fun p : CLPoly => eq_CLPoly (add p p2) (add p2 p)).
  Proof.
    solve_proper.
  Qed.

  Definition addCommFirstDepElim p2 := depElimProp (addCommFirstDepElimMotive p2) (addCommFirstProperGoal p2).

  Definition addCommSecondDepElimMotive (l : opaque_list) (proof : noLeadingZeros l) :=
    fun p => eq_CLPoly (add (depConstr l proof) p) (add p (depConstr l proof)).

  Theorem addCommSecondProperGoal (l : opaque_list) (proof : noLeadingZeros l) : 
    Proper
      (eq_CLPoly ==> iff)
      (addCommSecondDepElimMotive l proof).
  Proof.
    intros.
    unfold addCommSecondDepElimMotive.
    solve_proper.
  Qed.

  Definition addCommSecondDepElim l proof :=
    depElimProp (addCommSecondDepElimMotive l proof) (addCommSecondProperGoal l proof).

  Theorem addComm :
    forall (p1 p2 : CLPoly),
      eq_CLPoly (add p1 p2) (add p2 p1).
  Proof.
    intros.
    eapply (addCommFirstDepElim p2).
    intros.
    eapply (addCommSecondDepElim l proof).
    unfold addCommSecondDepElimMotive.
    intros.
    unfold add.
    repeat (apply iotaRecRev).
    apply (fun y => eq_rect _ (fun (x : noLeadingZeros (addLists l0 l)) => eq_CLPoly (depConstr (addLists l l0) (addListsNoLeadingZeros l l0 proof proof0)) (depConstr (addLists l0 l) x)) y (addListsNoLeadingZeros l0 l proof0 proof) (addListsCommNoLeadingZerosProofIrr l l0 proof proof0)).
    exact (internal_eq_rew_dep opaque_list (ListFns.addLists l l0)
                       (fun (a : opaque_list) (e : ListFns.addLists l l0 = a) =>
                        CLPoly.eq_CLPoly
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (ListFns.addListsNoLeadingZeros l l0 proof proof0))
                          (CLPoly.depConstr a
                             (eq_rect (ListFns.addLists l l0)
                                (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0) a e)))
                       (reflexivity
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (ListFns.addListsNoLeadingZeros l l0 proof proof0))) (ListFns.addLists l0 l)
                       (ListFns.addListsComm l l0)).
  Qed.

  Print addComm.

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

End CLPoly.



Module CEPPoly.

  Definition CEPPoly := list (nat * nat).

  Fixpoint coeff (p : CEPPoly) (exp : nat) :=
    match p with
    | [] => 0
    | (n, e) :: t => (if eqb exp e then n else 0) + (coeff t exp)
    end.

  Definition eq_CEPPoly (p1 p2 : CEPPoly) :=
    forall (exp : nat), coeff p1 exp = coeff p2 exp.

  Instance eq_CEPPoly_refl : Reflexive eq_CEPPoly.
  Proof.
    intros x.
    unfold eq_CEPPoly.
    reflexivity.
  Qed.

  Instance eq_CEPPoly_sym : Symmetric eq_CEPPoly.
  Proof.
    intros x1 x2 H.
    unfold eq_CEPPoly.
    unfold eq_CEPPoly in H.
    symmetry.
    apply H.
  Qed.

  Instance eq_CEPPoly_trans : Transitive eq_CEPPoly.
  Proof.
    intros x1 x2 x3 H1 H2.
    unfold eq_CEPPoly in *.
    congruence.
  Qed.

  Instance eq_CEPPoly_equiv : Equivalence eq_CEPPoly.
  Proof.
    split.
    - apply eq_CEPPoly_refl.
    - apply eq_CEPPoly_sym.
    - apply eq_CEPPoly_trans.
  Qed.

  Theorem permutation_implies_equiv p1 p2 : Permutation p1 p2 -> eq_CEPPoly p1 p2.
  Proof.
    intros.
    induction H.
    - reflexivity.
    - unfold eq_CEPPoly. intro.
      simpl. destruct x.
      f_equal.
      apply IHPermutation.
    - unfold eq_CEPPoly.
      simpl.
      intro.
      destruct x.
      destruct y.
      rewrite ->! PeanoNat.Nat.add_assoc.
      f_equal.
      apply PeanoNat.Nat.add_comm.
    - congruence.
  Defined.

  Theorem eq_CEPPoly_app_comm :
    forall l1 l2, eq_CEPPoly (l1 ++ l2) (l2 ++ l1).
  Proof.
    intros.
    apply permutation_implies_equiv.
    apply Permutation_app_comm.
  Defined.

  Theorem eq_CEPPoly_app :
    forall l1 l2 app, eq_CEPPoly l1 l2 -> eq_CEPPoly (l1 ++ app) (l2 ++ app).
  Proof.
    intros.
    rewrite eq_CEPPoly_app_comm.
    rewrite (eq_CEPPoly_app_comm l2 app).
    induction app.
    * simpl. apply H.
    * simpl.
      unfold eq_CEPPoly.
      intros.
      simpl.
      destruct a.
      f_equal.
      apply IHapp.
  Defined.

  Fixpoint get_max_degree (l: CEPPoly) : nat :=
    match l with
      | [] => 0
      | (coe, exp) :: xs => match coe with
        | 0 => get_max_degree xs
        | _ => max exp (get_max_degree xs)
        end
    end.

  Fixpoint canonicalize_help (acc : CEPPoly) (l: CEPPoly) (i : nat) : CEPPoly :=
    match i with
      | 0  => (coeff l 0, 0) :: acc
      | S n => canonicalize_help ((coeff l i, i) :: acc) l n
    end.

  Definition canonicalize (l: CEPPoly) : CEPPoly :=
    canonicalize_help [] l (get_max_degree l).

  Definition canonicalize_alt (l: CEPPoly) : CEPPoly :=
    let asec_seq := (seq 0 (S (get_max_degree l))) in
    (combine (map (coeff l) asec_seq) asec_seq).

  Fixpoint get_leading_same_exp_help (l : CEPPoly) (exp : nat) : CEPPoly :=
    match l with
    | [] => []
    | (n1, e1) :: t =>
        if eqb e1 exp then
          (n1, e1) :: get_leading_same_exp_help t exp
        else
          get_leading_same_exp_help t exp
    end.

  Print filter.

  Definition monomial_less_than_degree_n (n : nat) (p : nat * nat) :=
    match p with
    | (_, exp) => ltb exp n
    end.

  Definition remove_degrees_ge_n (p : CEPPoly) (n : nat) : CEPPoly :=
    filter (monomial_less_than_degree_n n) p.

  Theorem greater_degrees_not_in_remove_degrees :
    forall (p : CEPPoly) (n exp c : nat),
      n <= exp -> ~ In (c, exp) (remove_degrees_ge_n p n).
  Proof.
    induction p.
    - simpl.
      intros.
      intros H0.
      contradiction.
    - intros.
      unfold remove_degrees_ge_n.
      intros H0.
      rewrite filter_In in H0.
      destruct H0.
      simpl in H0.
      destruct H0.
      + unfold monomial_less_than_degree_n in H1.
        rewrite PeanoNat.Nat.ltb_lt in H1.
        apply Lt.lt_not_le in H1.
        contradiction.
      + specialize (IHp n exp c H).
        unfold remove_degrees_ge_n in IHp.
        assert (In (c, exp) p /\ monomial_less_than_degree_n n (c, exp) = true).
          split;
          assumption.
        apply filter_In in H2.
        contradiction.  
  Qed.

  Theorem remove_degrees_0_empty (p : CEPPoly) :
    remove_degrees_ge_n p 0 = [].
  Proof.
    induction p.
    - reflexivity.
    - simpl.
      unfold remove_degrees_ge_n in IHp.
      destruct a.
      unfold monomial_less_than_degree_n.
      simpl.
      apply IHp.
  Qed.

  Definition monomial_degree_n (n : nat) (p : nat * nat) :=
    match p with
    | (_, exp) => eqb n exp
    end.

  Definition degree_n_terms (p : CEPPoly) (n : nat) :=
    filter (monomial_degree_n n) p.

  Theorem coeff_only_degree_equal :
    forall (p : CEPPoly) (n : nat),
      coeff p n = coeff (degree_n_terms p n) n.
  Proof.
    induction p;
    intros.
    - reflexivity.
    - simpl.
      destruct a.
      unfold monomial_degree_n.
      destruct (PeanoNat.Nat.eqb_spec n n1).
      + simpl.
        apply PeanoNat.Nat.eqb_eq in e.
        rewrite e.
        rewrite IHp.
        reflexivity.
      + apply IHp.
  Qed.

  Theorem no_degree_n_terms_after_removed :
    forall (p : CEPPoly) (n exp : nat),
      (n <= exp) ->
      degree_n_terms (remove_degrees_ge_n p n) exp = [].
  Proof.
    intros.
    unfold degree_n_terms.
    unfold remove_degrees_ge_n.
    enough
      (forall (c1 exp1 : nat),
          ~ In (c1, exp1)
            (filter (monomial_degree_n exp) (filter (monomial_less_than_degree_n n) p))).
    - destruct (filter (monomial_degree_n exp) (filter (monomial_less_than_degree_n n) p)).
      + reflexivity.
      + destruct p0.
        specialize (H0 n0 n1).
        simpl in H0.
        apply Decidable.not_or in H0.
        destruct H0.
        contradiction.
    - intros.
      intros H0.
      apply filter_In in H0.
      destruct H0.
      apply filter_In in H0.
      destruct H0.
      unfold monomial_less_than_degree_n in H2.
      unfold monomial_degree_n in H1.
      apply PeanoNat.Nat.eqb_eq in H1.
      rewrite H1 in H.
      apply PeanoNat.Nat.ltb_lt in H2.
      apply Lt.lt_not_le in H2.
      contradiction.
  Qed.

  Theorem degree_n_terms_not_removed :
    forall (p : CEPPoly) (n exp : nat),
      (exp < n) ->
      degree_n_terms (remove_degrees_ge_n p n) exp = degree_n_terms p exp.
  Proof.
    induction p.
    - intros.
      reflexivity.
    - intros.
      destruct a.
      simpl.
      destruct (PeanoNat.Nat.ltb_spec n1 n).
      + simpl.
        rewrite IHp; auto.
      + assert (exp <> n1) by lia.
        apply PeanoNat.Nat.eqb_neq in H1.
        rewrite H1.
        apply IHp.
        apply H.
  Qed.

  Theorem coeff_of_removed_degree_0 : forall (n exp : nat) (p : CEPPoly),
      (n <= exp) -> coeff (remove_degrees_ge_n p n) exp = 0.
  Proof.
    intros.
    rewrite coeff_only_degree_equal.
    rewrite no_degree_n_terms_after_removed.
    - reflexivity.
    - lia.
  Qed.

  Theorem remove_degrees_Sn :
    forall (p : CEPPoly) (n : nat),
      eq_CEPPoly
        (remove_degrees_ge_n p (S n))
        ((coeff p n, n) :: remove_degrees_ge_n p n).
  Proof.
    intros.
    unfold eq_CEPPoly.
    intros exp.
    destruct (PeanoNat.Nat.lt_trichotomy n exp); [|destruct H].
    - unfold lt in H.
      pose proof (coeff_of_removed_degree_0 _ _ p H).
      rewrite H0.
      rewrite coeff_only_degree_equal.
      simpl.
      assert (exp <> n).
      lia.
      apply PeanoNat.Nat.eqb_neq in H1.
      rewrite H1.
      rewrite no_degree_n_terms_after_removed.
      + reflexivity.
      + lia.
    - subst.
      simpl.
      rewrite <- EqNat.beq_nat_refl.
      assert (exp <= exp) by lia.
      rewrite (coeff_of_removed_degree_0 _ _ _ H).
      rewrite coeff_only_degree_equal.
      rewrite degree_n_terms_not_removed.
      + rewrite <- coeff_only_degree_equal.
        lia.
      + lia.
    - simpl.
      assert (exp <> n) by lia.
      apply PeanoNat.Nat.eqb_neq in H0.
      rewrite H0.
      rewrite coeff_only_degree_equal.
      assert (exp < S n) by lia.
      rewrite (degree_n_terms_not_removed _ _ _ H1).
      rewrite (coeff_only_degree_equal (remove_degrees_ge_n p n)).
      rewrite (degree_n_terms_not_removed _ _ _ H).
      lia.
  Qed.

  Theorem unsimpl_app_cons {A : Type} :
    forall (a : A) (l : list A),
      a :: l = [a] ++ l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem canonicalize_respects_eq_help : forall n l acc,
      eq_CEPPoly (remove_degrees_ge_n l (S n) ++ acc) (canonicalize_help acc l n).
  Proof.
    intro.
    induction n.
    * intros.
      simpl.
      rewrite unsimpl_app_cons.
      apply eq_CEPPoly_app.
      rewrite remove_degrees_Sn.
      rewrite remove_degrees_0_empty.
      reflexivity.
    * intros.
      simpl.
      specialize (IHn l ((coeff l (S n), S n) :: acc)).
      rewrite <- IHn.
      simpl.
      rewrite unsimpl_app_cons.
      rewrite app_assoc.
      apply eq_CEPPoly_app.
      rewrite remove_degrees_Sn.
      rewrite unsimpl_app_cons.
      apply eq_CEPPoly_app_comm.
  Qed.

  Theorem get_max_degree_sublist : forall (p : CEPPoly) (c exp : nat),
      get_max_degree p <= get_max_degree ((c, exp) :: p).
  Proof.
    intros.
    simpl.
    destruct c.
    - reflexivity.
    - lia.
  Qed.

  Theorem get_max_degree_head :
    forall (p : CEPPoly) (c exp : nat),
      (c <> 0) -> exp <= get_max_degree ((c, exp) :: p).
  Proof.
    intros.
    simpl.
    destruct c.
    - contradiction. 
    - lia.
  Qed.

  Theorem eq_CEPPoly_remove_0 :
    forall (p : CEPPoly) (exp : nat),
      eq_CEPPoly ((0, exp) :: p) p.
  Proof.
    unfold eq_CEPPoly.
    intros.
    simpl.
    destruct (exp0 =? exp); reflexivity.
  Qed.

  Theorem eq_CEPPoly_cons :
    forall (p1 p2 : CEPPoly) (c exp : nat),
      eq_CEPPoly ((c, exp) :: p1) ((c, exp) :: p2) <->
      eq_CEPPoly p1 p2.
  Proof.
    unfold eq_CEPPoly.
    intros.
    simpl.
    split;
    intros;
    specialize (H exp0);
    lia.
  Qed.
      
  Theorem remove_greater_than_max_degree :
    forall (p : CEPPoly) (n : nat),
      (get_max_degree p < n) -> eq_CEPPoly (remove_degrees_ge_n p n) p.
  Proof.
    induction p.
    - reflexivity.
    - intros.
      destruct a.
      pose proof (get_max_degree_sublist p n0 n1).
      assert (get_max_degree p < n) by lia.
      simpl.
      destruct (PeanoNat.Nat.eq_dec n0 0).
      + subst.
        simpl in H.
        specialize (IHp _ H1).
        destruct (PeanoNat.Nat.ltb_spec n1 n).
        * rewrite eq_CEPPoly_remove_0.
          rewrite eq_CEPPoly_remove_0.
          apply IHp.
        * rewrite eq_CEPPoly_remove_0.
          apply IHp.
      + apply (get_max_degree_head p _ n1) in n2.
        assert (n1 < n) by lia.
        apply PeanoNat.Nat.ltb_lt in H2.
        rewrite H2.
        rewrite eq_CEPPoly_cons.
        apply (IHp _ H1).
  Qed.

  Theorem canonicalize_pres:
    forall p,
      eq_CEPPoly p (canonicalize p).
  Proof.
    intros.
    unfold canonicalize.
    rewrite <- canonicalize_respects_eq_help.
    rewrite app_nil_r.
    assert (get_max_degree p < S (get_max_degree p)) by lia.
    apply remove_greater_than_max_degree in H.
    symmetry.
    apply H.
  Qed.

  Theorem acc_always_contained_at_end_help_eq :
    forall n l acc, ((canonicalize_help [] l n) ++ acc) = (canonicalize_help acc l n).
  Proof.
    intro.
    induction n.
    * simpl. reflexivity.
    * simpl.
      intros.
      rewrite <- (IHn l [(coeff l (S n), S n)]).
      rewrite <- (IHn l ((coeff l (S n), S n) :: acc)).
      rewrite <- (app_assoc (canonicalize_help [] l n) [(coeff l (S n), S n)] acc).
      simpl.
      reflexivity.
  Defined.

  Theorem eqb_refl n : n =? n = true.
  Proof.
    intros.
    induction n.
    * auto.
    * simpl. apply IHn.
  Qed.

  (* Shows that max degree will indeed find all the degrees for non-zero coeffs *)
  Theorem get_max_degree_non_zero (l : CEPPoly) : get_max_degree l > 0 -> coeff l (get_max_degree l) <> 0.
  Proof.
    intros.
    induction l.
    + simpl in H. lia.
    + destruct a.
      destruct n.
      - simpl. simpl in H. apply IHl in H. lia.
      - pose proof (Arith.Compare_dec.lt_eq_lt_dec n0 (get_max_degree l)).
        destruct H0.
        * destruct s.
           ++ simpl in H.
              Search max.
              assert (get_max_degree l > 0). lia.
              apply IHl in H0.
              simpl.
              assert (max n0 (get_max_degree l) = get_max_degree l). lia.
              rewrite H1.
              lia.
          ++ simpl in H.
             assert (get_max_degree l > 0). lia.
             apply IHl in H0.
             simpl.
             assert (max n0 (get_max_degree l) = get_max_degree l). lia.
             rewrite H1.
             lia.
        * simpl in H.
          assert (n0 > 0). lia.
          simpl.
          assert (max n0 (get_max_degree l) = n0). lia.
          rewrite H1.
          rewrite eqb_refl.
          lia.
  Defined.

  Theorem get_max_degree_complete (l : CEPPoly) : forall deg, coeff l deg <> 0 -> deg <= get_max_degree l.
  Proof.
    induction l.
    + intros.
      induction deg.
      - lia.
      - simpl in H. lia.
    + intros. destruct a.
      destruct n.
      * simpl in H.
        simpl.
        destruct (deg =? n0); simpl in H; apply (IHl deg) in H; apply H.
      * pose proof (Peano_dec.eq_nat_dec deg n0).
        destruct H0.
        - rewrite e in *.
          simpl. lia.
        - simpl in H.
          assert (deg =? n0 = false).
          {
            clear l IHl H n.
            apply PeanoNat.Nat.eqb_neq.
            apply n1.
          }
          pose proof (IHl n0).
          rewrite H0 in H. simpl in H.
          pose proof (IHl deg H).
          simpl.
          lia.
  Defined.

  Theorem eq_maxDegreeSame_le (l1 l2 : CEPPoly) : forall (p : eq_CEPPoly l1 l2), get_max_degree l1 <= get_max_degree l2.
  Proof.
    intros.
    induction l2.
    + unfold eq_CEPPoly in p.
      simpl.
      induction l1.
      * auto.
      * destruct a.
        destruct n0.
        - simpl.
          {
            destruct n.
            +  apply IHl1.
                intro.
                pose proof (p exp).
                simpl in H.
                destruct exp; simpl in H; apply H.
            + apply IHl1. intro.
              pose proof (p exp).
              simpl in H.
              destruct (if exp =? 0 then S n else 0).
              - simpl in H. apply H.
              - discriminate.
          }
        - destruct n.
          {
            simpl.
            apply IHl1.
            intros.
            pose proof (p exp).
            simpl in H.
            destruct (exp =? S n0); simpl in H; apply H.
          }
          pose proof (p (S n0)).
          simpl in H.
          rewrite eqb_refl in H.
          discriminate.
    + destruct a.
      unfold eq_CEPPoly in p.
      destruct n.
      * simpl. apply IHl2.
        simpl in p. intro.
        pose proof (p exp).
        destruct (exp =? n0); simpl in H; apply H.
      * pose proof (get_max_degree_complete l2 (get_max_degree l1)).
        pose proof (Arith.Compare_dec.lt_eq_lt_dec n0 (get_max_degree l1)).
        destruct H0.
        - destruct s.
          -- unfold get_max_degree at 2.
             Search max.
             assert (n0 <= get_max_degree l1). lia.
             assert (forall n m p, m < n -> n <= p -> n <= max m p).
             {
               intros.
               induction m.
               + simpl. apply H2.
               + simpl. destruct p0; lia.
             }
             apply H1.
             apply l.
             fold get_max_degree.
             apply H.
             assert (get_max_degree l1 > 0) as side_lemma. lia.
             pose proof (get_max_degree_non_zero l1 side_lemma).
             pose proof (p (get_max_degree l1)).
             clear H0.
             rewrite H3 in H2.
             simpl in H2.
             assert (get_max_degree l1 =? n0 = false).
             {
               clear l2 p IHl2 H H1 H2 H3.
               apply PeanoNat.Nat.eqb_neq.
               intros H.
               rewrite H in l. apply (PeanoNat.Nat.lt_irrefl (get_max_degree l1)).
               lia.
             }
             rewrite H0 in H2. simpl in H2.
             apply H2.
          -- unfold get_max_degree at 2.
             rewrite e.
             lia.
        -  unfold get_max_degree at 2.
           lia.
  Defined.

  Theorem eq_maxDegreeSame (l1 l2 : CEPPoly) : forall (p : eq_CEPPoly l1 l2), get_max_degree l1 = get_max_degree l2.
  Proof.
    intros.
    pose proof (eq_maxDegreeSame_le l1 l2 p).
    assert (eq_CEPPoly l2 l1). congruence.
    pose proof (eq_maxDegreeSame_le l2 l1 H0).
    lia.
  Defined.

  Instance canonicalIsCanonical : Proper (eq_CEPPoly ==> eq) canonicalize.
  Proof.
    intros p1 p2 H.
    unfold canonicalize.
    pose proof (eq_maxDegreeSame p1 p2 H).
    rewrite <- H0.
    remember (get_max_degree p1).
    induction n in |- *.
    * simpl.
      unfold eq_CEPPoly in H.
      rewrite H.
      reflexivity.
    * simpl.
      rewrite <- (acc_always_contained_at_end_help_eq n p1 [(coeff p1 (S n), S n)]).
      rewrite <- (acc_always_contained_at_end_help_eq n p2 [(coeff p2 (S n), S n)]).
      rewrite H.
      rewrite IHn.
      reflexivity.
  Qed.

  Fixpoint CEPFromCoeffListHelp (l : list nat) (exp : nat) :=
    match l with
    | [] => []
    | h :: t =>
        (h, exp) :: (CEPFromCoeffListHelp t (S exp))
    end.

  Definition CEPFromCoeffList (l : list nat) := rev (CEPFromCoeffListHelp (rev l) 0).

  Fixpoint zeros (n : nat) :=
    match n with
    | 0 => []
    | S m => 0 :: (zeros m)
    end.

  Definition coeffListFromCEPHelp (p : CEPPoly) :=
    map fst p.
  
  Definition coeffListFromCEP (p : CEPPoly) :=
    removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize p))).
  
  Theorem coeffListFromCEPNoLeadingZeros (p : CEPPoly) :
    noLeadingZeros (coeffListFromCEP p).
  Proof.
    unfold coeffListFromCEP.
    apply ListFns.noLeadingZerosRemoveLeadingZeros.
  Qed.

  Definition depConstr (l : list nat) (p : noLeadingZeros l) := CEPFromCoeffList l.

  Definition depRec (C : Type) (X : forall (l : list nat) (p : noLeadingZeros l), C) (p : CEPPoly) : C :=
    X (coeffListFromCEP p) (coeffListFromCEPNoLeadingZeros p).


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

  Theorem canonicalize_max_preserves_coeffs (l : CEPPoly) : forall k, forall n, n <= k -> coeff l n = coeff (canonicalize l) n.
  Proof.
  Admitted.

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
    assert (eq_rect (canonicalize p1) (fun x => noLeadingZeros (removeLeadingZeros (coeffListFromCEPHelp (rev x)))) (coeffListFromCEPNoLeadingZeros p1) (canonicalize p2) H = coeffListFromCEPNoLeadingZeros p2).
    apply noLeadingZerosProofIrr.
    destruct H0.
    destruct H.
    reflexivity.
  Qed.

  Theorem CEPFromCoeffListApp : forall (l1 l2 : list nat) (n : nat),
    (CEPFromCoeffListHelp (l1 ++ l2) n) =
    ((CEPFromCoeffListHelp l1 n) ++ (CEPFromCoeffListHelp l2 (length l1 + n))).
  Proof.
    induction l1.
    - intros.
      reflexivity.
    - simpl.
      intros.
      f_equal.
      rewrite <- PeanoNat.Nat.add_succ_r.
      apply IHl1.
  Qed.

  Theorem eq_CEPPoly_rev : forall (p : CEPPoly),
      eq_CEPPoly (rev p) p.
  Proof.
    intros.
    apply permutation_implies_equiv.
    symmetry.
    apply Permutation_rev.
  Qed.

  Theorem removeLeadingZerosCoeffListEquiv :
    forall (l : list nat),
      eq_CEPPoly (CEPFromCoeffList (removeLeadingZeros l)) (CEPFromCoeffList l).
  Proof.
    unfold CEPFromCoeffList.
    induction l.
    - reflexivity.
    - simpl.
      destruct (PeanoNat.Nat.eqb_spec a 0).
      + rewrite e.
        simpl.
        rewrite eq_CEPPoly_rev.
        rewrite eq_CEPPoly_rev.
        rewrite CEPFromCoeffListApp.
        simpl.
        rewrite eq_CEPPoly_app_comm.
        simpl.
        rewrite eq_CEPPoly_remove_0.
        rewrite eq_CEPPoly_rev in IHl.
        rewrite eq_CEPPoly_rev in IHl.
        apply IHl.
      + reflexivity.
  Qed.

  Theorem inductOnDegree :
    forall (P : CEPPoly -> Prop),
      (forall (p : CEPPoly), get_max_degree p = 0 -> P p) ->
      (forall (n : nat),
          (forall (p : CEPPoly), get_max_degree p = n -> P p) ->
          (forall (p : CEPPoly), get_max_degree p = S n -> P p)) ->
      forall (p : CEPPoly), P p.
  Proof.
    intros.
  Admitted.

  Theorem canonicalizeMaxDegreeLength :
    forall (p : CEPPoly),
      get_max_degree p = 0 \/
      (S (get_max_degree p) = (length (canonicalize p)) /\ length (canonicalize p) <> 0).
  Proof.
  Admitted.

  Theorem canonicalizeDegreeZero :
    forall (p : CEPPoly),
      get_max_degree p = 0 -> canonicalize p = [((coeff p 0), 0)].
  Proof.
    intros.
    unfold canonicalize.
    rewrite H.
    reflexivity.
  Qed.

  Theorem canonicalizeDegreeSn :
    forall (p : CEPPoly),
      get_max_degree p <> 0 ->
      eq_CEPPoly (canonicalize p) ((coeff p (get_max_degree p), get_max_degree p) :: (canonicalize (remove_degrees_ge_n p (get_max_degree p)))).
  Proof.
    intros.
  Admitted.

  Theorem canonicalizeHead :
    forall (p : CEPPoly),
      canonicalize p = [((coeff p 0), 0)] \/
      eq_CEPPoly (canonicalize p) ((coeff p (get_max_degree p), get_max_degree p) :: (canonicalize (remove_degrees_ge_n p (get_max_degree p)))).
  Proof.
    intros.
    unfold canonicalize.
    
  Admitted.

(*  Theorem coeffListFromCEPCoeff :
    forall (p : CEPPoly) (exp : nat),
      exp <= get_max_degree p ->
      (is_true (nth_ok exp (rev (coeffListFromCEP p)) (S (get_max_degree p)))) /\
      (nth exp (rev (coeffListFromCEP p)) (S (get_max_degree p)) = coeff p exp).
  Proof.
    intros.
    unfold coeffListFromCEP.
  Admitted.*)

  Theorem CEPFromCoeffListCoeff :
    forall (l : list nat) (exp : nat),
      coeff (CEPFromCoeffList l) exp = nth exp (rev l) 0.
  Proof.
    induction l.
    - intros.
      simpl.
      destruct exp; reflexivity.
    - intros.
      unfold CEPFromCoeffList.
      simpl.
      rewrite CEPFromCoeffListApp.
      rewrite rev_app_distr.
      simpl.
      rewrite PeanoNat.Nat.add_0_r.
      rewrite rev_length.
      unfold CEPFromCoeffList in IHl.
      rewrite IHl.
      destruct (PeanoNat.Nat.lt_trichotomy (length l) exp); [|destruct H].
      + assert (exp <> length l) by lia.
        pose proof H0.
        apply PeanoNat.Nat.eqb_neq in H0.
        rewrite H0.
        rewrite nth_overflow.
        * rewrite app_nth2;
          rewrite rev_length.
          assert (0 < exp - length l) by lia.
          rewrite nth_overflow.
          reflexivity.
          simpl.
          lia.
          lia.
        * rewrite rev_length.
          lia.
      + pose proof H.
        symmetry in H0.
        apply PeanoNat.Nat.eqb_eq in H0.
        rewrite H0.
        rewrite app_nth2;
        rewrite rev_length;
        [|lia].
        rewrite H.
        rewrite PeanoNat.Nat.sub_diag.
        rewrite nth_overflow.
        rewrite PeanoNat.Nat.add_0_r.
        reflexivity.
        rewrite rev_length.
        lia.
      + assert (exp <> length l) by lia.
        pose proof H0.
        apply PeanoNat.Nat.eqb_neq in H1.
        rewrite H1.
        rewrite app_nth1.
        * reflexivity.
        * rewrite rev_length.
          lia.
  Qed.

  (* Theorem map_f_equal {A} {B} : *)
  (*   forall (f1 : A -> B) (f2: A -> B) (l : list A), *)
  (*     (forall a, f1 a = f2 a) -> map f1 l = map f2 l. *)
  (* Proof. *)
  (*   intros. *)
  (*   induction l. *)
  (*   - reflexivity. *)
  (*   - simpl. rewrite IHl. rewrite H. reflexivity. *)
  (* Defined. *)
  Definition combined_n_m n m : list (nat * nat) :=
    combine (repeat 0 (n - m)) (rev (seq m (n - m))).
  Compute (combined_n_m 6 3).


  Theorem canonicalize_equiv_canonicalize_alt:
    forall p, canonicalize p = canonicalize_alt p.
  Proof.
    intros.
    induction p using
      (well_founded_induction
         (wf_inverse_image _ nat _  get_max_degree
            PeanoNat.Nat.lt_wf_0)).
    unfold canonicalize. unfold canonicalize_alt.
    remember (get_max_degree p).
    destruct n.
    reflexivity.
    simpl.
    rewrite <- acc_always_contained_at_end_help_eq.
    Print remove_degrees_ge_n.
    assert (canonicalize_help [] p (get_max_degree p)
                              =
            canonicalize_help
              (combined_n_m
                 (get_max_degree p)
                 (S (get_max_degree (remove_degrees_ge_n p (get_max_degree p))))
              )
              (remove_degrees_ge_n p (get_max_degree p))
              (get_max_degree (remove_degrees_ge_n p (get_max_degree p)))
              ++
              [(coeff p (get_max_degree p), (get_max_degree p))]
           ).
  Admitted.

  Theorem map_fst_combine A B:
    forall (l1 : list A) (l2 : list B), length l1 = length l2 -> (map fst (combine l1 l2)) = l1.
  Proof.
    induction l1.
    + reflexivity.
    + intros. destruct l2. discriminate.
      simpl.
      inversion H.
      rewrite (IHl1 l2 H1).
      reflexivity.
  Defined.

  Theorem removeLeadingZerosnth :
    forall l n,
      nth n (rev (removeLeadingZeros l)) 0 = nth n (rev l) 0.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - simpl. destruct a; simpl.
      + rewrite IHl.
        destruct (PeanoNat.Nat.lt_trichotomy n (length (rev l))).
        * rewrite (app_nth1); auto.
        * destruct H.
          -- rewrite (app_nth2). rewrite H at 2.
             rewrite (PeanoNat.Nat.sub_diag).
             simpl.
             rewrite nth_overflow.
             reflexivity.
             lia.
             lia.
          -- rewrite ->! nth_overflow. reflexivity.
             rewrite app_length.
             simpl.
             lia.
             lia.
      + reflexivity.
  Defined.

  Print coeffListFromCEP.
  Print canonicalize.
  Print canonicalize_help.

  Definition CoeffPairsNToMaxDeg (n : nat) (p : CEPPoly) :=
    map (fun x => (coeff p x, x)) (seq n (get_max_degree p + 1 - n)).

  Module Test.
  Print canonicalize_help.

  Definition p := [(3, 1); (2, 4); (5, 2)].
  Definition n := 3.
  Definition exp := 5.

  Print canonicalize_help.
  Print seq.

  Eval compute in (seq 0 (get_max_degree p + 1 - 0)).

  Eval compute in (canonicalize_help [] p n) ++ ((coeff p (S n), S n) :: (CoeffPairsNToMaxDeg (S n) p)).

  Eval compute in (nth exp
    (rev (removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize_help (CoeffPairsNToMaxDeg (S n) p) p n)))))
    0).
  Eval compute in (nth exp
    (rev (removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize_help ((coeff p (S n), S n) :: (CoeffPairsNToMaxDeg (S n) p)) p n)))))
    0).
  End Test.

  Module Test2.
    Definition p := [(1, 0) ; (2, 1) ; (3, 2)].
    Definition n := 3.
    Eval compute in ((coeff p (S n), S n) :: CoeffPairsNToMaxDeg (S (S n)) p = CoeffPairsNToMaxDeg (S n) p).
  Eval compute in (S n :: seq (S (S n)) (get_max_degree p + 1 - S (S n)) = seq (S n) (get_max_degree p + 1 - S n)).
  End Test2.

  Theorem coeffListFromCEPCoeff :
    forall (n : nat) (p : CEPPoly) (exp : nat) (acc : CEPPoly),
      acc = CoeffPairsNToMaxDeg (S n) p ->
      coeff p exp = nth exp (rev (removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize_help acc p n))))) 0.
  Proof.
    induction n.
    - intros.
      simpl.
      unfold coeffListFromCEPHelp.
      rewrite map_app.
      simpl.
      rewrite removeLeadingZerosnth.
      rewrite rev_app_distr.
      simpl.
      rewrite H.
      rewrite map_rev.
      rewrite rev_involutive.
      unfold CoeffPairsNToMaxDeg.
      rewrite map_map.
      simpl.
      enough (forall (A : Type) (d : A) (n len start : nat) (f : nat -> A), n < len -> nth n (map f (seq start len)) d = f (start + n)).
      destruct (PeanoNat.Nat.le_decidable exp (get_max_degree p)).
      destruct exp; auto.        
      rewrite (H0 nat 0 exp (get_max_degree p + 1 - 1)).
      reflexivity.
      unfold lt.
        lia.
        destruct exp; auto.
        rewrite nth_overflow.
        assert (get_max_degree p < S exp).
        lia.
        Print remove_greater_than_max_degree.
        enough (get_max_degree p < S exp -> coeff p (S exp) = 0).
        * apply H3.
          apply H2.
        * give_up.
        * rewrite map_length.
          rewrite seq_length.
          lia.
        * give_up. (*prove this*)
       (*this should be an assumption*)
    - simpl.
      intros.
      rewrite H.
      (*enough ((coeff p (S n), S n) :: CoeffPairsNToMaxDeg (S (S n)) p = CoeffPairsNToMaxDeg (S n) p).
      rewrite H0.*)
      pose proof (IHn p exp ((coeff p (S n), S n)  :: acc)).
      destruct acc.
      + simpl in H.
        give_up.
      + apply H0.
      apply IHn.
      reflexivity.
      unfold CoeffPairsNToMaxDeg.
      simpl.
      assert ((coeff p (S n), S n) :: map (fun x : nat => (coeff p x, x)) (seq (S (S n)) (get_max_degree p + 1 - S (S n))) = map (fun x : nat => (coeff p x, x)) (S n :: seq (S (S n)) (get_max_degree p + 1 - S (S n)))).
      reflexivity.
      rewrite H0.
      f_equal.
      simpl.
      rewrite (IHn _ _ (CoeffPairsNToMaxDeg (S (S n)) p)).
      repeat f_equal.
      rewrite H.
      unfold CoeffPairsNToMaxDeg.
      rewrite 
        rewrite seq_shift.
        rewrite seq_nth.
      induction exp.
      + reflexivity.
      + rewrite map_rev.
        rewrite rev_involutive.
        
        * rewrite H.
          unfold CoeffPairsNToMaxDeg.
          rewrite map_map.
          simpl.
    intros p.
    remember (get_max_degree p).
    revert Heqn.
  
  
  Theorem coeffListFromCEPCoeff :
    forall (p : CEPPoly) (exp : nat),
      coeff p exp = nth exp (rev (coeffListFromCEP p)) 0.
  Proof.
    intros.
    unfold coeffListFromCEP.
    rewrite canonicalize_equiv_canonicalize_alt.
    unfold canonicalize_alt.
    rewrite rev_involutive.
    unfold coeffListFromCEPHelp.
    assert ((length (map (coeff p) (seq 0 (get_max_degree p)))) = (length (seq 0 (get_max_degree p)))).
    rewrite map_length. reflexivity.
    rewrite (map_fst_combine _ _ _ _ H).
    rewrite removeLeadingZerosnth.
    rewrite <- map_rev.
    assert (nth exp (map (coeff p) (rev (seq 0 (get_max_degree p)))) 0 =
            nth exp (map (coeff p) (rev (seq 0 (get_max_degree p)))) (coeff p exp)).
    {
      pose proof (get_max_degree_complete p exp).
      Check get_max_degree_complete.
      give_up.
    }
    rewrite H0.
    rewrite map_nth.
    assert (forall n, (nth exp (rev (seq 0 n)) exp) = exp).
    give_up.
    rewrite H1.
    reflexivity.
  Admitted.

  (* Definition canonicalize_alt' (l: CEPPoly) : CEPPoly := *)
  (*   let asec_seq := (seq 0 (get_max_degree l)) in *)
  (*   rev (combine (map (coeff l) asec_seq) asec_seq). *)

  Theorem CEPFromCoeffListInv :
    forall (p : CEPPoly),
      eq_CEPPoly (CEPFromCoeffList (coeffListFromCEP p)) p.
  Proof.
    unfold eq_CEPPoly.
    intros.
    rewrite CEPFromCoeffListCoeff.
    rewrite coeffListFromCEPCoeff.
    reflexivity.
  Qed.
   (* unfold coeffListFromCEP.
    rewrite removeLeadingZerosCoeffListEquiv.
    unfold CEPFromCoeffList.
    unfold canonicalize.
    induction p using
      (well_founded_induction
         (wf_inverse_image _ nat _ get_max_degree
            PeanoNat.Nat.lt_wf_0)).
    unfold coeffListFromCEP.
    rewrite removeLeadingZerosCoeffListEquiv.
    unfold CEPFromCoeffList.
    destruct (PeanoNat.Nat.eq_dec (get_max_degree p) 0).
    - apply canonicalizeDegreeZero in e.
      rewrite e.
      simpl.
      rewrite (canonicalize_pres p) at 2.
      rewrite e.
      reflexivity.
    - pose proof n.
      apply canonicalizeDegreeSn in H0.
      rewrite H0.
      simpl.
      specialize (H (remove_degrees_ge_n p (get_max_degree p))).
      rewrite eq_CEPPoly_rev.
      rewrite CEPFromCoeffListApp.
      simpl.
      rewrite PeanoNat.Nat.add_0_r.
      rewrite <- eq_CEPPoly_rev.
      rewrite rev_app_distr.
      simpl.
      rewrite rev_length.
      enough (length (coeffListFromCEPHelp (canonicalize (remove_degrees_ge_n p (get_max_degree p)))) = get_max_degree p).
      + rewrite H1.
        rewrite (canonicalize_pres p) at 6.
        rewrite H0.
        apply eq_CEPPoly_cons.
        rewrite <- canonicalize_pres at 2.
        rewrite <- H at 2.
        unfold coeffListFromCEP.
        rewrite removeLeadingZerosCoeffListEquiv.
        f_equiv.
        give_up.
      + unfold coeffListFromCEPHelp.
        
      unfold CEPFromCoeffList in H.
  Qed.*)

  Theorem depElimProp (P : CEPPoly -> Prop)
    `(proper : Proper _ (eq_CEPPoly ==> iff) P)
    (X : forall (l : list nat) (proof : noLeadingZeros l), P (depConstr l proof))
    (p : CEPPoly) :
    P p.
  Proof.
    rewrite <- CEPFromCoeffListInv.
    apply (X (coeffListFromCEP p) (coeffListFromCEPNoLeadingZeros p)).
  Qed.

  (*Theorem CoeffListFromCEPInv :
    forall (l : list nat),
      coeffListFromCEP (CEPFromCoeffList l) = l.
  Proof.
    unfold eq_CEPPoly.
    intros.
    rewrite CEPFromCoeffListCoeff.
    rewrite coeffListFromCEPCoeff.
    reflexivity.
  Qed.*)

  Theorem coeffListCanonical (l : list nat) (proof : noLeadingZeros l) :
    removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize (depConstr l proof)))) = l.
  Proof.
    unfold depConstr.
    unfold canonicalize.
    enough
      (forall (n : nat) (l : list nat),
        (coeffListFromCEPHelp (canonicalize (CEPFromCoeffList (n :: l))) =
        (n :: (coeffListFromCEPHelp (canonicalize (CEPFromCoeffList l)))))).
    induction l.
    - reflexivity.
    - unfold depConstr.
      unfold CEPFromCoeffList.
      simpl.
      rewrite CEPFromCoeffListApp.
      rewrite rev_app_distr.
      unfold canonicalize.
      pose proof (proof).
      apply ListFns.noLeadingZerosHeadNonzero in H0.
      destruct a.
      + contradiction.
      + simpl.
      
  Admitted.

  Definition iotaRecEq (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    depRec C X (depConstr l proof) = X l proof.
  Proof.
    unfold depRec.
    unfold coeffListFromCEP.
    pose proof (coeffListCanonical l proof).
    Check coeffListFromCEPNoLeadingZeros.
    assert (eq_rect (removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize (depConstr l proof))))) noLeadingZeros (coeffListFromCEPNoLeadingZeros (depConstr l proof)) l H = proof).
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

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {opaque noLeadingZeros ListFns.addLists ListFns.addListsNoLeadingZeros noLeadingZerosProofIrr ListFns.evalList ListFns.evalListRespectsAddLists opaque_list ListFns.addListsCommNoLeadingZerosProofIrr ListFns.addListsComm}.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.depRec as depRecCEP.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.add as addCEP.

Print CLPoly.add.
Print addCEP.

Instance addCEPProper : Proper (CEPPoly.eq_CEPPoly ==> CEPPoly.eq_CEPPoly ==> CEPPoly.eq_CEPPoly) addCEP.
Proof.
  unfold addCEP.
  intros p1 p2 H0 p3 p4 H1.
  unfold CEPPoly.depConstr.
  unfold depRecCEP.
  unfold CEPPoly.depRec.
  unfold CEPPoly.coeffListFromCEP.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.eval as evalCEP.

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

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.evalRespectsAdd as evalRespectsAddCEP.

Print evalRespectsAddCEP.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.addCommFirstDepElimMotive as addCommFirstDepElimMotiveCEP.

Print addCommFirstDepElimMotiveCEP.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.addCommSecondDepElimMotive as addCommSecondDepElimMotiveCEP.

Print addCommSecondDepElimMotiveCEP.

Instance addCommFirstDepElimMotiveCEPProper (p2 : CEPPoly.CEPPoly) :
  Proper
    (CEPPoly.eq_CEPPoly ==> iff)
    (addCommFirstDepElimMotiveCEP p2).
Proof.
  unfold addCommFirstDepElimMotiveCEP.
  solve_proper.
Qed.

Instance addCommSecondDepElimMotiveCEPProper l proof :
  Proper
    (CEPPoly.eq_CEPPoly ==> iff)
    (addCommSecondDepElimMotiveCEP l proof).
Proof.
  unfold addCommSecondDepElimMotiveCEP.
  solve_proper.
Qed.

Definition addCommFirstDepElimCEP p2 :=
  CEPPoly.depElimProp
    (addCommFirstDepElimMotiveCEP p2)
    (addCommFirstDepElimMotiveCEPProper p2).

Definition addCommSecondDepElimCEP l proof :=
  CEPPoly.depElimProp
    (addCommSecondDepElimMotiveCEP l proof)
    (addCommSecondDepElimMotiveCEPProper l proof).

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {
    constrs_a = CLPoly.depConstr ;
    constrs_b = CEPPoly.depConstr ;
    elim_a = CLPoly.depRec CLPoly.addCommFirstDepElim CLPoly.addCommSecondDepElim ;
    elim_b = CEPPoly.depRec addCommFirstDepElimCEP addCommSecondDepElimCEP ;
    eta_a = etaCLPoly ;
    eta_b = etaCEPPoly ;
    iota_a = CLPoly.iotaRec CLPoly.iotaRecRev ;
    iota_b = CEPPoly.iotaRec CEPPoly.iotaRecRev
  }.

Print CLPoly.addComm.

Definition eq_rect_opaque := eq_rect.

Definition eq_refl_opaque {A : Type} := @eq_refl A.

Definition eq_opaque {A : Type} := @eq A.

Print eq_rect_opaque.

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {opaque eq_rect_opaque eq_refl_opaque}.

Definition test (l l0 : opaque_list) (proof : noLeadingZeros l) (proof0 : noLeadingZeros l0) := eq_rect
                    (eq_rect (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                       (ListFns.addListsNoLeadingZeros l l0 proof proof0) 
                       (ListFns.addLists l0 l) (ListFns.addListsComm l l0))
                    (fun x : noLeadingZeros (ListFns.addLists l0 l) =>
                     CLPoly.eq_CLPoly
                       (CLPoly.depConstr (ListFns.addLists l l0)
                          (ListFns.addListsNoLeadingZeros l l0 proof proof0))
                       (CLPoly.depConstr (ListFns.addLists l0 l) x))
                    (internal_eq_rew_dep (opaque_list) (ListFns.addLists l l0)
                       (fun (a : opaque_list) (e : ListFns.addLists l l0 = a) =>
                        CLPoly.eq_CLPoly
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (ListFns.addListsNoLeadingZeros l l0 proof proof0))
                          (CLPoly.depConstr a
                             (eq_rect_opaque opaque_list (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0) a e)))
                       (reflexivity
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (eq_rect (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0)
                                (ListFns.addLists l l0) eq_refl)))
                       (ListFns.addLists l0 l)
                       (ListFns.addListsComm l l0))
                    (ListFns.addListsNoLeadingZeros l0 l proof0 proof)
                    (ListFns.addListsCommNoLeadingZerosProofIrr l l0 proof proof0).

Lift CLPoly.CLPoly CEPPoly.CEPPoly in test as testCEP.

Print testCEP.

Definition trm l l0 proof proof0 := eq_rect (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0)
                                (ListFns.addLists l l0) eq_refl.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in trm as trmCEP.

Print trmCEP.

Definition trm2 (l : opaque_list) (l0 : opaque_list) (proof : noLeadingZeros l) (proof0 : noLeadingZeros l0) (p : CLPoly.CLPoly) := eq_rect (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0)
                                (ListFns.addLists l l0) eq_refl.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in trm2 as trm2CEP.

Print trm2CEP.

Check trm2.

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {opaque trm internal_eq_rew_dep}.

Definition test2 (l l0 : opaque_list) (proof : noLeadingZeros l) (proof0 : noLeadingZeros l0) :=
internal_eq_rew_dep (opaque_list) (ListFns.addLists l l0)
                       (fun (a : opaque_list) (e : ListFns.addLists l l0 = a) =>
                        CLPoly.eq_CLPoly
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (ListFns.addListsNoLeadingZeros l l0 proof proof0))
                          (CLPoly.depConstr a
                             (eq_rect_opaque opaque_list (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0) a e)))
                       (reflexivity
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (trm l l0 proof proof0)))
                       (ListFns.addLists l0 l)
                       (ListFns.addListsComm l l0).

Print test2.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in test2 as test2CEP.

Print test2CEP.

Print CLPoly.addComm.

Definition test3 (l l0 : opaque_list) (proof : noLeadingZeros l) (proof0 : noLeadingZeros l0) (p : CLPoly.CLPoly) := fun p1 p2 : CLPoly.CLPoly =>
CLPoly.addCommFirstDepElim p2
  (fun (l : opaque_list) (proof : noLeadingZeros l) =>
   CLPoly.addCommSecondDepElim l proof
     (fun (l0 : opaque_list) (proof0 : noLeadingZeros l0) =>
      CLPoly.iotaRecRev CLPoly.CLPoly
        (fun (l1 : opaque_list) (p : noLeadingZeros l1) =>
         CLPoly.depRec CLPoly.CLPoly
           (fun (l2 : opaque_list) (p0 : noLeadingZeros l2) =>
            CLPoly.depConstr (ListFns.addLists l1 l2) (ListFns.addListsNoLeadingZeros l1 l2 p p0))
           (CLPoly.depConstr l0 proof0)) l proof
        (fun c : CLPoly.CLPoly =>
         CLPoly.eq_CLPoly c
           (CLPoly.depRec CLPoly.CLPoly
              (fun (l1 : opaque_list) (p : noLeadingZeros l1) =>
               CLPoly.depRec CLPoly.CLPoly
                 (fun (l2 : opaque_list) (p0 : noLeadingZeros l2) =>
                  CLPoly.depConstr (ListFns.addLists l1 l2)
                    (ListFns.addListsNoLeadingZeros l1 l2 p p0)) (CLPoly.depConstr l proof))
              (CLPoly.depConstr l0 proof0)))
        (CLPoly.iotaRecRev CLPoly.CLPoly
           (fun (l1 : opaque_list) (p0 : noLeadingZeros l1) =>
            CLPoly.depConstr (ListFns.addLists l l1) (ListFns.addListsNoLeadingZeros l l1 proof p0))
           l0 proof0
           (fun c : CLPoly.CLPoly =>
            CLPoly.eq_CLPoly c
              (CLPoly.depRec CLPoly.CLPoly
                 (fun (l1 : opaque_list) (p : noLeadingZeros l1) =>
                  CLPoly.depRec CLPoly.CLPoly
                    (fun (l2 : opaque_list) (p0 : noLeadingZeros l2) =>
                     CLPoly.depConstr (ListFns.addLists l1 l2)
                       (ListFns.addListsNoLeadingZeros l1 l2 p p0)) (CLPoly.depConstr l proof))
                 (CLPoly.depConstr l0 proof0)))
           (CLPoly.iotaRecRev CLPoly.CLPoly
              (fun (l1 : opaque_list) (p : noLeadingZeros l1) =>
               CLPoly.depRec CLPoly.CLPoly
                 (fun (l2 : opaque_list) (p0 : noLeadingZeros l2) =>
                  CLPoly.depConstr (ListFns.addLists l1 l2)
                    (ListFns.addListsNoLeadingZeros l1 l2 p p0)) (CLPoly.depConstr l proof)) l0
              proof0
              (fun c : CLPoly.CLPoly =>
               CLPoly.eq_CLPoly
                 (CLPoly.depConstr (ListFns.addLists l l0)
                    (ListFns.addListsNoLeadingZeros l l0 proof proof0)) c)
              (CLPoly.iotaRecRev CLPoly.CLPoly
                 (fun (l1 : opaque_list) (p0 : noLeadingZeros l1) =>
                  CLPoly.depConstr (ListFns.addLists l0 l1)
                    (ListFns.addListsNoLeadingZeros l0 l1 proof0 p0)) l proof
                 (fun c : CLPoly.CLPoly =>
                  CLPoly.eq_CLPoly
                    (CLPoly.depConstr (ListFns.addLists l l0)
                       (ListFns.addListsNoLeadingZeros l l0 proof proof0)) c)
                 (eq_rect
                    (eq_rect (ListFns.addLists l l0) (fun x : opaque_list => noLeadingZeros x)
                       (ListFns.addListsNoLeadingZeros l l0 proof proof0) 
                       (ListFns.addLists l0 l) (ListFns.addListsComm l l0))
                    (fun x : noLeadingZeros (ListFns.addLists l0 l) =>
                     CLPoly.eq_CLPoly
                       (CLPoly.depConstr (ListFns.addLists l l0)
                          (ListFns.addListsNoLeadingZeros l l0 proof proof0))
                       (CLPoly.depConstr (ListFns.addLists l0 l) x))
                    (internal_eq_rew_dep opaque_list (ListFns.addLists l l0)
                       (fun (a : opaque_list) (e : ListFns.addLists l l0 = a) =>
                        CLPoly.eq_CLPoly
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (ListFns.addListsNoLeadingZeros l l0 proof proof0))
                          (CLPoly.depConstr a
                             (eq_rect (ListFns.addLists l l0)
                                (fun x : opaque_list => noLeadingZeros x)
                                (ListFns.addListsNoLeadingZeros l l0 proof proof0) a e)))
                       (reflexivity
                          (CLPoly.depConstr (ListFns.addLists l l0)
                             (ListFns.addListsNoLeadingZeros l l0 proof proof0))) (ListFns.addLists l0 l)
                       (ListFns.addListsComm l l0))
                    (ListFns.addListsNoLeadingZeros l0 l proof0 proof)
                    (ListFns.addListsCommNoLeadingZerosProofIrr l l0 proof proof0)))))) p2) p1.
                             

Print test3.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in test3 as test3CEP.

Print test3CEP.


(* If we don't set lift type here, the default type of addCommCEP doesn't allow
 * needed rewrites to be performed in comm_once and comm_twice.
 *)
Set DEVOID lift type.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.addComm as addCommCEP.

Print addCommCEP.

Theorem comm_once :
  forall (p1 p2 : CLPoly.CLPoly),
    CLPoly.eq_CLPoly (CLPoly.add p1 p2) (CLPoly.add p2 p1).
Proof.
  intros.
  rewrite_annotate (CLPoly.addComm p1 p2).
  reflexivity.
Qed.

Set Printing All.

Print comm_once.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in comm_once as comm_onceCEP.

Print comm_onceCEP.

Theorem comm_twice :
  forall (p1 p2 p3 : CLPoly.CLPoly),
    CLPoly.eq_CLPoly (CLPoly.add p1 (CLPoly.add p2 p3)) (CLPoly.add (CLPoly.add p3 p2) p1).
Proof.
  intros.
  rewrite_annotate (CLPoly.addComm p2 p3).
  rewrite_annotate (CLPoly.addComm p1 (CLPoly.add p3 p2)).
  reflexivity.
Qed.

Print comm_twice.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in comm_twice as comm_twiceCEP.

Print comm_twiceCEP.

(*fun p1 p2 : CLPoly.CLPoly =>
START_REWRITE (CLPoly.addComm p1 p2) (CLPoly.eq_CLPoly (CLPoly.add p1 p2) (CLPoly.add p2 p1))
  ((fun lemma : CLPoly.eq_CLPoly (CLPoly.add p1 p2) (CLPoly.add p2 p1) =>
    trans_co_eq_inv_impl_morphism CLPoly.eq_CLPoly_trans (CLPoly.add p1 p2) 
      (CLPoly.add p2 p1) lemma (CLPoly.add p2 p1) (CLPoly.add p2 p1)
      (eq_proper_proxy (CLPoly.add p2 p1))) (CLPoly.addComm p1 p2) (reflexivity (CLPoly.add p2 p1)))

fun p1 p2 : CLPoly.CLPoly =>
let H : CLPoly.eq_CLPoly (CLPoly.add p1 p2) (CLPoly.add p2 p1) := CLPoly.addComm p1 p2 in
START_REWRITE H (CLPoly.eq_CLPoly (CLPoly.add p1 p2) (CLPoly.add p2 p1))
  ((fun lemma : CLPoly.eq_CLPoly (CLPoly.add p1 p2) (CLPoly.add p2 p1) =>
    trans_co_eq_inv_impl_morphism CLPoly.eq_CLPoly_trans (CLPoly.add p1 p2) 
      (CLPoly.add p2 p1) lemma (CLPoly.add p2 p1) (CLPoly.add p2 p1)
      (eq_proper_proxy (CLPoly.add p2 p1))) H (reflexivity (CLPoly.add p2 p1)))*)

Theorem sym (p1 p2 : CLPoly.CLPoly) (H : CLPoly.eq_CLPoly p1 p2) : CLPoly.eq_CLPoly p2 p1.
Proof.
  rewrite_annotate H.
  reflexivity.
Qed.

Print sym.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in sym as symCEP.

Print symCEP.

Print reflexivity.
