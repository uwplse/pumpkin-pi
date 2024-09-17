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
Require Import Coq.Logic.Decidable.

(*
 * This file defines two representations of polynomials.
 * The first is as a list of its coefficients, with the head 
 * being the highest degree term, and the second being a list
 * of pairs of a coefficient and the exponent of that coefficient.
 * Both of these types are setoids with equivalence relations 
 * different from equality.
 *)

(*
 * First, we define several functions over lists.
 *)

Module ListFns.

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
    unfold UIP_.
    unfold UIP_on_.
    apply UIP_nat.
  Qed.

  (* 
   * Here, we define a term opaque_list. Because we need to use
   * lists both as a setoid and with equality, we need to distinguish these
   * for Pumpkin Pi. To do this, we define functions and theorems over lists
   * using this opaque_list type, and tell Pumpkin Pi to treat this type and 
   * those functions and theorems as opaque. Then, it won't attempt to lift
   * them to the target setoid.
   *)

  Definition opaque_list := list nat.

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
  
End ListFns.



Module CLPoly.

  Import ListFns.

  (*
   * Here is our first setoid. We define the type of lists of natural numbers.
   * The list [an ; a(n-1) ; ... ; a0] represents the polynomial 
   * an * x^n + a(n-1) * x^(n-1) + ... + a0. Each polynomial has multiple representations
   * by appending any number of 0s to the front of the list. To account for this
   * we define an equivalence relation saying that two representations are equivalent
   * if they are equal after removing any leading 0s.
   *)

  Definition CLPoly := list nat.

  Definition eq_CLPoly (l1 l2 : CLPoly) :=
    removeLeadingZeros l1 = removeLeadingZeros l2.

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

  (*
   * Now, we begin defining the elements of the configuration.
   * Our configuration needs to be based on an inductive type, but in this
   * case our source type is a setoid. We base our configuration on the
   * inductive type {l : list nat | noLeadingZeros l}. We then need to 
   * write our functions on CLPoly in terms of the elements of this configuration.
   *)
  
  Definition depConstr (l : opaque_list) (p : noLeadingZeros l) : CLPoly := l.

  (* We define a canonical element for each class of equivalent CLPolys. *)
  
  Definition canonicalize (l : CLPoly) :=
    removeLeadingZeros l.

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

  (* 
   * Now that the configuration is defined, we define functions and theorems
   * based off of the configuration.
   *)
    
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

  (*
   * The below theorems need to use depElimProp. To enable repair, we specialize depElimProp
   * with a motive and a proof that the motive is proper before we apply it in our theorems.
   *)

  Definition evalRespectsAddFirstMotive (p2 : CLPoly) (n : nat) :=
    (fun p => eval (add p p2) n = eval p n + eval p2 n).

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

End CLPoly.



Module CEPPoly.

  Import ListFns.

  (*
   * Here is our secondc setoid. We define the type of lists of pairs natural numbers.
   * The list [(an, expn) ; (a(n-1), exp(n-1) ; ... ; (a0, exp0)] represents the 
   * polynomial an * x^expn + a(n-1) * x^exp^(n-1) + ... + a0 * x^exp0. 
   * Each polynomial has multiple representations, since we allow for repeated exponents.
   * To account for this we define an equivalence relation saying that two representations 
   * are equivalent if their coefficients of the same degree sum to the same number.
   *)

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

  (* To define the configuration, we first prove a number of helper theorems. *)

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

  Theorem get_max_degree_non_zero (l : CEPPoly) :
    get_max_degree l > 0 -> coeff l (get_max_degree l) <> 0.
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
          rewrite PeanoNat.Nat.eqb_refl.
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
          rewrite PeanoNat.Nat.eqb_refl in H.
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

  Definition coeffPairsToN (p : CEPPoly) (n : nat) :=
    map (fun x => (coeff p x, x)) (seq 0 (S n)).

  Theorem seqEndSn : forall n m,
      seq m (S n) = (seq m n) ++ [m + n].
  Proof.
    induction n.
    - intros.
      rewrite PeanoNat.Nat.add_0_r.
      reflexivity.
    - intros.
      assert (seq m (S (S n)) = m :: (seq (S m) (S n))).
      reflexivity.
      rewrite H.
      rewrite IHn.
      simpl.
      repeat f_equal.
      lia.
  Qed.

  Theorem elim_canonicalize :
    forall p n,
      canonicalize_help [] p n = coeffPairsToN p n.
  Proof.
    unfold coeffPairsToN.
    intros.
    rewrite seqEndSn.
    rewrite map_app.
    simpl.
    induction n.
    - reflexivity.
    - rewrite seqEndSn.
      rewrite map_app.
      simpl.
      rewrite <- IHn.
      rewrite <- acc_always_contained_at_end_help_eq.
      reflexivity.
  Qed.

  Theorem coeffGreaterThanMaxDegree (p : CEPPoly) (exp : nat) :
    get_max_degree p < exp -> coeff p exp = 0.
  Proof.
    apply contrapositive.
    apply PeanoNat.Nat.eq_decidable.
    intros.
    pose proof (get_max_degree_complete p exp).
    apply H1 in H.
    lia.
  Qed.

  Theorem coeffListFromCEPCoeff :
    forall (p : CEPPoly) (exp : nat),
      coeff p exp = nth exp (rev (coeffListFromCEP p)) 0.
  Proof.
    unfold coeffListFromCEP.
    unfold canonicalize.
    intros.
    rewrite elim_canonicalize.
    rewrite removeLeadingZerosnth.
    unfold coeffListFromCEPHelp.
    rewrite map_rev.
    rewrite rev_involutive.
    unfold coeffPairsToN.
    rewrite map_map.
    enough (coeff p (S (get_max_degree p)) = 0).
    - rewrite <- H at 2.
      rewrite map_nth.
      destruct (PeanoNat.Nat.le_decidable exp (get_max_degree p)).
      + rewrite seq_nth.
        simpl.
        reflexivity.
        lia.
      + assert (get_max_degree p < exp) by lia.
        rewrite nth_overflow.
        simpl.
        rewrite H.
        apply coeffGreaterThanMaxDegree.
        apply H1.
        rewrite seq_length.
        lia.
    - apply coeffGreaterThanMaxDegree.
      lia.
  Qed.

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

  Theorem max_degree_bounded_by_exps :
    forall (p : CEPPoly) (bound : nat),
      ((forall (c exp : nat), In (c, exp) p -> exp <= bound) -> get_max_degree p <= bound).
  Proof.
    induction p.
    - intros.
      simpl.
      lia.
    - intros.
      destruct a.
      assert (In (n, n0) ((n, n0) :: p)).
      + simpl.
        left.
        reflexivity.
      + pose proof (H n n0 H0).
        simpl.
        destruct n.
        * apply IHp.
          intros.
          apply (in_cons (0, n0)) in H2.
          apply H in H2.
          apply H2.
        * apply PeanoNat.Nat.max_lub; auto.
          apply IHp.
          intros.
          apply (in_cons (S n, n0)) in H2.
          apply (H _ _ H2).
  Qed.

  Theorem CEPFromCoeffListDegreesLessThanLength :
    forall (l : list nat),
      (forall (c exp : nat), In (c, exp) (CEPFromCoeffListHelp (rev l) 0) -> S exp <= length l).
  Proof.
    induction l.
    - intros.
      simpl in H.
      contradiction.
    - intros.
      simpl in H.
      rewrite CEPFromCoeffListApp in H.
      apply in_app_or in H.
      destruct H.
      + specialize (IHl _ _ H).
        simpl.
        lia.
      + simpl in H.
        destruct H; try contradiction.
        inversion H.
        rewrite rev_length.
        simpl.
        lia.
  Qed.

  Theorem maxDegreeCEPFromCoeffListLength :
    forall (l : list nat),
      l = [] \/
        (noLeadingZeros l ->
           S (get_max_degree (CEPFromCoeffList l)) = length l).
  Proof.
    Print get_max_degree.
    intros.
    destruct l.
    - left.
      reflexivity.
    - unfold CEPFromCoeffList.
      right.     
      intros.
      rewrite (eq_maxDegreeSame (rev (CEPFromCoeffListHelp (rev (n :: l)) 0)) (CEPFromCoeffListHelp (rev (n :: l)) 0)).
      enough (S (get_max_degree (CEPFromCoeffListHelp (rev (n :: l)) 0)) >= length (n :: l) /\
              S (get_max_degree (CEPFromCoeffListHelp (rev (n :: l)) 0)) <= length (n :: l)).
      + destruct H0.
        lia.
      + split.
        * simpl.
          rewrite CEPFromCoeffListApp.
          simpl.
          rewrite PeanoNat.Nat.add_0_r.
          rewrite (eq_maxDegreeSame (CEPFromCoeffListHelp (rev l) 0 ++ [(n, length (rev l))])
                     ([(n, length (rev l))] ++ CEPFromCoeffListHelp (rev l) 0)).
          -- rewrite rev_length.
             apply ListFns.noLeadingZerosHeadNonzero in H.
             pose proof (get_max_degree_head (CEPFromCoeffListHelp (rev l) 0) n (length l) H).
             unfold ge.
             simpl.
             simpl in H0.
             lia.
          -- apply eq_CEPPoly_app_comm.
        * pose proof (max_degree_bounded_by_exps (CEPFromCoeffListHelp (rev (n :: l)) 0)).
          pose proof (CEPFromCoeffListDegreesLessThanLength (n ::l)).
          simpl.
          apply Le.le_n_S.
          apply H0.
          intros.
          specialize (H1 c exp H2).
          simpl in H1.
          lia.
      + apply eq_CEPPoly_rev.
  Qed.

  Theorem coeffListCanonicalHelp :
    forall (l : list nat),
      rev (map (fun x : nat => nth x (rev l) 0) (seq 0 (length l))) = l.
  Proof.
    induction l.
    - reflexivity.
    - assert (length (a :: l) = S (length l)) by reflexivity.
      rewrite H.
      rewrite seqEndSn.
      rewrite <- map_rev.
      rewrite rev_app_distr.
      simpl.
      rewrite app_nth2 by (rewrite rev_length; lia).
      rewrite rev_length.
      rewrite PeanoNat.Nat.sub_diag.
      simpl.
      f_equal.
      rewrite map_rev.
      enough (map (fun x : nat => nth x (rev l ++ [a]) 0) (seq 0 (length l)) = map (fun x : nat => nth x (rev l) 0) (seq 0 (length l))).
      + rewrite H0.
        apply IHl.
      + apply map_ext_in.
        intros.
        rewrite in_seq in H0.
        simpl in H0.
        rewrite app_nth1.
        * reflexivity.
        * rewrite rev_length.
          apply H0.
  Qed.

  (*
   * Now, we define the configuration, again based off of 
   * {l : list nat | noLeadingZeros l}.
   *)

  Definition depConstr (l : list nat) (p : noLeadingZeros l) := CEPFromCoeffList l.

  Definition depRec (C : Type) (X : forall (l : list nat) (p : noLeadingZeros l), C) (p : CEPPoly) : C :=
    X (coeffListFromCEP p) (coeffListFromCEPNoLeadingZeros p).

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

  Theorem depElimProp (P : CEPPoly -> Prop)
    `(proper : Proper _ (eq_CEPPoly ==> iff) P)
    (X : forall (l : list nat) (proof : noLeadingZeros l), P (depConstr l proof))
    (p : CEPPoly) :
    P p.
  Proof.
    rewrite <- CEPFromCoeffListInv.
    apply (X (coeffListFromCEP p) (coeffListFromCEPNoLeadingZeros p)).
  Qed.

  Theorem coeffListCanonical (l : list nat) (proof : noLeadingZeros l) :
    removeLeadingZeros (coeffListFromCEPHelp (rev (canonicalize (depConstr l proof)))) = l.
  Proof.
    unfold depConstr.
    unfold canonicalize.
    rewrite elim_canonicalize.
    unfold coeffListFromCEPHelp.
    unfold coeffPairsToN.
    rewrite map_rev.
    rewrite map_map.
    pose proof (maxDegreeCEPFromCoeffListLength l).
    destruct H.
    - rewrite H.
      reflexivity.
    - specialize (H proof).
      rewrite H.
      simpl.
      rewrite (map_ext (fun x => coeff (CEPFromCoeffList l) x) (fun x => nth x (rev l) 0) (CEPFromCoeffListCoeff l)).
      rewrite coeffListCanonicalHelp.
      symmetry.
      apply proof.
  Qed.

  Definition iotaRecEq (C : Type)
    (X : forall (l : list nat) (p : noLeadingZeros l), C)
    (l : list nat) (proof : noLeadingZeros l) :
    depRec C X (depConstr l proof) = X l proof.
  Proof.
    unfold depRec.
    unfold coeffListFromCEP.
    pose proof (coeffListCanonical l proof).
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

(* 
 * The lift type option makes Pumpkin Pi lift the types of terms as well as 
 * the terms themselves. If we don't set lift type, the default type of 
 * addCommCEP doesn't allow needed rewrites to be performed in 
 * comm_once and comm_twice.
 *)

Set DEVOID lift type.

(*
 * We define p and f, as well as etaCLPoly and etaCEPPoly, 
 * which are part of the required input for the tool.
 *) 

Definition p (p : CLPoly.CLPoly) := CLPoly.depRec CEPPoly.CEPPoly (fun l proof => CEPPoly.CEPFromCoeffList l) p.

Definition f (p : CEPPoly.CEPPoly) := CEPPoly.depRec CLPoly.CLPoly (fun l proof => CLPoly.depConstr (CEPPoly.coeffListFromCEP p) (CEPPoly.coeffListFromCEPNoLeadingZeros p)) p.

(* 
 * Here, we configure Pumpkin Pi to lift our setoids. We pass CLPoly.CLPoly to types_a,
 * CLPoly.eq_CLPoly to rels_a, and CLPoly.eq_CLPoly_equiv to equiv_proofs_a to define
 * CLPoly.CLPoly as a setoid with equivalence relation CLPoly.eq_CLPoly. Likewise,
 * we pass CEPPoly.CEPPoly to types_b, CEPPoly.eq_CEPPoly to rels_b, and 
 * CEPPoly.eq_CEPPoly_equiv to equiv_proofs_b to define CEPPoly.CEPPoly as a setoid 
 * with equivalence relation CEPPoly.eq_CEPPoly. Pumpkin Pi will then repair 
 * CLPoly.eq_CLPoly as CEPPoly.eq_CEPPoly when repairing terms.
 *)

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

(*
 * Here, we make opaque_list, as well as some functions and theorems over it,
 * opaque, so that Pumpkin Pi will not repair them.
 *)

Configure Lift CLPoly.CLPoly CEPPoly.CEPPoly {opaque ListFns.noLeadingZeros ListFns.addLists ListFns.addListsNoLeadingZeros ListFns.noLeadingZerosProofIrr ListFns.evalList ListFns.evalListRespectsAddLists ListFns.opaque_list ListFns.addListsCommNoLeadingZerosProofIrr ListFns.addListsComm}.

(* 
 * We lift CLPoly.depRec, which prevents Pumpkin Pi from unfolding 
 * its definition in lifted terms. This helps with proper proof 
 * generation.
 *)

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.depRec as depRecCEP.

(* Now, we repair our functions. *)

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.add as addCEP.

Print addCEP.

(* 
 * Pumpkin Pi fails to automatically generate a proof that addCEP is proper,
 * so we prove it manually.
 *)

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

(*
 * Now, we repair our theorems. Because they use depElimProp, we need to
 * specialize CEPPoly.depElimProp to use lifted versions of the motives
 * of the CLPoly.depElimProp instances in the source term, as well as a 
 * proof that those instances are proper. We could generate those proper proofs,
 * but because we define these motives at the top level, the motives we define
 * take arguments for terms that would be in scope in the original term. Thus,
 * the generated proper proofs don't have the right type, and we need to prove
 * our own. If Pumpkin Pi automatically lifted depElimProps, it could generate
 * the proper proofs in the context they would appear in, preventing this 
 * hiccup.
 *)

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.evalRespectsAddFirstMotive as evalRespectsAddFirstMotiveCEP.

Print evalRespectsAddFirstMotiveCEP.

Theorem evalRespectsAddFirstCEPProperGoal (p2 : CEPPoly.CEPPoly) (n : nat) :
  Proper (CEPPoly.eq_CEPPoly ==> iff) (evalRespectsAddFirstMotiveCEP p2 n).
Proof.
  unfold evalRespectsAddFirstMotiveCEP.
  solve_proper2.
Qed.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.evalRespectsAddSecondMotive as evalRespectsAddSecondMotiveCEP.

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

(* Now, we lift CLPoly.addComm. *)

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

Lift CLPoly.CLPoly CEPPoly.CEPPoly in CLPoly.addComm as addCommCEP.

Print addCommCEP.

(*
 * None of the above theorems used setoid rewriting in their proofs.
 * Thus, to demonstrate repair of setoid writing, we quickly prove
 * some simple theorems using setoid rewriting, and then repair them.
 * Notice the use of rewrite_annotate, which is a tactic that 
 * automatically annotates rewrites in proofs.
 *)

Theorem comm_once :
  forall (p1 p2 p3 p4 : CLPoly.CLPoly),
    CLPoly.eq_CLPoly
      (CLPoly.add (CLPoly.add p3 p4) (CLPoly.add p1 p2))
      (CLPoly.add (CLPoly.add p3 p4) (CLPoly.add p2 p1)).
Proof.
  intros.
  rewrite_annotate (CLPoly.addComm p1 p2).
  reflexivity.
Qed.

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

Theorem sym (p1 p2 : CLPoly.CLPoly) (H : CLPoly.eq_CLPoly p1 p2) : CLPoly.eq_CLPoly p2 p1.
Proof.
  rewrite_annotate H.
  reflexivity.
Qed.

Print sym.

Lift CLPoly.CLPoly CEPPoly.CEPPoly in sym as symCEP.

Print symCEP.
