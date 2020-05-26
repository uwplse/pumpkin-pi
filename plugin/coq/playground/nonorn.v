Require Import Coq.Program.Tactics.
Require Import PeanoNat.
Require Import Ornamental.Ornaments.

(*
 * This is my first attempt at understanding equivalences that are not ornaments
 * and how they relate to this transformation. I will start with two very easy cases:
 * partitioning constructors and partitioning inductive hypotheses.
 * The idea being that in both cases, the transformation should no longer preserve
 * definitional equalities, so some transformation of rewrites ought to occur.
 * Ornaments are the specific case where this transformation maps refl to refl.
 *)

(* --- Partitioning constructors --- *)

(*
 * This is sort of a minimized version of what we see happen with bin and nat.
 * To do that, we use a definition of binary numbers from Agda:
 * https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda,
 * which is itself from RedPRL:
 * https://github.com/RedPRL/redtt/blob/master/library/cool/nats.red.
 * As they note, this is still not as efficient as the other version,
 * but it's minimal and simple which will help us define this transformation
 * and then generalize what we do. This is all just using their equivalence
 * translated into Coq. We generalize later in this file.
 *)
Inductive binnat :=
| zero : binnat
| consOdd : binnat -> binnat
| consEven : binnat -> binnat.

(*
 * DepConstr:
 *)
Program Definition suc_binnat : binnat -> binnat.
Proof.
  intros b. induction b.
  - apply consOdd. apply zero.
  - apply consEven. apply b.
  - apply consOdd. apply IHb.
Defined. 

(*
 * Equiv:
 *)
Program Definition binnat_to_nat : binnat -> nat.
Proof.
  intros b. induction b.
  - apply 0.
  - apply S. apply (IHb + IHb).
  - apply S. apply S. apply (IHb + IHb).
Defined.

Program Definition nat_to_binnat : nat -> binnat.
Proof.
  intros n. induction n.
  - apply zero.
  - apply suc_binnat. apply IHn.
Defined.

Lemma refold_suc_binnat :
  forall (b : binnat), binnat_to_nat (suc_binnat b) = S (binnat_to_nat b).
Proof.
  intros b. induction b; auto. simpl.
  rewrite IHb. simpl. rewrite <- plus_n_Sm. auto.
Defined.

Lemma retraction :
  forall (n : nat),
    binnat_to_nat (nat_to_binnat n) = n.
Proof.
  intros n. induction n.
  - auto.
  - simpl. rewrite refold_suc_binnat. rewrite IHn. auto.
Defined.

Lemma refold_suc_nat:
  forall (n : nat), suc_binnat (nat_to_binnat (n + n))   = consOdd (nat_to_binnat n).
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite <- plus_n_Sm. simpl. rewrite IHn. auto.
Defined.

Lemma section :
  forall (b : binnat),
    nat_to_binnat (binnat_to_nat b) = b.
Proof.
  intros b. induction b.
  - auto.
  - simpl. rewrite refold_suc_nat. rewrite IHb. reflexivity.
  - simpl. rewrite refold_suc_nat. rewrite IHb. reflexivity.
Defined.

(* --- Partitioning constructors: interface --- *)

(*
 * Let's try to generalize the intuition here.
 *)
Module Type Split.

Definition nat := binnat.
Definition O := zero.
Definition S1 := consOdd.
Definition S2 := consEven.

(*
 * DepConstr:
 *)
Parameter S : nat -> nat.
Parameter Datatypes_S1 : Datatypes.nat -> Datatypes.nat.
Parameter Datatypes_S2 : Datatypes.nat -> Datatypes.nat.

End Split.

Module Split_Equiv (s : Split).

(*
 * Equiv:
 *)
Program Definition to : s.nat -> nat.
Proof.
  intros n. induction n.
  - apply 0.
  - apply s.Datatypes_S1. apply IHn.
  - apply s.Datatypes_S2. apply IHn.
Defined.

Program Definition of : nat -> s.nat.
Proof.
  intros n. induction n.
  - apply s.O.
  - apply s.S. apply IHn.
Defined.

End Split_Equiv.

Module Type Split_Equiv_OK (s : Split).

Module e := Split_Equiv s.

Parameter S_OK :
  forall (n : s.nat), e.to (s.S n) = S (e.to n).

Parameter S1_OK :
  forall (n : nat), e.of (s.Datatypes_S1 n) = s.S1 (e.of n).

Parameter S2_OK :
  forall (n : nat), e.of (s.Datatypes_S2 n) = s.S2 (e.of n).

End Split_Equiv_OK.

Module Split_Equiv_Proof (s : Split) (H : Split_Equiv_OK s).

Lemma retraction :
  forall (n : nat),
    H.e.to (H.e.of n) = n.
Proof.
  intros n. induction n.
  - auto.
  - simpl. rewrite H.S_OK. rewrite IHn. auto.
Defined.

Lemma section :
  forall (n : s.nat),
    H.e.of (H.e.to n) = n.
Proof.
  intros n. induction n.
  - auto.
  - simpl. rewrite H.S1_OK. rewrite IHn. reflexivity.
  - simpl. rewrite H.S2_OK. rewrite IHn. reflexivity.
Defined.

End Split_Equiv_Proof.

(* --- Now we define the above via our interface: --- *)

Module Bin <: Split.

Definition nat := binnat.
Definition O := zero.
Definition S1 := consOdd.
Definition S2 := consEven.

(*
 * DepConstr:
 *)
Definition S := suc_binnat.
Definition Datatypes_S1 (n : Datatypes.nat) := Datatypes.S (n + n).
Definition Datatypes_S2 (n : Datatypes.nat) := Datatypes.S (Datatypes.S (n + n)).

End Bin.

Module e := Split_Equiv Bin.

Module Bin_Equiv_OK <: Split_Equiv_OK Bin.
Module e := e.
Import e Bin.

Definition S_OK := refold_suc_binnat.
Program Definition S1_OK :
  forall (n : Datatypes.nat), e.of (Datatypes_S1 n) = S1 (e.of n).
Proof.
  intros n. induction n.
  - auto.
  - simpl. simpl in IHn. rewrite <- plus_n_Sm. simpl.
    rewrite IHn. auto.
Defined.
Program Definition S2_OK :
  forall (n : Datatypes.nat), e.of (Datatypes_S2 n) = S2 (e.of n).
Proof.
  intros n. induction n.
  - auto.
  - simpl. simpl in IHn. rewrite <- plus_n_Sm. simpl.
    rewrite IHn. auto.
Defined.

End Bin_Equiv_OK.

Module Bin_Equiv_Proof := Split_Equiv_Proof Bin Bin_Equiv_OK.

(*
 * Here's our dependent eliminator, but to get there we convert to nats first:
 *)
Definition dep_elim_via_nat_rect (P : Bin.nat -> Type) (PO : P Bin.O)
    (PS : forall n : Bin.nat, P n -> P (Bin.S n)) (n : Bin.nat) : P n :=
  eq_rect
    (nat_to_binnat (binnat_to_nat n))
    (fun n0 : binnat => P n0)
    (nat_rect
      (fun m0 : nat =>
        forall n0 : Bin.nat, m0 = binnat_to_nat n0 -> P (nat_to_binnat m0))
      (fun (n0 : Bin.nat) (_ : 0 = binnat_to_nat n0) => PO)
      (fun (m0 : nat) (IHm : forall n0 : Bin.nat, m0 = binnat_to_nat n0 -> P (nat_to_binnat m0))
           (n0 : Bin.nat) (Heqm0 : S m0 = binnat_to_nat n0) =>
        PS (nat_to_binnat m0) (IHm (nat_to_binnat (pred (binnat_to_nat n0)))
           (eq_ind_r (fun n1 : nat => m0 = n1)
              (eq_ind (S m0) (fun n1 : nat => m0 = pred n1) eq_refl
                 (binnat_to_nat n0) Heqm0)
              (retraction (pred (binnat_to_nat n0))))))
      (binnat_to_nat n)
      n
      eq_refl)
    n
    (section n).

(*
 * I assume there is a way to do this without inducting over nats by cleverly
 * manipulating the motive. How so, though? argh.
 *
 * Ah, Conor McBride wrote an epic poem about this, as always:
 * https://personal.cis.strath.ac.uk/conor.mcbride/pub/1Song/Song.pdf
 *
 * For now we'll use the last construction from that paper, since it's the easiest.
 * (Conor credits McKinna for this one)
 *)
Inductive natty : Bin.nat -> Type :=
| nO : natty Bin.O
| nsuc : forall (n : Bin.nat), natty n -> natty (Bin.S n).

(*
 * Hey cute, this is an algebraic ornament of nat. Actually, more than cute.
 * This really connects everything together.
 *)

Set DEVOID search prove equivalence.
Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.
Set DEVOID lift type.

(*
 * So nice automation would be writing a procedure that determines the
 * algebraic ornament from the equivalence between binnat and nat.
 * Also, what happens to our definitional equalities, here?
 * They are preserved between nat and natty. But I'm guessing what breaks them
 * is the conversion from bin to natty!
 *
 * Also note that what we get here is over { b : Bin.nat & natty b }.
 * To get proofs over Bin.nat from proofs over nat, we want to swap in
 * binnat_nat_rect for nat_rect, then take care of the appropriate
 * equalities. The algorithm should take care of that part.
 *
 * When we go from proofs over nat to proofs over Bin.nat, we will want
 * something similar in the opposite direction.
 *)

(*
 * What are our identities, now? First let's lift our equality proofs from nat
 * along the algebraic ornament.
 *)
Preprocess Module e as e'
  { opaque
      binnat_rect binnat_rec binnat_ind
      Coq.Init.Datatypes.nat_ind Coq.Init.Datatypes.nat_rect Coq.Init.Datatypes.nat_rec
      Coq.Init.Logic.eq_ind Coq.Init.Logic.eq_ind_r Coq.Init.Logic.eq_sym
      Bin.nat
  }.
Preprocess Module Bin_Equiv_OK as Bin_Equiv_OK'
  { opaque
      binnat_rect binnat_rec binnat_ind
      Coq.Init.Datatypes.nat_ind Coq.Init.Datatypes.nat_rect Coq.Init.Datatypes.nat_rec
      Coq.Init.Logic.eq_ind Coq.Init.Logic.eq_ind_r Coq.Init.Logic.eq_sym
      Bin.nat
  }.
Preprocess Module Bin_Equiv_Proof as Bin_Equiv_Proof'
  { opaque
      binnat_rect binnat_rec binnat_ind
      Coq.Init.Datatypes.nat_ind Coq.Init.Datatypes.nat_rect Coq.Init.Datatypes.nat_rec
      Coq.Init.Logic.eq_ind Coq.Init.Logic.eq_ind_r Coq.Init.Logic.eq_sym
      Bin.nat
  }.
Lift Module nat natty in e' as Natty_Equiv.
Lift Module nat natty in Bin_Equiv_OK' as Natty_Equiv_OK.
Lift Module nat natty in Bin_Equiv_Proof' as Natty_Equiv_Proof.

(*
 * To get bin_natty, we'll want proofs over indexed natty first
 *)
Module indexed.

  Definition binnat_to_natty (b : Bin.nat) : { n : sigT natty & projT1 n = b } :=
    existT _ (Natty_Equiv.to b) (eq_rect (projT1 (Natty_Equiv.to b)) (fun b0 => projT1 (Natty_Equiv.to b) = b0) eq_refl b (Natty_Equiv_Proof.section b)).

End indexed.

Print Natty_Equiv_OK.Top_binnat_to_nat.
Definition packed b := {n : sigT natty & projT1 n = b}.
Lift Module packed natty in Natty_Equiv as Natty_Indexed_Equiv.
Lift Module packed natty in Natty_Equiv_OK as Natty_Indexed_Equiv_OK.
Lift Module packed natty in Natty_Equiv_Proof as Natty_Indexed_Proof.
Lift Module packed natty in indexed as Natty_Indexed.

(*
 * This gives us bin_natty:
 *)
Definition bin_natty (n : Bin.nat) : natty n :=
   Natty_Indexed.binnat_to_natty n.

Program Definition binnat_nat_rect :
  forall (P : Bin.nat -> Type),
    P Bin.O ->
    (forall (n : Bin.nat), P n -> P (Bin.S n)) ->
    forall (n : Bin.nat), P n.
Proof.
  intros P PO PS n. induction (bin_natty n); auto.
Defined.

Definition id_eta (n : Bin.nat) : Bin.nat := n.

(*
 * dep_elim is OK:
 *)
Lemma dep_elim_OK :
  forall (n : Bin.nat) (f : forall (n : Bin.nat), n = n),
    binnat_nat_rect (fun n => n = n) (f Bin.O) (fun n _ => f (Bin.S n)) n = f (id_eta n).
Proof.
  unfold id_eta. intros n f. unfold binnat_nat_rect. induction (bin_natty n); auto.
Defined.

(*
 * Showing our eliminator is OK is harder, so I'm going to prove a bunch
 * of lemmas here.
 *)

Definition elim_id (b : Bin.nat) :=
  binnat_nat_rect
   (fun _ => Bin.nat)
   Bin.O
   (fun _ IH => Bin.S IH)
   b.

Lemma elim_id_id:
  forall b,
    b = elim_id b.
Proof.
  intros b. unfold elim_id. unfold binnat_nat_rect.
  induction (bin_natty b); auto.
  simpl. f_equal. apply IHn.
Defined.

(*
 * Where this differs from ornaments is that this is no longer
 * reflexivity.
 *)
Lemma rew_S:
  forall b,
    elim_id (Bin.S b) = Bin.S (elim_id b).
Proof.
  intros b. rewrite <- elim_id_id. f_equal. apply elim_id_id. 
Defined. 

(*
 * I can't find a way to prove refold_elim_S without UIP_dec, so if we need
 * this property to hold too, we might need our types to be H-sets.
 *)
Lemma bin_dec:
  forall x y : Bin.nat, {x = y} + {x <> y}.
Proof.
  intros x. induction x; induction y; auto; try (right; discriminate);
  induction (IHx y); try (rewrite a; auto);
  right; unfold not; intros; apply b; inversion H; auto. 
Defined.

Require Import Arith.

Lemma suc_S:
  forall (b : Bin.nat) (n : sigT natty)
         (H : projT1 n = b),
    @eq_rect
      _
      (Bin.S (projT1 n))
      natty
      (nsuc (projT1 n) (projT2 n))
      (Bin.S b)
      (f_equal Bin.S H) =
    nsuc
      b
      (@eq_rect
        _
        (projT1 n)
        natty
        (projT2 n)
        b
        H).
Proof.
  intros. induction n. rewrite <- H. reflexivity.
Defined.   

Lemma bin_natty_suc :
  forall (b : Bin.nat),
    bin_natty (Bin.S b) = nsuc b (bin_natty b).
Proof.
  intros b. unfold bin_natty. unfold Natty_Indexed.binnat_to_natty.
  rewrite <- suc_S; auto.
  symmetry. eapply eq_trans.
  - apply (f_equal (fun n => eq_rect _ _ n _ _) (eq_sym (projT2_eq (Natty_Equiv_OK.S_OK b)))).
  - rewrite <- eq_trans_rew_distr. f_equal. apply Eqdep_dec.UIP_dec. apply bin_dec. 
Defined.

Lemma refold_elim_S:
  forall P PO PS n,
    binnat_nat_rect P PO PS (Bin.S n) = 
    PS n (binnat_nat_rect P PO PS n).
Proof.
  intros. unfold binnat_nat_rect. rewrite bin_natty_suc.
  auto.
Defined.

(* --- OK cute. Notes on how to keep playing with this below. --- *)

(*
 * For now let's focus not on partitions in particular, but on
 * providing the equalities we need manually. Let's see how we can
 * port proofs using those. Let's start manually with a few proofs
 * on natural numbers. 
 *
 * We already have addition preprocessed and lifted to natty, so it's
 * a nice starting example.
 *)

Definition add := e'.Coq_Init_Nat_add.
Definition natty_add := Natty_Equiv_Proof.Coq_Init_Nat_add.

(*
 * How would we port addition to use binnat_nat_rect?
 * Naively:
 *)
Definition binnat_add (b1 : Bin.nat) (b2 : Bin.nat) :=
  binnat_nat_rect
    (fun _ : Bin.nat => Bin.nat -> Bin.nat)
    (fun b2 : Bin.nat => b2)
    (fun (_ : Bin.nat) (add : Bin.nat -> Bin.nat) (b2 : Bin.nat) =>
      Bin.S (add b2))
    b1
    b2.

(*
 * Now what happens when we port proofs? Let's look at plus_n_Sm:
 *)
Definition plus_n_Sm := Bin_Equiv_Proof'.Coq_Init_Peano_plus_n_Sm.
Definition natty_plus_n_Sm := Natty_Equiv_Proof.Coq_Init_Peano_plus_n_Sm.

(*
 * Naively:
 *)
Fail Definition binnat_plus_n_Sm (n m : Bin.nat) :=
  binnat_nat_rect
    (fun n0 : Bin.nat =>
       Bin.S (binnat_add n0 m) =
       binnat_add n0 (Bin.S m))
    eq_refl
    (fun (n0 : Bin.nat) (IHn : Bin.S (binnat_add n0 m) = binnat_add n0 (Bin.S m)) =>
       f_equal Bin.S IHn)
    n.

(*
 * Here the equality problem shows up:
 *
 * In environment
 *   n m n0 : Bin.nat
 *   IHn : Bin.S (binnat_add n0 m) = binnat_add n0 (Bin.S m)
 * The term 
 *   f_equal Bin.S IHn
 * has type
 *   Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))
 * while it is expected to have type
 *   Bin.S (binnat_add (Bin.S n0) m) = binnat_add (Bin.S n0) (Bin.S m)
 *)

(*
 * What would we need to fix this?
 * The inductive argument of add is the first argument.
 * We need to show it preserves the successor case.
 * For nats, this holds reflexively, but for binnats,
 * we need to be more clever. This is easy with refold_elim_S.
 *)
Lemma binnat_plus_Sn_m:
  forall (n0 m : Bin.nat),
    Bin.S (binnat_add n0 m) = binnat_add (Bin.S n0) m.
Proof.
  intros. unfold binnat_add. rewrite refold_elim_S. reflexivity.
Defined.
(*
 * Immediately after porting add, we want to generate the proof of this lemma.
 *)

Lemma transport_IH:
  forall (n0 m : Bin.nat),
    Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m)) ->
    Bin.S (binnat_add (Bin.S n0) m) = binnat_add (Bin.S n0) (Bin.S m).
Proof.
  intros. rewrite <- binnat_plus_Sn_m. rewrite <- binnat_plus_Sn_m.
  apply H.
Defined.

(*
 * Then:
 *)
Definition binnat_plus_n_Sm (n m : Bin.nat) :=
  binnat_nat_rect
    (fun n0 : Bin.nat =>
       Bin.S (binnat_add n0 m) =
       binnat_add n0 (Bin.S m))
    eq_refl
    (fun (n0 : Bin.nat) (IHn : Bin.S (binnat_add n0 m) = binnat_add n0 (Bin.S m)) =>
       transport_IH n0 m (f_equal Bin.S IHn))
    n.

(*
 * We need to figure out where there are implicit uses of eq_refl,
 * so we can figure out where to use binnat_plus_Sn_m.
 * Over nats we have this subterm, expanded:
 *)
Definition f_equal_IH (n0 m : nat) (IHn : S (add n0 m) = add n0 (S m)) : S (S (add n0 m)) = S (add n0 (S m)) :=
  @f_equal
    nat
    nat
    (fun (n : nat) => S n)
    (S (add n0 m))
    (add n0 (S m))
    IHn.

(*
 * Actually, what's interesting here is that over binnats this term can be defined OK:
 *)
Definition f_equal_binnat_IH (n0 m : Bin.nat) (IHn : Bin.S (binnat_add n0 m) = binnat_add n0 (Bin.S m)) : Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m)) :=
  @f_equal
    Bin.nat
    Bin.nat
    (fun (n : Bin.nat) => Bin.S n)
    (Bin.S (binnat_add n0 m))
    (binnat_add n0 (Bin.S m))
    IHn.
(*
 * But the catch is that over nats, the type:
 *   S (S (add n0 m)) = S (add n0 (S m))
 * that Coq infers for this term is definitionally equal to the type:
 *   S (add (S n0) m) = add (S n0) (S m)
 * that the inductive case of our proof expects.
 * In contrast, these types do not unify over binnat.
 *
 * Interestingly, if we fully expand the nat proof, we see the casts:
 *)
Definition plus_n_Sm_expanded (n m : nat) : S (add n m) = add n (S m) :=
  nat_ind
    (fun (n0 : nat) =>
       S (add n0 m) = add n0 (S m))
    (@eq_refl nat (S m) : (S (add O m)) = (add O (S m)))
    (fun (n0 : nat) (IHn : (S (add n0 m)) = (add n0 (S m))) =>
       @f_equal
         nat
         nat
         (fun (n : nat) => S n)
         (S (add n0 m))
         (add n0 (S m))
         IHn
      : (* <-- Check it out! The cast! *)
        (S (add (S n0) m)) = (add (S n0) (S m)))
     n.

(*
 * So we can cast in the nat case:
 *)
Definition f_equal_IH_cast (n0 m : nat) (IHn : S (add n0 m) = add n0 (S m)) : (S (add (S n0) m)) = (add (S n0) (S m)) :=
  f_equal_IH n0 m IHn.

(*
 * But note in the binnat case:
 *)
Fail Definition f_equal_binnat_IH_cast (n0 m : Bin.nat) (IHn : Bin.S (binnat_add n0 m) = binnat_add n0 (Bin.S m)) : (Bin.S (binnat_add (Bin.S n0) m)) = (binnat_add (Bin.S n0) (Bin.S m)) :=
  f_equal_binnat_IH n0 m IHn.

(*
 * What are the semantics of casting? If t : T, and we cast t to some T', then
 * we are saying that eq_refl T : T = T'. So over nats, our claim is that:
 *)
Definition cast_nat_OK (n0 m : nat) : (S (S (add n0 m)) = S (add n0 (S m))) = ((S (add (S n0) m)) = (add (S n0) (S m))) :=
  @eq_refl Prop (S (S (add n0 m)) = S (add n0 (S m))).

(*
 * Transporting this to binnats naively would not work:
 *)
Fail Definition cast_binnat_OK (n0 m : Bin.nat) : (Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))) = ((Bin.S (binnat_add (Bin.S n0) m)) = (binnat_add (Bin.S n0) (Bin.S m))) :=
  @eq_refl Prop (Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))).

(*
 * On the other hand:
 *)
Definition cast_binnat_OK (n0 m : Bin.nat) : (Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))) = ((Bin.S (binnat_add (Bin.S n0) m)) = (binnat_add (Bin.S n0) (Bin.S m))) :=
  eq_rect
    (Bin.S (binnat_add n0 m))
    (fun b : Bin.nat =>
      (Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))) =
      (Bin.S b = binnat_add (Bin.S n0) (Bin.S m)))
    (eq_rect
      (Bin.S (binnat_add n0 (Bin.S m)))
      (fun b : binnat =>
        (Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))) =
        (Bin.S (Bin.S (binnat_add n0 m)) = b))
      (@eq_refl Prop (Bin.S (Bin.S (binnat_add n0 m)) = Bin.S (binnat_add n0 (Bin.S m))))
      (binnat_add (Bin.S n0) (Bin.S m))
      (binnat_plus_Sn_m n0 (Bin.S m)))
    (binnat_add (Bin.S n0) m)
    (binnat_plus_Sn_m n0 m).

(* --- What happens when we don't have an h-set? --- *)

(*
 * I don't know yet. I need to see if we can prove a variant of refold_elim_S.
 * Lists might be a good case study.
 *)

