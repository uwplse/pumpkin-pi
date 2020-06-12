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

Module e.

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

(* eta problems with f_equal_nat in the original version *)

Lemma add_n_Sm : forall n m : nat, S (n + m) = n + S m.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Defined.

Lemma refold_suc_binnat :
  forall (b : binnat), binnat_to_nat (suc_binnat b) = S (binnat_to_nat b).
Proof.
  intros b. induction b; auto. simpl.
  rewrite IHb. simpl. rewrite <- add_n_Sm. auto.
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
  - simpl. rewrite <- add_n_Sm. simpl. rewrite IHn. auto.
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

End e.

(* --- Now we define the above via our interface: --- *)

Definition S1 := consOdd.
Definition S2 := consEven.

(*
 * DepConstr:
 *)
Definition S := e.suc_binnat.
Definition Datatypes_S1 (n : Datatypes.nat) := Datatypes.S (n + n).
Definition Datatypes_S2 (n : Datatypes.nat) := Datatypes.S (Datatypes.S (n + n)).

(*
 * DepElim:
 *
 * I assume there is a way to do this without inducting over nats by cleverly
 * manipulating the motive. How so, though? argh.
 *
 * Ah, Conor McBride wrote an epic poem about this, as always:
 * https://personal.cis.strath.ac.uk/conor.mcbride/pub/1Song/Song.pdf
 *
 * For now we'll use the last construction from that paper, since it's the easiest.
 * (Conor credits McKinna for this one)
 *)
Inductive natty : binnat -> Type :=
| nO : natty zero
| nsuc : forall (n : binnat), natty n -> natty (e.suc_binnat n).

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
 * Also note that what we get here is over { b : binnat & natty b }.
 * To get proofs over binnat from proofs over nat, we want to swap in
 * binnat_nat_rect for nat_rect, then take care of the appropriate
 * equalities. The algorithm should take care of that part.
 *
 * When we go from proofs over nat to proofs over binnat, we will want
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
      Coq.Init.Logic.eq_rect Coq.Init.Logic.eq_rect_r 
      Coq.Init.Logic.f_equal
  }.
Lift Module nat natty in e' as Natty_Equiv.

(*
 * To get bin_natty, we'll want proofs over indexed natty first
 *)
Module indexed.

  Definition binnat_to_natty (b : binnat) : { n : sigT natty & projT1 n = b } :=
    existT _ (Natty_Equiv.binnat_to_nat b) (eq_rect (projT1 (Natty_Equiv.binnat_to_nat b)) (fun b0 => projT1 (Natty_Equiv.binnat_to_nat b) = b0) eq_refl b (Natty_Equiv.section b)).

End indexed.

Definition packed b := {n : sigT natty & projT1 n = b}.
Lift Module packed natty in Natty_Equiv as Natty_Indexed_Equiv.
Lift Module packed natty in indexed as Natty_Indexed.

(*
 * This gives us bin_natty:
 *)
Definition bin_natty (n : binnat) : natty n :=
   Natty_Indexed.binnat_to_natty n.

Program Definition binnat_nat_rect :
  forall (P : binnat -> Type),
    P zero ->
    (forall (n : binnat), P n -> P (e.suc_binnat n)) ->
    forall (n : binnat), P n.
Proof.
  intros P PO PS n. induction (bin_natty n); auto.
Defined.

Definition id_eta (n : binnat) : binnat := n.

(*
 * dep_elim is OK:
 *)
Lemma dep_elim_OK :
  forall (n : binnat) (f : forall (n : binnat), n = n),
    binnat_nat_rect (fun n => n = n) (f zero) (fun n _ => f (e.suc_binnat n)) n = f (id_eta n).
Proof.
  unfold id_eta. intros n f. unfold binnat_nat_rect. induction (bin_natty n); auto.
Defined.

(*
 * Showing our eliminator is OK is harder, so I'm going to prove a bunch
 * of lemmas here.
 *)

Definition elim_id (b : binnat) :=
  binnat_nat_rect
   (fun _ => binnat)
   zero
   (fun _ IH => e.suc_binnat IH)
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
    elim_id (e.suc_binnat b) = e.suc_binnat (elim_id b).
Proof.
  intros b. rewrite <- elim_id_id. f_equal. apply elim_id_id. 
Defined. 

(*
 * John has managed to prove refold_elim_S without UIP_dec, but I don't know how yet
 *)
Lemma bin_dec:
  forall x y : binnat, {x = y} + {x <> y}.
Proof.
  intros x. induction x; induction y; auto; try (right; discriminate);
  induction (IHx y); try (rewrite a; auto);
  right; unfold not; intros; apply b; inversion H; auto. 
Defined.

Lemma suc_S:
  forall (b : binnat) (n : sigT natty)
         (H : projT1 n = b),
    @eq_rect
      _
      (e.suc_binnat (projT1 n))
      natty
      (nsuc (projT1 n) (projT2 n))
      (e.suc_binnat b)
      (f_equal e.suc_binnat H) =
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

Require Import Arith.

Lemma bin_natty_suc :
  forall (b : binnat),
    bin_natty (e.suc_binnat b) = nsuc b (bin_natty b).
Proof.
  intros b. unfold bin_natty. unfold Natty_Indexed.binnat_to_natty.
  rewrite <- suc_S; auto.
  symmetry. eapply eq_trans.
  - apply (f_equal (fun n => eq_rect _ _ n _ _) (eq_sym (projT2_eq (Natty_Equiv.refold_suc_binnat b)))).
  - rewrite <- eq_trans_rew_distr. f_equal. apply Eqdep_dec.UIP_dec. apply bin_dec. 
Defined.

Lemma refold_elim_S:
  forall P PO PS n,
    binnat_nat_rect P PO PS (e.suc_binnat n) = 
    PS n (binnat_nat_rect P PO PS n).
Proof.
  intros. unfold binnat_nat_rect. rewrite bin_natty_suc.
  auto.
Defined.

(* --- OK cute. Notes on how to keep playing with this below. --- *)

(*
 * We already have addition preprocessed and lifted to natty, so it's
 * a nice starting example.
 *)

Definition add := e'.Coq_Init_Nat_add.
Definition natty_add := Natty_Equiv.Coq_Init_Nat_add.

(*
 * How would we port addition to use binnat_nat_rect?
 * Naively:
 *)
Definition binnat_add (b1 : binnat) (b2 : binnat) :=
  binnat_nat_rect
    (fun _ : binnat => binnat -> binnat)
    (fun b2 : binnat => b2)
    (fun (_ : binnat) (add : binnat -> binnat) (b2 : binnat) =>
      e.suc_binnat (add b2))
    b1
    b2.

(*
 * Now what happens when we port proofs? Let's look at plus_n_Sm:
 *)
Definition plus_n_Sm := e'.add_n_Sm.
Definition natty_plus_n_Sm := Natty_Equiv.add_n_Sm.

(*
 * Naively:
 *)
Fail Definition binnat_plus_n_Sm (n m : binnat) :=
  binnat_nat_rect
    (fun n0 : binnat =>
       e.suc_binnat (binnat_add n0 m) =
       binnat_add n0 (e.suc_binnat m))
    eq_refl
    (fun (n0 : binnat) (IHn : e.suc_binnat (binnat_add n0 m) = binnat_add n0 (e.suc_binnat m)) =>
       eq_ind
         (e.suc_binnat (binnat_add n0 m))
         (fun (n1 : binnat) =>
           e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat n1)
         eq_refl
         (binnat_add n0 (e.suc_binnat m))
         IHn)
    n.

(*
 * Here the equality problem shows up.
 *
 * What would we need to fix this?
 * The inductive argument of add is the first argument.
 * We need to show it preserves the successor case.
 * For nats, this holds reflexively, but for binnats,
 * we need to be more clever. This is easy with refold_elim_S.
 *)
Lemma binnat_plus_Sn_m:
  forall (n0 m : binnat),
    e.suc_binnat (binnat_add n0 m) = binnat_add (e.suc_binnat n0) m.
Proof.
  intros. unfold binnat_add. rewrite refold_elim_S. reflexivity.
Defined.
(*
 * Immediately after porting add, we want to generate the proof of this lemma.
 *)

Lemma transport_IH:
  forall (n0 m : binnat),
    e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m)) ->
    e.suc_binnat (binnat_add (e.suc_binnat n0) m) = binnat_add (e.suc_binnat n0) (e.suc_binnat m).
Proof.
  intros. rewrite <- binnat_plus_Sn_m. rewrite <- binnat_plus_Sn_m.
  apply H.
Defined.

(*
 * Then:
 *)
Definition binnat_plus_n_Sm (n m : binnat) :=
  binnat_nat_rect
    (fun n0 : binnat =>
       e.suc_binnat (binnat_add n0 m) =
       binnat_add n0 (e.suc_binnat m))
    eq_refl
    (fun (n0 : binnat) (IHn : e.suc_binnat (binnat_add n0 m) = binnat_add n0 (e.suc_binnat m)) =>
      transport_IH n0 m
      (eq_ind
        (e.suc_binnat (binnat_add n0 m))
        (fun (n1 : binnat) =>
          e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat n1)
        eq_refl
        (binnat_add n0 (e.suc_binnat m))
        IHn))
    n.
  

(*
 * We need to figure out where there are implicit uses of eq_refl,
 * so we can figure out where to use binnat_plus_Sn_m.
 * Over nats we have this subterm, expanded:
 *)
Definition f_equal_IH (n0 m : nat) (IHn : Datatypes.S (add n0 m) = add n0 (Datatypes.S m)) : Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m)) :=
  eq_ind (Datatypes.S (e'.Coq_Init_Nat_add n0 m))
     (fun n1 : nat =>
      Datatypes.S (Datatypes.S (e'.Coq_Init_Nat_add n0 m)) = Datatypes.S n1)
     eq_refl (e'.Coq_Init_Nat_add n0 (Datatypes.S m)) IHn.

(*
 * Actually, what's interesting here is that over binnats this term can be defined OK.
 * But the catch is that over nats, the type:
 *   S (S (add n0 m)) = S (add n0 (S m))
 * that Coq infers for this term is definitionally equal to the type:
 *   S (add (S n0) m) = add (S n0) (S m)
 * that the inductive case of our proof expects.
 * In contrast, these types do not unify over binnat.
 *
 * Interestingly, if we fully expand the nat proof, we see the casts
 * in the inductive case. What are the semantics of casting? If t : T, and we cast t to some T', then
 * we are saying that eq_refl T : T = T'. So over nats, our claim is that:
 *)
Definition cast_nat_OK (n0 m : nat) : (Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m))) = ((Datatypes.S (add (Datatypes.S n0) m)) = (add (Datatypes.S n0) (Datatypes.S m))) :=
  @eq_refl Prop (Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m))).

(*
 * Transporting this to binnats naively would not work:
 *)
Fail Definition cast_binnat_OK (n0 m : binnat) : (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m))) = ((e.suc_binnat (binnat_add (e.suc_binnat n0) m)) = (binnat_add (e.suc_binnat n0) (e.suc_binnat m))) :=
  @eq_refl Prop (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m))).

(*
 * On the other hand:
 *)
Definition cast_binnat_OK (n0 m : binnat) : (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m))) = ((e.suc_binnat (binnat_add (e.suc_binnat n0) m)) = (binnat_add (e.suc_binnat n0) (e.suc_binnat m))) :=
  eq_rect
    (e.suc_binnat (binnat_add n0 m))
    (fun b : binnat =>
      (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m))) =
      (e.suc_binnat b = binnat_add (e.suc_binnat n0) (e.suc_binnat m)))
    (eq_rect
      (e.suc_binnat (binnat_add n0 (e.suc_binnat m)))
      (fun b : binnat =>
        (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m))) =
        (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = b))
      (@eq_refl Prop (e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat (binnat_add n0 (e.suc_binnat m))))
      (binnat_add (e.suc_binnat n0) (e.suc_binnat m))
      (binnat_plus_Sn_m n0 (e.suc_binnat m)))
    (binnat_add (e.suc_binnat n0) m)
    (binnat_plus_Sn_m n0 m).

(*
 * Another way of thinking about casted refl is that we are
 * implicitly rewriting with reflexivity:
 *)
Definition cast_nat_OK_rew (n0 m : nat) : (Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m))) = ((Datatypes.S (add (Datatypes.S n0) m)) = (add (Datatypes.S n0) (Datatypes.S m))) :=
  eq_rect
    (Datatypes.S (add n0 m))
    (fun n : nat =>
      (Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m))) =
      (Datatypes.S n = add (Datatypes.S n0) (Datatypes.S m)))
    (eq_rect
      (Datatypes.S (add n0 (Datatypes.S m)))
      (fun n : nat =>
        (Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m))) =
        (Datatypes.S (Datatypes.S (add n0 m)) = n))
      (@eq_refl Prop (Datatypes.S (Datatypes.S (add n0 m)) = Datatypes.S (add n0 (Datatypes.S m))))
      (add (Datatypes.S n0) (Datatypes.S m))
      (@eq_refl nat (Datatypes.S (add n0 (Datatypes.S m))))) (* <-- first refl *)
    (add (Datatypes.S n0) m)
    (@eq_refl nat (Datatypes.S (add n0 m))). (* <-- second refl *)

(*
 * Thus, every refl proof that does not lift correctly can be viewed as a contracted
 * rewrite. The first difficult step is figuring out how to expand our input term
 * to include these. For now, let's assume this occurs in a seperate step as part
 * of requiring fully expanded terms. We want every equality to be expanded with explicit
 * refl over successors of eliminators and eliminators of successors.
 * We'll need automation to do that expansion at some point. But it is orthogonal
 * to lifting itself. (I actually think in a language without casting, these
 * rewrites would maybe have to show up?) Once we have that, we can lift rewrites.
 * We lift every:
 *)
Definition rew_S_add (P : nat -> Type) (n m : nat) (H : P (Datatypes.S (add n m))) : P (add (Datatypes.S n) m) :=
  eq_rect
    (Datatypes.S (add n m))
    (fun n : nat => P n)
    H
    (add (Datatypes.S n) m)
    (@eq_refl nat (Datatypes.S (add n m))).
(*
 * to:
 *)
Definition rew_bin_S_add (P : binnat -> Type) (n m : binnat) (H : P (e.suc_binnat (binnat_add n m))) : P (binnat_add (e.suc_binnat n) m) :=
  eq_rect
    (e.suc_binnat (binnat_add n m))
    (fun n : binnat => P n)
    H
    (binnat_add (e.suc_binnat n) m)
    (binnat_plus_Sn_m n m).
(*
 * and every:
 *)
Definition rew_add_S (P : nat -> Type) (n m : nat) (H : P (add (Datatypes.S n) m)) : P (Datatypes.S (add n m)) :=
  eq_rect
    (add (Datatypes.S n) m)
    (fun n : nat => P n)
    H
    (Datatypes.S (add n m))
    (@eq_refl nat (add (Datatypes.S n) m)).
(*
 * to:
 *)
Definition rew_bin_add_S (P : binnat -> Type) (n m : binnat) (H : P (binnat_add (e.suc_binnat n) m)) : P (e.suc_binnat (binnat_add n m)) :=
  eq_rect
    (binnat_add (e.suc_binnat n) m)
    (fun n : binnat => P n)
    H
    (e.suc_binnat (binnat_add n m))
    (eq_sym (binnat_plus_Sn_m n m)).

(*
 * We can generate these based on every induction.
 * If we generalize by our proof: 
 *)
Definition rew_S_elim (P : nat -> Type) PO PS n (Q : P (Datatypes.S n) -> Type) (H : Q (PS n (nat_rect P PO PS n))) : Q (nat_rect P PO PS (Datatypes.S n)) :=
  eq_rect
    (PS n (nat_rect P PO PS n))
    (fun (H : P (Datatypes.S n)) => Q H)
    H
    (nat_rect P PO PS (Datatypes.S n))
    (@eq_refl (P (Datatypes.S n)) (PS n (nat_rect P PO PS n))).

Definition rew_binnat_S_elim (P : binnat -> Type) PO PS n (Q : P (e.suc_binnat n) -> Type) (H : Q (PS n (binnat_nat_rect P PO PS n))) : Q (binnat_nat_rect P PO PS (e.suc_binnat n)) :=
  eq_rect
    (PS n (binnat_nat_rect P PO PS n))
    (fun (H : P (e.suc_binnat n)) => Q H)
    H
    (binnat_nat_rect P PO PS (e.suc_binnat n))
    (eq_sym (refold_elim_S P PO PS n)).

Definition rew_elim_S (P : nat -> Type) PO PS n (Q : P (Datatypes.S n) -> Type) (H : Q (nat_rect P PO PS (Datatypes.S n))) : Q (PS n (nat_rect P PO PS n)) :=
  eq_rect
    (nat_rect P PO PS (Datatypes.S n))
    (fun (H : P (Datatypes.S n)) => Q H)
    H
    (PS n (nat_rect P PO PS n))
    (@eq_refl (P (Datatypes.S n)) (nat_rect P PO PS (Datatypes.S n))).

Definition rew_binnat_elim_S (P : binnat -> Type) PO PS n (Q : P (e.suc_binnat n) -> Type) (H : Q (binnat_nat_rect P PO PS (e.suc_binnat n))) : Q (PS n (binnat_nat_rect P PO PS n)) :=
  eq_rect
    (binnat_nat_rect P PO PS (e.suc_binnat n))
    (fun (H : P (e.suc_binnat n)) => Q H)
    H
    (PS n (binnat_nat_rect P PO PS n))
    (refold_elim_S P PO PS n).

(*
 * Thus, the expanded plus_n_Sm is:
 *)
Definition plus_n_Sm_expanded_rewrites (n m : nat) : Datatypes.S (add n m) = add n (Datatypes.S m) :=
  nat_rect
    (fun (n0 : nat) =>
       Datatypes.S (add n0 m) = add n0 (Datatypes.S m))
    (@eq_refl nat (Datatypes.S m) : (Datatypes.S (add O m)) = (add O (Datatypes.S m)))
    (fun (n0 : nat) (IHn : (Datatypes.S (add n0 m)) = (add n0 (Datatypes.S m))) =>
       rew_S_elim
         (fun _ => nat -> nat)
         (fun p => p)
         (fun _ IH p => Datatypes.S (IH p))
         n0
         (fun PS => Datatypes.S (PS m) = add (Datatypes.S n0) (Datatypes.S m))
         (rew_S_elim
           (fun _ => nat -> nat)
           (fun p => p)
           (fun _ IH p => Datatypes.S (IH p))
           n0
           (fun PS => Datatypes.S (Datatypes.S (add n0 m)) = PS (Datatypes.S m))
           (eq_ind (Datatypes.S (e'.Coq_Init_Nat_add n0 m))
     (fun n1 : nat =>
      Datatypes.S (Datatypes.S (e'.Coq_Init_Nat_add n0 m)) = Datatypes.S n1)
     eq_refl (e'.Coq_Init_Nat_add n0 (Datatypes.S m)) IHn)))
     n.

Definition plus_n_Sm_binnat_expanded_rewrites (n m : binnat) : e.suc_binnat (binnat_add n m) = binnat_add n (e.suc_binnat m) :=
  binnat_nat_rect
    (fun (n0 : binnat) =>
       e.suc_binnat (binnat_add n0 m) = binnat_add n0 (e.suc_binnat m))
    (@eq_refl binnat (e.suc_binnat m) : (e.suc_binnat (binnat_add zero m)) = (binnat_add zero (e.suc_binnat m)))
    (fun (n0 : binnat) (IHn : (e.suc_binnat (binnat_add n0 m)) = (binnat_add n0 (e.suc_binnat m))) =>
       rew_binnat_S_elim
         (fun _ => binnat -> binnat)
         (fun p => p)
         (fun _ IH p => e.suc_binnat (IH p))
         n0
         (fun PS => e.suc_binnat (PS m) = binnat_add (e.suc_binnat n0) (e.suc_binnat m))
         (rew_binnat_S_elim
           (fun _ => binnat -> binnat)
           (fun p => p)
           (fun _ IH p => e.suc_binnat (IH p))
           n0
           (fun PS => e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = PS (e.suc_binnat m))
           (eq_ind
        (e.suc_binnat (binnat_add n0 m))
        (fun (n1 : binnat) =>
          e.suc_binnat (e.suc_binnat (binnat_add n0 m)) = e.suc_binnat n1)
        eq_refl
        (binnat_add n0 (e.suc_binnat m))
        IHn)))
     n.

(* --- What happens when we have a type equivalent to equality? --- *)

(*
 * We want to make sure we're not specializing too much.
 * Perhaps we want our eliminator over equality (and other types indexed by our type)
 * to lift to an elimiantor that does this extra work.
 * I can't immediately think of what this would be.
 *)

(* --- What happens when we don't have an h-set? --- *)

(*
 * I don't know yet. I need to see if we can prove a variant of refold_elim_S.
 * Lists might be a good case study.
 *
 * John managed to prove refold_elim_S without using the fact
 * that bin is an hset.
 *)

(* --- Let's start playing with the implemented commands --- *)

Definition O := O.
Definition nat_S := Datatypes.S.
Definition id_eta_nat (n : nat) : nat := n.
Definition z := zero.

Definition rew_S_elim_2_typ :=
forall (P : nat -> Type) (PO : P O) (PS : forall x : nat, P x -> P (nat_S x)) 
         (n : nat) (Q : P (nat_S n) -> Type),
       Q (PS n (nat_rect P PO PS n)) -> Q (nat_rect P PO PS (nat_S n)).

Definition rew_S_elim2 :=
  (fun (P : nat -> Type) (PO : P O) (PS : forall n, P n -> P (nat_S n)) n (Q : P (nat_S n) -> Type) (H : Q (PS n (nat_rect P PO PS n))) =>
   eq_rect
    (PS n (nat_rect P PO PS n))
    (fun (H : P (nat_S n)) => Q H)
    H
    (nat_rect P PO PS (nat_S n))
    (@eq_refl (P (nat_S n)) (PS n (nat_rect P PO PS n)))) : rew_S_elim_2_typ.

Definition rew_binnat_S_elim_2_typ :=
  forall (P : binnat -> Type) (PO : P z) (PS : forall x : binnat, P x -> P (e.suc_binnat x)) 
         (n : binnat) (Q : P (e.suc_binnat n) -> Type),
       Q (PS n (binnat_nat_rect P PO PS n)) -> Q (binnat_nat_rect P PO PS (e.suc_binnat n)).

Definition rew_binnat_S_elim2  :=
  (fun (P : binnat -> Type) (PO : P z) (PS : forall b, P b -> P (S b)) n (Q : P (e.suc_binnat n) -> Type) (H : Q (PS n (binnat_nat_rect P PO PS n))) =>
  eq_rect
    (PS n (binnat_nat_rect P PO PS n))
    (fun (H : P (e.suc_binnat n)) => Q H)
    H
    (binnat_nat_rect P PO PS (e.suc_binnat n))
    (eq_sym (refold_elim_S P PO PS n))) : rew_binnat_S_elim_2_typ.

(* TODO may be multiple rew_etas for different constructors? fix *)
Save equivalence nat binnat { promote = e.nat_to_binnat; forget = e.binnat_to_nat }.
Configure Lift nat binnat {
  constrs_a = O nat_S;
  constrs_b = z e.suc_binnat;
  elim_a = nat_rect;
  elim_b = binnat_nat_rect;
  id_eta_a = id_eta_nat;
  id_eta_b = id_eta;
  rew_eta_a = rew_S_elim2;
  rew_eta_b = rew_binnat_S_elim2
}.

(* Basic tests *)
Lift nat binnat in O as O_lifted.
Lift nat binnat in nat_S as S_lifted.
Lift binnat nat in z as Bin_O_lifted.
Lift binnat nat in e.suc_binnat as Bin_S_lifted.

Definition add2 (n m : nat) : nat :=
nat_rect (fun _ : nat => nat -> nat) (fun m : nat => m)
  (fun (_ : nat) (add : nat -> nat) (m : nat) => nat_S (add m)) n m.

Lift nat binnat in add2 as binnat_add2.

Definition f_equal_term (m : nat) (n0 : nat) (IHn : (nat_S (add2 n0 m)) = (add2 n0 (nat_S m))) :=
  @f_equal
             nat
             nat
             (fun (n : nat) => nat_S n)
             (nat_S (add2 n0 m))
             (add2 n0 (nat_S m))
             IHn.

Configure Lift nat binnat {
  opaque f_equal eq_rect (* TODO make rew_S_elim opaque automatically? and why is the fact that it's cached not triggering? *)
}.

Lift nat binnat in f_equal_term as f_equal_term_binnat.

Lift nat binnat in rew_S_elim_2_typ as rew_S_elim_2_typ_lifted. 
Lemma foo:
  rew_binnat_S_elim_2_typ =
  rew_S_elim_2_typ_lifted.
Proof.
  reflexivity.
Defined.

Lift nat binnat in rew_S_elim2 as rew_S_elim_lifted.

(* TODO There is some evar map bug if we don't prove foo. investigate *)

Definition inner_term (m : nat) (n0 : nat) (IHn : (nat_S (add2 n0 m)) = (add2 n0 (nat_S m))) :=
(rew_S_elim2
           (fun _ => nat -> nat)
           (fun p => p)
           (fun _ IH p => nat_S (IH p))
           n0
           (fun PS => nat_S (nat_S (add2 n0 m)) = PS (nat_S m))
           (f_equal_term m n0 IHn)).

Lift nat binnat in inner_term as inner_term_lifted.


Definition plus_n_Sm_expanded_rewrites2_inductive (m : nat) 
  (n0 : nat) (IHn : (nat_S (add2 n0 m)) = (add2 n0 (nat_S m))) :=
       rew_S_elim2
         (fun _ => nat -> nat)
         (fun p => p)
         (fun _ IH p => nat_S (IH p))
         n0
         (fun PS => nat_S (PS m) = add2 (nat_S n0) (nat_S m))
         (inner_term m n0 IHn).

(* TODO why broken? *)
Lift nat binnat in plus_n_Sm_expanded_rewrites2_inductive as binnat_plus_n_Sm_expanded_rewrites2_inductive.

Definition plus_n_Sm_expanded_rewrites2 (n m : nat) : nat_S (add2 n m) = add2 n (nat_S m) :=
  nat_rect
    (fun (n0 : nat) =>
       nat_S (add2 n0 m) = add2 n0 (nat_S m))
    (@eq_refl nat (nat_S m))
    (fun (n0 : nat) (IHn : (nat_S (add2 n0 m)) = (add2 n0 (nat_S m))) =>
       plus_n_Sm_expanded_rewrites2_inductive m n0 IHn)
     n.


Lift nat binnat in plus_n_Sm_expanded_rewrites2 as binnat_plus_n_Sm_expanded_rewrites2.

Print binnat_plus_n_Sm_expanded_rewrites2.

Print O_lifted.
Print S_lifted.
Print Bin_O_lifted.
Print Bin_S_lifted.