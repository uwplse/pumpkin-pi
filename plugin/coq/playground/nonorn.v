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
  rewrite IHb. simpl. rewrite Nat.add_comm. auto.
Defined.

Lemma retraction :
  forall (n : nat),
    binnat_to_nat (nat_to_binnat n) = n.
Proof.
  intros n. induction n.
  - auto.
  - simpl. rewrite refold_suc_binnat. f_equal. apply IHn.
Defined.

Lemma refold_suc_nat:
  forall (n : nat), suc_binnat (nat_to_binnat (n + n))   = consOdd (nat_to_binnat n).
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite Nat.add_comm. simpl. rewrite IHn. auto.
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
  - simpl. rewrite H.S_OK. f_equal. apply IHn.
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
  - simpl. simpl in IHn. rewrite Nat.add_comm. simpl.
    rewrite IHn. auto.
Defined.
Program Definition S2_OK :
  forall (n : Datatypes.nat), e.of (Datatypes_S2 n) = S2 (e.of n).
Proof.
  intros n. induction n.
  - auto.
  - simpl. simpl in IHn. rewrite Nat.add_comm. simpl.
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
Lemma bin_natty:
  forall (n : Bin.nat), natty n.
Proof.
  intros n. induction n.
  - constructor.
  - induction IHn.
    + apply (nsuc zero). constructor.
    + apply (nsuc (Bin.S2 n)). apply (nsuc (Bin.S1 n)). apply IHIHn. 
  - induction IHn.
    + apply (nsuc (Bin.S1 Bin.O) (nsuc zero nO)).
    + apply (nsuc (Bin.S1 (Bin.S n))). apply (nsuc (Bin.S2 n)). apply IHIHn.
Defined. 

Program Definition binnat_nat_rect :
  forall (P : Bin.nat -> Type),
    P Bin.O ->
    (forall (n : Bin.nat), P n -> P (Bin.S n)) ->
    forall (n : Bin.nat), P n.
Proof.
  intros P PO PS n. induction (bin_natty n); auto.
Defined.

(*
 * So nice automation would be writing a procedure that determines the
 * algebraic ornament from the equivalence between binnat and nat.
 * Also, what happens to our definitional equalities, here?
 *)

(* --- OK cute. Notes on how to keep playing with this below. --- *)

(* 
 * The key is that we need a way to partition the S case exactly.
 * (So this is not partitioning the natural numbers, but rather partitioning
 * the successor function itself into two parts).
 * Any partition works fine, as long as we can always get back to where we started.
 * What we saw before is that binary numbers are exactly what we get by
 * partitioning the successor function for the natural numbers into even and odd cases.
 * This makes sense because the original nat inductive type acts like a unary nat.
 * I think we could get n-ary nat if we split n times all at once following that
 * pattern, and in a sense, the n-ary numbers induce the n-induction principle.
 *
 * But it would be way more fun to think of some weirder partitions and to partition
 * some other types. So that's what I'll do here next. Then I'll automate both
 * proving this equivalence (with the parameters as user proof obligations) and
 * lifting proofs across it.
 *
 * Are there any partitions here besides the mod groups for which you can
 * define a successor function that the equivalence preserves? If so,
 * what are they? I'm not sure. I tried lists and it was useless because
 * I don't understand how to split the cons case. Ugh.
 *)
