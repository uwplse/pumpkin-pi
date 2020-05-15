Require Import Coq.Program.Tactics.
Require Import PeanoNat.

(*
 * This is my first attempt at understanding equivalences that are not ornaments
 * and how they relate to this transformation. I will start with two very easy cases:
 * splitting constructors along some decidable disjunction, and splitting inductive
 * hypotheses along some decidable disjunction. The idea being that in both cases,
 * the transformation should no longer preserve definitional equalities, so some
 * transformation of rewrites ought to occur. Ornaments are the specific case where
 * this transformation maps refl to refl.
 *)

(* --- Splitting constructors --- *)

(*
 * This is sort of a minimized version of what we see happen with bin and nat.
 * To do that, we use a definition of binary numbers from Agda:
 * https://github.com/agda/cubical/blob/master/Cubical/Data/BinNat/BinNat.agda.
 * As they note, this is still not as efficient as the other version,
 * but it's minimal and simple which will help us define this transformation
 * and then generalize what we do.
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
  forall (n : nat), suc_binnat (nat_to_binnat (n + n)) = consOdd (nat_to_binnat n).
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

(*
 * Now left is to abstract what they were doing in this.
 * How can we, more generally, derive all of these proofs for any splitting
 * of the cases along some decidable proposition? Find out on the next episode
 * of I'm exhausted and it's Friday.
 *)