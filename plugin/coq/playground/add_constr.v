(*
 * Taking another shot at adding new constructors.
 * 
 * My conclusion: I think it's really cool that we can express adding
 * a constructor as an equivalence, like I suspected.
 * But I'm not trying to fool anyone into thinking the way that I do this
 * is useful yet. It just gives clear path to something useful, separating
 * out the hard work from the easy work. A lot of the other changes we handle,
 * we handle efficiently and usefully. Just being able to do this at all surprised
 * people, so I think it's cute still.
 *)
Require Import List.
Require Import String.
Require Import ZArith.

Import ListNotations.

Require Import Ornamental.Ornaments.
Set CARROT search prove coherence.
Set CARROT search prove equivalence.
Set CARROT lift type.
Set CARROT search smart eliminators.

(*
 * Let's do more of the REPLICA benchmark and see what happens.
 * We start with the swap from Swap.v, then add the bool constructor.
 *
 * This is going to walk through more steps than actually needed long-term,
 * just to show the thought process. For simplicity, we are going to start
 * with just the functions.
 *)

(* --- Original --- *)

Definition Identifier := string.
Definition id_eq_dec := string_dec.

Module Old.

Inductive Term : Set :=
  | Var : Identifier -> Term
  | Int : Z -> Term
  | Eq : Term -> Term -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.

End Old.

Module User5Session19.

Import Old.

Fixpoint identity (t : Term) : Term :=
  match t with
  | Var x => Var x
  | Int i => Int i
  | Eq a b => Eq (identity a) (identity b)
  | Plus a b => Plus (identity a) (identity b)
  | Times a b => Times (identity a) (identity b)
  | Minus a b => Minus (identity a) (identity b)
  | Choose x P => Choose x (identity P)
  end.

Fixpoint free_vars (t : Term) : list Identifier :=
  match t with
  | Var x => [x]
  | Int _ => []
  | Eq a b => free_vars a ++ free_vars b
  | Plus a b => free_vars a ++ free_vars b
  | Times a b => free_vars a ++ free_vars b
  | Minus a b => free_vars a ++ free_vars b
  | Choose x P =>
      filter (fun y => if id_eq_dec x y then false else true) (free_vars P)
  end.

End User5Session19.

Preprocess Module User5Session19 as OldProofs {
  opaque
    Coq.Init.Datatypes Coq.Strings.String Coq.Init.Logic Coq.Lists.List
}.

(* --- Swap --- *)

(*
 * This is the same swap from Swap.v, just one part of the change.
 *)

Module New.

Inductive Term : Set :=
  | Var : Identifier -> Term
  | Eq : Term -> Term -> Term
  | Int : Z -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.

End New.

(* failures below are just redundant attempts at repairing projections *) 
Find ornament Old.Term New.Term { mapping 0 }.
Repair Module Old.Term New.Term in OldProofs as NewProofs.

(* --- Add Bool --- *)

(*
 * OK, now let's extend with Bool.
 *)

Module AddBool.

Inductive Term : Set :=
  | Var : Identifier -> Term
  | Bool : bool -> Term
  | Eq : Term -> Term -> Term
  | Int : Z -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.

End AddBool.

(* --- What's new? --- *)

(*
 * To capture the new information, the first thing we are going to do is split
 * extended AddBool type in half: the left projection and the right projection,
 * essentially. We should be able to produce these automatically, I believe,
 * but for now let's write them manually.
 *)

(*
 * The left projection is straightforward---just use the same structure as
 * the old type, but index by the new type. I think REDACTED NON-AUTHOR 3 said this
 * is the reornament.
 *)
Inductive no_bools : AddBool.Term -> Type :=
| nb1 : forall i, no_bools (AddBool.Var i)
| nb2 : forall t1 t2, no_bools t1 -> no_bools t2 -> no_bools (AddBool.Eq t1 t2)
| nb3 : forall z, no_bools (AddBool.Int z)
| nb4 : forall t1 t2, no_bools t1 -> no_bools t2 -> no_bools (AddBool.Plus t1 t2)
| nb5 : forall t1 t2, no_bools t1 -> no_bools t2 -> no_bools (AddBool.Times t1 t2)
| nb6 : forall t1 t2, no_bools t1 -> no_bools t2 -> no_bools (AddBool.Minus t1 t2)
| nb7 : forall a t, no_bools t -> no_bools (AddBool.Choose a t).

(*
 * The right projection needs to handle the new case, plus all of the inductive
 * cases that may refer to the new case. There is some case explosion here
 * that we will need to make induction useful.
 *)
Inductive yes_bools : AddBool.Term -> Type :=
| yb1 : forall b, yes_bools (AddBool.Bool b)
| yb2left : forall t1, yes_bools t1 -> forall t2 : sigT no_bools, yes_bools (AddBool.Eq t1 (projT1 t2))
| yb2right : forall t1 : sigT no_bools, forall t2, yes_bools t2 -> yes_bools (AddBool.Eq (projT1 t1) t2)
| yb2 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Eq t1 t2)
| yb3left : forall t1, yes_bools t1 -> forall t2 : sigT no_bools, yes_bools (AddBool.Plus t1 (projT1 t2))
| yb3right : forall t1 : sigT no_bools, forall t2, yes_bools t2 -> yes_bools (AddBool.Plus (projT1 t1) t2)
| yb3 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Plus t1 t2)
| yb4left : forall t1, yes_bools t1 -> forall t2 : sigT no_bools, yes_bools (AddBool.Times t1 (projT1 t2))
| yb4right : forall t1 : sigT no_bools, forall t2, yes_bools t2 -> yes_bools (AddBool.Times (projT1 t1) t2)
| yb4 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Times t1 t2)
| yb5left : forall t1, yes_bools t1 -> forall t2 : sigT no_bools, yes_bools (AddBool.Minus t1 (projT1 t2))
| yb5right : forall t1 : sigT no_bools, forall t2, yes_bools t2 -> yes_bools (AddBool.Minus (projT1 t1) t2)
| yb5 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Minus t1 t2)
| yb6 : forall a t, yes_bools t -> yes_bools (AddBool.Choose a t).

(*
 * The idea is that:
 * 1. New.Term is equivalent to sigT no_bools.
 * 2. There exists some non-indexed type Diff that is equivalent to sigT yes_bools.
 * 3. AddBool.Term is equivalent to sigT no_bools + sigT yes_bools.
 * 4. Thus, New.Term + Diff is equivalent to AddBool.Term.
 *
 * We are going to start by finding the ornaments that get us 1 and 2.
 *)

(* --- 1. New.Term is equivalent to sigT no_bools --- *)

(*
 * This is easy.
 * The left projection no_bools is an ornament. So we can easily do this:
 *)
Repair Module New.Term no_bools in NewProofs as NoBoolProofs.
(*
 * This proves the equivalence, and gives us all functions and proofs over
 * sigT no_bools.
 *)

(* --- 2. There exists some non-indexed type Diff that is equivalent to sigT yes_bools --- *)

(*
 * yes_bools must be the reornament of something.
 * We can just go in and remove the index.
 *)
Inductive Diff : Type :=
| DiffBool : bool -> Diff
| DiffEqLeft : Diff -> sigT no_bools -> Diff
| DiffEqRight : sigT no_bools -> Diff -> Diff
| DiffEq : Diff -> Diff -> Diff
| DiffPlusLeft : Diff -> sigT no_bools -> Diff
| DiffPlusRight : sigT no_bools -> Diff -> Diff
| DiffPlus : Diff -> Diff -> Diff
| DiffTimesLeft : Diff -> sigT no_bools -> Diff
| DiffTimesRight : sigT no_bools -> Diff -> Diff
| DiffTimes : Diff -> Diff -> Diff
| DiffMinusLeft : Diff -> sigT no_bools -> Diff
| DiffMinusRight : sigT no_bools -> Diff -> Diff
| DiffMinus : Diff -> Diff -> Diff
| DiffChoose : Identifier -> Diff -> Diff.

(*
 * Let's prove things over diff and port it to yes_bools.
 * For now, we will leave EpsilonLogic alone.
 * We'll deal with that later, since it involves extending a second type.
 * I just want to see what happens to our simple functions.
 *)
Module DiffProofs_fix.

Fixpoint identity (d : Diff) : Diff :=
  match d with
  | DiffBool b => DiffBool b
  | DiffEqLeft t1 t2 => DiffEqLeft (identity t1) (NoBoolProofs.identity t2)
  | DiffEqRight t1 t2 => DiffEqRight (NoBoolProofs.identity t1) (identity t2)
  | DiffEq t1 t2 => DiffEq (identity t1) (identity t2)
  | DiffPlusLeft t1 t2 => DiffPlusLeft (identity t1) (NoBoolProofs.identity t2)
  | DiffPlusRight t1 t2 => DiffPlusRight (NoBoolProofs.identity t1) (identity t2)
  | DiffPlus t1 t2 => DiffPlus (identity t1) (identity t2)
  | DiffTimesLeft t1 t2 => DiffTimesLeft (identity t1) (NoBoolProofs.identity t2)
  | DiffTimesRight t1 t2 => DiffTimesRight (NoBoolProofs.identity t1) (identity t2)
  | DiffTimes t1 t2 => DiffTimes (identity t1) (identity t2)
  | DiffMinusLeft t1 t2 => DiffMinusLeft (identity t1) (NoBoolProofs.identity t2)
  | DiffMinusRight t1 t2 => DiffMinusRight (NoBoolProofs.identity t1) (identity t2)
  | DiffMinus t1 t2 => DiffMinus (identity t1) (identity t2)
  | DiffChoose i t => DiffChoose i (identity t)
  end.

Fixpoint free_vars (d : Diff) : list Identifier :=
  match d with
  | DiffBool b => []
  | DiffEqLeft t1 t2 => free_vars t1 ++ NoBoolProofs.free_vars t2
  | DiffEqRight t1 t2 => NoBoolProofs.free_vars t1 ++ free_vars t2
  | DiffEq t1 t2 => free_vars t1 ++ free_vars t2
  | DiffPlusLeft t1 t2 => free_vars t1 ++ NoBoolProofs.free_vars t2
  | DiffPlusRight t1 t2 => NoBoolProofs.free_vars t1 ++ free_vars t2
  | DiffPlus t1 t2 => free_vars t1 ++ free_vars t2
  | DiffTimesLeft t1 t2 => free_vars t1 ++ NoBoolProofs.free_vars t2
  | DiffTimesRight t1 t2 => NoBoolProofs.free_vars t1 ++ free_vars t2
  | DiffTimes t1 t2 => free_vars t1 ++ free_vars t2
  | DiffMinusLeft t1 t2 => free_vars t1 ++ NoBoolProofs.free_vars t2
  | DiffMinusRight t1 t2 => NoBoolProofs.free_vars t1 ++ free_vars t2
  | DiffMinus t1 t2 => free_vars t1 ++ free_vars t2
  | DiffChoose x t =>
      filter (fun y => if id_eq_dec x y then false else true) (free_vars t)
  end.

End DiffProofs_fix.

Preprocess Module DiffProofs_fix as DiffProofs {
  opaque
    Coq.Init.Datatypes Coq.Strings.String Coq.Init.Logic Coq.Lists.List
}.

(*
 * OK, then we port that to yes_bools:
 *)
Repair Module Diff yes_bools in DiffProofs as YesBoolProofs.
(*
 * Now we have proofs over sigT yes_bools.
 *)

(* --- 3. AddBool.Term is equivalent to sigT no_bools + sigT yes_bools --- *)

(*
 * We'll need a manual configuration for this one.
 * We'll start with a slow eliminator, and think about a fast eliminator later.
 * First we'll need this (should also be easy to automate at some point):
 *)
Lemma split:
  forall (t : AddBool.Term), no_bools t + yes_bools t.
Proof.
  intros. induction t.
  - left. constructor.
  - right. constructor.
  - induction IHt1, IHt2.
    + left. constructor; auto.
    + right. apply (yb2right (existT _ t1 a) t2 y).
    + right. apply (yb2left t1 b (existT _ t2 n)).
    + right. constructor; auto.
  - left. constructor.
  - induction IHt1, IHt2.
    + left. constructor; auto.
    + right. apply (yb3right (existT _ t1 a) t2 y).
    + right. apply (yb3left t1 b (existT _ t2 n)).
    + right. constructor; auto.
  - induction IHt1, IHt2.
    + left. constructor; auto.
    + right. apply (yb4right (existT _ t1 a) t2 y).
    + right. apply (yb4left t1 b (existT _ t2 n)).
    + right. constructor; auto.
  - induction IHt1, IHt2.
    + left. constructor; auto.
    + right. apply (yb5right (existT _ t1 a) t2 y).
    + right. apply (yb5left t1 b (existT _ t2 n)).
    + right. constructor; auto.
  - induction IHt.
    + left. constructor. auto.
    + right. constructor. auto.
Defined.

Lemma split_OK_left:
  forall (t : AddBool.Term) (H : no_bools t),
    inl H = split t.
Proof.
  intros. induction H; auto; simpl.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools. auto.
Defined.

Lemma split_OK_right:
  forall (t : AddBool.Term) (H : yes_bools t),
    inr H = split t.
Proof.
  intros. induction H; auto; simpl.
  - induction t2. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - induction t1. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - induction t2. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - induction t1. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - induction t2. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - induction t1. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - induction t2. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - induction t1. simpl.
    rewrite <- IHyes_bools. rewrite <- split_OK_left with (H := p). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - rewrite <- IHyes_bools. auto.
Defined.

(*
 * Configuration follows easily.
 *)
Definition A : Type := sigT no_bools + sigT yes_bools.
Definition B : Type := AddBool.Term.

Definition dep_constr_A_0 (s : sigT no_bools) : A := inl s.
Definition dep_constr_A_1 (s : sigT yes_bools) : A := inr s.

Definition dep_constr_B_0 (s : sigT no_bools) : B := projT1 s.
Definition dep_constr_B_1 (s : sigT yes_bools) : B := projT1 s.

Definition eta_A (a : A) : A := a.
Definition eta_B (b : B) : B := b.

Program Definition dep_elim_A (P : A -> Type)
  (f0 : forall s, P (dep_constr_A_0 s))
  (f1 : forall s, P (dep_constr_A_1 s))
  (a : A)
: P a.
Proof.
  induction a; auto.
Defined.

Program Definition dep_elim_B (P : B -> Type)
  (f0 : forall s, P (dep_constr_B_0 s))
  (f1 : forall s, P (dep_constr_B_1 s))
  (b : B)
: P b.
Proof.
  induction (split b).
  - apply (f0 (existT _ b a)).
  - apply (f1 (existT _ b b0)).
Defined.

Program Definition iota_A_0 P f0 f1 s (Q : P (dep_constr_A_0 s) -> Type)
: Q (dep_elim_A P f0 f1 (dep_constr_A_0 s)) -> Q (f0 s).
Proof.
  intros. apply X.
Defined.

Program Definition iota_A_1 P f0 f1 s (Q : P (dep_constr_A_1 s) -> Type)
: Q (dep_elim_A P f0 f1 (dep_constr_A_1 s)) -> Q (f1 s).
Proof.
  intros. apply X.
Defined.

Program Definition iota_B_0 P f0 f1 s (Q : P (dep_constr_B_0 s) -> Type)
: Q (dep_elim_B P f0 f1 (dep_constr_B_0 s)) -> Q (f0 s).
Proof.
  intros. unfold dep_constr_B_0 in *. unfold dep_elim_B in X. 
  induction s. simpl in X.
  rewrite <- (split_OK_left x p) in X. apply X.
Defined.

Program Definition iota_B_1 P f0 f1 s (Q : P (dep_constr_B_1 s) -> Type)
: Q (dep_elim_B P f0 f1 (dep_constr_B_1 s)) -> Q (f1 s).
Proof.
  intros. unfold dep_constr_B_1 in *. unfold dep_elim_B in X.
  induction s. simpl in X.
  rewrite <- (split_OK_right x p) in X. apply X.
Defined.

Program Definition f : A -> B.
Proof.
  intros a. apply dep_elim_A with (P := fun _ => B); intros.
  - apply (dep_constr_B_0 s).
  - apply (dep_constr_B_1 s).
  - apply a.
Defined.

Program Definition g : B -> A.
Proof.
  intros b. apply dep_elim_B with (P := fun _ => A); intros.
  - apply (dep_constr_A_0 s).
  - apply (dep_constr_A_1 s).
  - apply b.
Defined.

Save equivalence A B { promote = f; forget = g }.
Configure Lift A B {
  constrs_a = dep_constr_A_0 dep_constr_A_1;
  constrs_b = dep_constr_B_0 dep_constr_B_1;
  elim_a = dep_elim_A;
  elim_b = dep_elim_B;
  eta_a = eta_A;
  eta_b = eta_B;
  iota_a = iota_A_0 iota_A_1;
  iota_b = iota_B_0 iota_B_1
}.

(*
 * Then we can write:
 *)
Module SumProofs.

Program Definition identity (a : A) : A.
Proof.
  apply dep_elim_A with (P := fun _ => A); intros.
  - apply dep_constr_A_0. apply NoBoolProofs.identity. apply s.
  - apply dep_constr_A_1. apply YesBoolProofs.identity. apply s.
  - apply a.
Defined.

Program Definition free_vars (a : A) : list Identifier.
Proof.
  apply dep_elim_A with (P := fun _ => list Identifier); intros.
  - apply NoBoolProofs.free_vars. apply s.
  - apply YesBoolProofs.free_vars. apply s.
  - apply a.
Defined.

End SumProofs.

Repair Module A B in NoBoolProofs as NoBoolProofs'.
Repair Module A B in YesBoolProofs as YesBoolProofs'.
Repair Module A B in SumProofs as AddBoolProofs.

Print AddBoolProofs.identity.
Print AddBoolProofs.free_vars.

(*
 * This works, but it gives you slow functions!
 * It does separate out the new information, though, and guarantee preservation
 * of the old behavior:
 *)
Module Manual.

Import AddBool.

  Fixpoint identity (t : Term) : Term :=
  match t with
  | Var x => Var x
  | Int i => Int i
  | Bool b => Bool b
  | Eq a b => Eq (identity a) (identity b)
  | Plus a b => Plus (identity a) (identity b)
  | Times a b => Times (identity a) (identity b)
  | Minus a b => Minus (identity a) (identity b)
  | Choose x P => Choose x (identity P)
  end.

Fixpoint free_vars (t : Term) : list Identifier :=
  match t with
  | Var x => [x]
  | Int _ => []
  | Bool _ => []
  | Eq a b => free_vars a ++ free_vars b
  | Plus a b => free_vars a ++ free_vars b
  | Times a b => free_vars a ++ free_vars b
  | Minus a b => free_vars a ++ free_vars b
  | Choose x P =>
      filter (fun y => if id_eq_dec x y then false else true) (free_vars P)
  end.

End Manual.

Lemma identity_OK:
  forall t, AddBoolProofs.identity t = Manual.identity t.
Proof.
  intros t. induction t; auto; simpl.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.identity. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.identity. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.identity. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.identity. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt.
    unfold AddBoolProofs.identity. simpl.
    induction (split t); reflexivity.
Defined.

Lemma free_vars_OK:
  forall t, AddBoolProofs.free_vars t = Manual.free_vars t.
Proof.
  intros t. induction t; auto; simpl.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.free_vars. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.free_vars. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.free_vars. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt1. rewrite <- IHt2.
    unfold AddBoolProofs.free_vars. simpl.
    induction (split t1), (split t2); reflexivity.
  - rewrite <- IHt.
    unfold AddBoolProofs.free_vars. simpl.
    induction (split t); reflexivity.
Defined.

(*
 * Can we get faster functions and proofs?
 * Let's try working directly with the final equivalence.
 *)

(* --- 4. Thus, New.Term + Diff is equivalent to AddBool.Term --- *)

(*
 * We already have slow correct functions.
 * Down here I'm exploring if we can get fast ones.
 * The developer effort to get fast ones here is way too high,
 * so I think the answer is for now, not reasonably, and getting
 * slow versions and checking correctness is the better use case.
 * There may be a better equivalence and configuration that gets you there,
 * or this may be a place to compose with another tool since it involves
 * a very different eliminator transformation.
 * 
 * Still, you can look at this equivalence if you are interested.
 * Long-term, I think we're going to chain our work with CoqEAL or something
 * to handle this case efficiently.
 *)

Definition A' : Type := New.Term + Diff.
Definition B' : Type := AddBool.Term.

Program Definition dep_constr_A_0' (i : Identifier) : A'.
Proof.
  left. apply (New.Var i).
Defined.
Program Definition dep_constr_A_1' (b : bool) : A'.
Proof.
  right. apply (DiffBool b).
Defined.
Program Definition dep_constr_A_2' (a1 a2 : A') : A'.
Proof.
  induction a1, a2.
  - left. apply (New.Eq a t).
  - right. apply DiffEqLeft; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply DiffEqRight; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply (DiffEq b d). 
Defined.
Program Definition dep_constr_A_3' (z : Z) : A'.
Proof.
  left. apply (New.Int z).
Defined.
Program Definition dep_constr_A_4' (a1 a2 : A') : A'.
Proof.
  induction a1, a2.
  - left. apply (New.Plus a t).
  - right. apply DiffPlusLeft; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply DiffPlusRight; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply (DiffPlus b d). 
Defined.
Program Definition dep_constr_A_5' (a1 a2 : A') : A'.
Proof.
  induction a1, a2.
  - left. apply (New.Times a t).
  - right. apply DiffTimesLeft; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply DiffTimesRight; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply (DiffTimes b d).  
Defined.
Program Definition dep_constr_A_6' (a1 a2 : A') : A'.
Proof.
  induction a1, a2.
  - left. apply (New.Minus a t).
  - right. apply DiffMinusLeft; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply DiffMinusRight; auto using NoBoolProofs.Term_to_no_bools.
  - right. apply (DiffMinus b d).  
Defined.
Program Definition dep_constr_A_7' (i : Identifier) (a : A') : A'.
Proof.
  induction a.
  - left. apply (New.Choose i a).
  - right. apply DiffChoose; auto.
Defined.
Definition dep_constr_B_0' := AddBool.Var.
Definition dep_constr_B_1' := AddBool.Bool.
Definition dep_constr_B_2' := AddBool.Eq.
Definition dep_constr_B_3' := AddBool.Int.
Definition dep_constr_B_4' := AddBool.Plus.
Definition dep_constr_B_5' := AddBool.Times.
Definition dep_constr_B_6' := AddBool.Minus.
Definition dep_constr_B_7' := AddBool.Choose.

Definition eta_A' (a : A') : A' := a. (* should probably expand for real *)
Definition eta_B' (b : B') : B' := b.

Lemma dep_elim_A' (P : A' -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0' i))
  (f1 : forall b : bool, P (dep_constr_A_1' b))
  (f2 : forall t : A', P t -> forall t0 : A', P t0 -> P (dep_constr_A_2' t t0))
  (f3 : forall z : Z, P (dep_constr_A_3' z))
  (f4 : forall t : A', P t -> forall t0 : A', P t0 -> P (dep_constr_A_4' t t0))
  (f5 : forall t : A', P t -> forall t0 : A', P t0 -> P (dep_constr_A_5' t t0))
  (f6 : forall t : A', P t -> forall t0 : A', P t0 -> P (dep_constr_A_6' t t0))
  (f7 : forall (i : Identifier) (t : A'), P t -> P (dep_constr_A_7' i t))
  (t : A')
: P t.
Proof.
  assert (forall a, P (inl a)).
  - intros a. induction a.
    + apply f0.
    + apply (f2 (inl a1) IHa1 (inl a2) IHa2).
    + apply f3.
    + apply (f4 (inl a1) IHa1 (inl a2) IHa2).
    + apply (f5 (inl a1) IHa1 (inl a2) IHa2).
    + apply (f6 (inl a1) IHa1 (inl a2) IHa2).
    + apply (f7 i (inl a) IHa).
  - induction t; auto. induction b.
    + apply f1.
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f2 (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s)) (inr b) IHb ).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f2 (inr b) IHb (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s))).
    + apply (f2 (inr b1) IHb1 (inr b2) IHb2).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f4 (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s)) (inr b) IHb ).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f4 (inr b) IHb (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s))).
    + apply (f4 (inr b1) IHb1 (inr b2) IHb2).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f5 (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s)) (inr b) IHb ).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f5 (inr b) IHb (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s))).
    + apply (f5 (inr b1) IHb1 (inr b2) IHb2).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f6 (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s)) (inr b) IHb ).
    + rewrite <- (NoBoolProofs.Term_to_no_bools_retraction s).
      apply (f6 (inr b) IHb (inl (NoBoolProofs.Term_to_no_bools_inv s)) (X (NoBoolProofs.Term_to_no_bools_inv s))).
    + apply (f6 (inr b1) IHb1 (inr b2) IHb2).
    + apply (f7 i (inr b) IHb).
Defined.

Definition dep_elim_B' := AddBool.Term_rect.

Definition section_adjoint := Adjoint.fg_id' NoBoolProofs.Term_to_no_bools_inv NoBoolProofs.Term_to_no_bools NoBoolProofs.Term_to_no_bools_retraction NoBoolProofs.Term_to_no_bools_section.

Lemma is_adjoint a : NoBoolProofs.Term_to_no_bools_retraction (NoBoolProofs.Term_to_no_bools a) = f_equal NoBoolProofs.Term_to_no_bools (section_adjoint a).
Proof.
  apply Adjoint.g_adjoint.
Defined.

Program Definition iota_A_0' P f0 f1 f2 f3 f4 f5 f6 f7 i Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_0' i)) ->
  Q (f0 i).
Proof.
  intros. auto.
Defined.

Program Definition iota_B_0' P f0 f1 f2 f3 f4 f5 f6 f7 i Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_0' i)) ->
  Q (f0 i).
Proof.
  intros. auto.
Defined.

Program Definition iota_A_1' P f0 f1 f2 f3 f4 f5 f6 f7 b Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_1' b)) ->
  Q (f1 b).
Proof.
  intros. auto.
Defined.

Program Definition iota_B_1' P f0 f1 f2 f3 f4 f5 f6 f7 b Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_1' b)) ->
  Q (f1 b).
Proof.
  intros. auto.
Defined.

Lemma iota_A_2'_aux P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2:
  dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_2' a1 a2) =
  f2 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2).
Proof.
  induction a1, a2; auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint a). auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint t). auto.
Defined.

Program Definition iota_A_2' P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2 Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_2' a1 a2)) ->
  Q (f2 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. rewrite <- iota_A_2'_aux. auto.
Defined.

Program Definition iota_B_2' P f0 f1 f2 f3 f4 f5 f6 f7 b1 b2 Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_2' b1 b2)) ->
  Q (f2 b1 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b1) b2 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b2)).
Proof.
  intros. auto.
Defined.

Program Definition iota_A_3' P f0 f1 f2 f3 f4 f5 f6 f7 z Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_3' z)) ->
  Q (f3 z).
Proof.
  intros. auto.
Defined.

Program Definition iota_B_3' P f0 f1 f2 f3 f4 f5 f6 f7 z Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_3' z)) ->
  Q (f3 z).
Proof.
  intros. auto.
Defined.

Lemma iota_A_4'_aux P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2:
  dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_4' a1 a2) =
  f4 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2).
Proof.
  induction a1, a2; auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint a). auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint t). auto.
Defined.

Program Definition iota_A_4' P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2 Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_4' a1 a2)) ->
  Q (f4 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. rewrite <- iota_A_4'_aux. auto.
Defined.

Program Definition iota_B_4' P f0 f1 f2 f3 f4 f5 f6 f7 b1 b2 Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_4' b1 b2)) ->
  Q (f4 b1 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b1) b2 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b2)).
Proof.
  intros. auto.
Defined.

Lemma iota_A_5'_aux P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2:
  dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_5' a1 a2) =
  f5 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2).
Proof.
  induction a1, a2; auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint a). auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint t). auto.
Defined.

Program Definition iota_A_5' P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2 Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_5' a1 a2)) ->
  Q (f5 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. rewrite <- iota_A_5'_aux. auto.
Defined.

Program Definition iota_B_5' P f0 f1 f2 f3 f4 f5 f6 f7 b1 b2 Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_5' b1 b2)) ->
  Q (f5 b1 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b1) b2 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b2)).
Proof.
  intros. auto.
Defined.

Lemma iota_A_6'_aux P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2:
  dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_6' a1 a2) =
  f6 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2).
Proof.
  induction a1, a2; auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint a). auto.
  - simpl. rewrite is_adjoint. destruct (section_adjoint t). auto.
Defined.

Program Definition iota_A_6' P f0 f1 f2 f3 f4 f5 f6 f7 a1 a2 Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_6' a1 a2)) ->
  Q (f6 a1 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. rewrite <- iota_A_6'_aux. auto.
Defined.

Program Definition iota_B_6' P f0 f1 f2 f3 f4 f5 f6 f7 b1 b2 Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_6' b1 b2)) ->
  Q (f6 b1 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b1) b2 (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b2)).
Proof.
  intros. auto.
Defined.

Program Definition iota_A_7' P f0 f1 f2 f3 f4 f5 f6 f7 i a Q
: Q (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_7' i a)) ->
  Q (f7 i a (dep_elim_A' P f0 f1 f2 f3 f4 f5 f6 f7 a)).
Proof.
  intros. induction a; apply X.
Defined.

Program Definition iota_B_7' P f0 f1 f2 f3 f4 f5 f6 f7 i b Q
: Q (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_7' i b)) ->
  Q (f7 i b (dep_elim_B' P f0 f1 f2 f3 f4 f5 f6 f7 b)).
Proof.
  intros. auto.
Defined.

Program Definition f' : A' -> B'.
Proof.
  intros a. apply dep_elim_A' with (P := fun _ => B'); intros.
  - apply (dep_constr_B_0' i).
  - apply (dep_constr_B_1' b).
  - apply (dep_constr_B_2' X X0).
  - apply (dep_constr_B_3' z).
  - apply (dep_constr_B_4' X X0).
  - apply (dep_constr_B_5' X X0).
  - apply (dep_constr_B_6' X X0).
  - apply (dep_constr_B_7' i X).
  - apply a.
Defined.

Program Definition g' : B' -> A'.
Proof.
  intros b. apply dep_elim_B' with (P := fun _ => A'); intros.
  - apply (dep_constr_A_0' i).
  - apply (dep_constr_A_1' b0).
  - apply (dep_constr_A_2' X X0).
  - apply (dep_constr_A_3' z).
  - apply (dep_constr_A_4' X X0).
  - apply (dep_constr_A_5' X X0).
  - apply (dep_constr_A_6' X X0).
  - apply (dep_constr_A_7' i X).
  - apply b.
Defined.

Save equivalence A' B' { promote = f'; forget = g' }.
Configure Lift A' B' {
  constrs_a = dep_constr_A_0' dep_constr_A_1' dep_constr_A_2' dep_constr_A_3' dep_constr_A_4' dep_constr_A_5' dep_constr_A_6' dep_constr_A_7';
  constrs_b = dep_constr_B_0' dep_constr_B_1' dep_constr_B_2' dep_constr_B_3' dep_constr_B_4' dep_constr_B_5' dep_constr_B_6' dep_constr_B_7';
  elim_a = dep_elim_A';
  elim_b = dep_elim_B';
  eta_a = eta_A';
  eta_b = eta_B';
  iota_a = iota_A_0' iota_A_1' iota_A_2' iota_A_3' iota_A_4' iota_A_5' iota_A_6' iota_A_7';
  iota_b = iota_B_0' iota_B_1' iota_B_2' iota_B_3' iota_B_4' iota_B_5' iota_B_6' iota_B_7'
}.

(*
 * But writing functions and proofs this way isn't any easier.
 * We can backport from the fast version to show equivalent terms exist,
 * at least, but nobody would ever want to write these directly.
 *)
Preprocess Module Manual as Manual'.
Repair Module B' A' in Manual' as Backported.
Print Backported.identity.
Print Backported.free_vars.
(* there may be a different configuration that gets you there and isn't this hard, but I don't know it *)


