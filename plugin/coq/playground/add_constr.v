(*
 * Taking another shot at adding new constructors.
 *)
Require Import List.
Require Import String.
Require Import ZArith.

Import ListNotations.

Require Import Ornamental.Ornaments.
Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.
Set DEVOID lift type.
Set DEVOID search smart eliminators.

(*
 * Let's do the full REPLICA benchmark and see what happens.
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

Definition extendEnv {Value} (env : Identifier -> Value) 
  (var : Identifier) (newValue : Value) : Identifier -> Value :=
  fun id => if id_eq_dec id var then newValue else env id.

Record EpsilonLogic :=
 mkLogic {Value : Type;
          value_eq_dec : forall v1 v2 : Value, {v1 = v2} + {v1 <> v2};
          vTrue : Value;
          vFalse : Value;
          trueAndFalseDistinct : vTrue <> vFalse;
          eval : (Identifier -> Value) -> Term -> Value;
          evalVar : forall env id, eval env (Var id) = env id;
          evalIntConst :
           forall env1 env2 i, eval env1 (Int i) = eval env2 (Int i);
          evalIntInj :
           forall env i j, i <> j -> eval env (Int i) <> eval env (Int j);
          evalEqTrue :
           forall env a b,
           eval env a = eval env b <-> eval env (Eq a b) = vTrue;
          evalEqFalse :
           forall env a b,
           eval env a <> eval env b <-> eval env (Eq a b) = vFalse;
          evalPlus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Plus iE jE) = eval env (Int (i + j));
          evalMinus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Minus iE jE) = eval env (Int (i - j));
          evalTimes :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Times iE jE) = eval env (Int (i * j));
          evalChoose :
           forall env x P,
           (exists value, eval (extendEnv env x value) P = vTrue) ->
           eval (extendEnv env x (eval env (Choose x P))) P = vTrue;
          evalChooseDet :
           forall env x P Q,
           eval env P = vTrue <-> eval env Q = vTrue ->
           eval env (Choose x P) = eval env (Choose x Q)}.

Definition isTheorem (L : EpsilonLogic) (t : Term) :=
  forall env, L.(eval) env t = L.(vTrue).

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

Theorem eval_eq_true_or_false :
  forall (L : EpsilonLogic) env (t1 t2 : Term),
  L.(eval) env (Eq t1 t2) = L.(vTrue) \/ L.(eval) env (Eq t1 t2) = L.(vFalse).
Proof.
(intros).
(destruct (L.(value_eq_dec) (L.(eval) env t1) (L.(eval) env t2)) eqn:E).
-
left.
(apply L.(evalEqTrue)).
assumption.
-
right.
(apply L.(evalEqFalse)).
assumption.
Qed.

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

(*
 * OK, so the first challenge is figuring out the equivalence to begin with.
 * What is the new information?
 *
 * Let's start with the trivial equivalence that ignores the new information,
 * and then improve from there.
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
 * Hilariously, this is an algebraic ornament.
 * So we can get these with automatic config:
 *)
Repair Module New.Term no_bools in NewProofs as AddBoolProofs.
Print AddBoolProofs.identity.
  
Definition index := AddBoolProofs.Term_to_no_bools_index.

(*
 * OK, we have things over B. Now the question is, is there an
 * easy way to get from that to the extended definition?
 *
 * Maybe:
 *)
Module Curious.

(*
 * TODO can probably automate this part:
 *)
Inductive yes_bools : forall (t : AddBool.Term), Type :=
| yb1 : forall b, yes_bools (AddBool.Bool b)
| yb2left : forall t1 t2, yes_bools t1 -> no_bools t2 -> yes_bools (AddBool.Eq t1 t2)
| yb2right : forall t1 t2, no_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Eq t1 t2)
| yb2 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Eq t1 t2)
| yb3left : forall t1 t2, yes_bools t1 -> no_bools t2 -> yes_bools (AddBool.Plus t1 t2)
| yb3right : forall t1 t2, no_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Plus t1 t2)
| yb3 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Plus t1 t2)
| yb4left : forall t1 t2, yes_bools t1 -> no_bools t2 -> yes_bools (AddBool.Times t1 t2)
| yb4right : forall t1 t2, no_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Times t1 t2)
| yb4 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Times t1 t2)
| yb5left : forall t1 t2, yes_bools t1 -> no_bools t2 -> yes_bools (AddBool.Minus t1 t2)
| yb5right : forall t1 t2, no_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Minus t1 t2)
| yb5 : forall t1 t2, yes_bools t1 -> yes_bools t2 -> yes_bools (AddBool.Minus t1 t2)
| yb6 : forall a t, yes_bools t -> yes_bools (AddBool.Choose a t).

Definition A : Type := sigT (fun (t : AddBool.Term) => no_bools t) + sigT (fun (t : AddBool.Term) => yes_bools t).
Definition B : Type := AddBool.Term.

(* TODO can probably automate this part *)
Program Definition dep_constr_A_0 (t : AddBool.Term) (H : no_bools t) : A.
Proof.
  unfold A. left. exists t. apply H.
Defined.
Program Definition dep_constr_A_1 (t : AddBool.Term) (H : yes_bools t) : A.
Proof.
  unfold A. right. exists t. apply H.
Defined.

Program Definition dep_constr_B_0 (t : AddBool.Term) (H : no_bools t) : B.
Proof.
  apply t.
Defined.
Program Definition dep_constr_B_1 (t : AddBool.Term) (H : yes_bools t) : B.
Proof.
  apply t.
Defined.

Program Definition eta_A (a : A) : A.
Proof.
  unfold A in *. induction a.
  - left. apply (existT _ (projT1 a) (projT2 a)).
  - right. apply (existT _ (projT1 b) (projT2 b)).
Defined.
Definition eta_B (b : B) := b.

Program Definition dep_elim_A (P : A -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_A_0 t H))
  (f1 : forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_A_1 t H))
  (a : A)
: P (eta_A a).
Proof.
  induction a.
  - induction a. apply f0.
  - induction b. apply f1.
Defined.

Lemma split_dec :
  forall (b : B), no_bools b + yes_bools b.
Proof.
  intros b0. induction b0.
  - left. constructor.
  - right. constructor.
  - induction IHb0_1, IHb0_2.
    + left. constructor; auto.
    + right. apply yb2right; auto.
    + right. apply yb2left; auto.
    + right. apply yb2; auto.
  - left. constructor.
  - induction IHb0_1, IHb0_2.
    + left. constructor; auto.
    + right. apply yb3right; auto.
    + right. apply yb3left; auto.
    + right. apply yb3; auto.
  - induction IHb0_1, IHb0_2.
    + left. constructor; auto.
    + right. apply yb4right; auto.
    + right. apply yb4left; auto.
    + right. apply yb4; auto.
  - induction IHb0_1, IHb0_2.
    + left. constructor; auto.
    + right. apply yb5right; auto.
    + right. apply yb5left; auto.
    + right. apply yb5; auto.
  - induction IHb0.
    + left. constructor; auto.
    + right. apply yb6; auto.
Defined.

Program Definition dep_elim_B (P : B -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_B_0 t H))
  (f1 : forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_B_1 t H))
  (b : B)
: P b.
Proof.
  generalize (split_dec b). intros. induction H. 
  - apply (f0 b a).
  - apply (f1 b b0).
Defined.

Lemma iota_A_0 (P : A -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_A_0 t H))
  (f1 : forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_A_1 t H))
  (t : AddBool.Term) (Ht : no_bools t) (Q : P (dep_constr_A_0 t Ht) -> Type)
  (H : Q (dep_elim_A P f0 f1 (dep_constr_A_0 t Ht))) 
: Q (f0 t Ht).
Proof.
  intros. apply H.
Defined.

Lemma iota_A_1 (P : A -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_A_0 t H))
  (f1 : forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_A_1 t H))
  (t : AddBool.Term) (Ht : yes_bools t) (Q : P (dep_constr_A_1 t Ht) -> Type)
  (H : Q (dep_elim_A P f0 f1 (dep_constr_A_1 t Ht))) 
: Q (f1 t Ht).
Proof.
  intros. apply H.
Defined.

Lemma split_dec_left_OK:
  forall (t : AddBool.Term) (H : no_bools t),
    inl H = split_dec t.
Proof.
  intros. induction H; auto; simpl.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools1. rewrite <- IHno_bools2. auto.
  - rewrite <- IHno_bools. auto.
Defined.

Lemma split_dec_right_OK:
  forall (t : AddBool.Term) (H : yes_bools t),
    inr H = split_dec t.
Proof.
  intros. induction H; auto; simpl.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t2 n). auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t1 n). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t2 n). auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t1 n). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t2 n). auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t1 n). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t2 n). auto.
  - rewrite <- IHyes_bools. simpl. rewrite <- (split_dec_left_OK t1 n). auto.
  - rewrite <- IHyes_bools1. rewrite <- IHyes_bools2. auto.
  - rewrite <- IHyes_bools. simpl. auto.
Defined.

Lemma iota_B_0 (P : B -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_B_0 t H))
  (f1 : forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_B_1 t H))
  (t : AddBool.Term) (Ht : no_bools t) (Q : P (dep_constr_B_0 t Ht) -> Type)
  (H : Q (dep_elim_B P f0 f1 (dep_constr_B_0 t Ht))) 
: Q (f0 t Ht).
Proof.
  unfold dep_elim_B in H. unfold dep_constr_B_0 in H.
  rewrite <- (split_dec_left_OK t Ht) in H.
  apply H.
Defined.

Lemma iota_B_1 (P : B -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_B_0 t H))
  (f1 : forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_B_1 t H))
  (t : AddBool.Term) (Ht : yes_bools t) (Q : P (dep_constr_B_1 t Ht) -> Type)
  (H : Q (dep_elim_B P f0 f1 (dep_constr_B_1 t Ht))) 
: Q (f1 t Ht).
Proof.
  unfold dep_elim_B in H. unfold dep_constr_B_1 in H.
  rewrite <- (split_dec_right_OK t Ht) in H.
  apply H.
Defined.

Program Definition f : A -> B.
Proof.
  intros a. apply dep_elim_A with (P := fun _ => B); intros.
  - apply (dep_constr_B_0 t H).
  - apply (dep_constr_B_1 t H).
  - apply a.
Defined.

Program Definition g : B -> A.
Proof.
  intros b. apply dep_elim_B with (P := fun _ => A); intros.
  - apply (dep_constr_A_0 t H).
  - apply (dep_constr_A_1 t H).
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

Unset DEVOID lift type. (* silly unification bug *)
Repair A B in dep_elim_A as dep_elim_A_lifted.
Print dep_elim_A_lifted.
(* TODO iota, equiv, proof, save config, use *)
(* TODO then one more ...
Definition A := AddBool.Term.
Definition B := True.
*)

Program Definition dep_elim_A_gen (P : A -> Type)
  (f0 : forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_A_0 t H))
  (f1 : (forall (t : AddBool.Term) (H : no_bools t), P (dep_constr_A_0 t H)) -> forall (t : AddBool.Term) (H : yes_bools t), P (dep_constr_A_1 t H))
  (a : A)
: P (eta_A a).
Proof.
  apply dep_elim_A; intros; auto.
Defined.

Repair A B in dep_elim_A_gen as dep_elim_B_gen.
Print dep_elim_B_gen.

End Curious.

Import Curious.

(*
 * Can we get this induction principle to begin with somehow, though? To avoid gross sigma stuff?
 * If so, what would AddBool.Bool and projT1 lift from?
 *)

Module AddBoolProofsExt.

Import AddBool AddBoolProofs.

Print EpsilonLogic.

(* TODO defer these
Definition EpsilonLogic := 
 mkLogic {Value : Type;
          value_eq_dec : forall v1 v2 : Value, {v1 = v2} + {v1 <> v2};
          vTrue : Value;
          vFalse : Value;
          trueAndFalseDistinct : vTrue <> vFalse;
          eval : (Identifier -> Value) -> Term -> Value;
          evalVar : forall env id, eval env (Var id) = env id;
          evalIntConst :
           forall env1 env2 i, eval env1 (Int i) = eval env2 (Int i);
          evalIntInj :
           forall env i j, i <> j -> eval env (Int i) <> eval env (Int j);
          evalEqTrue :
           forall env a b,
           eval env a = eval env b <-> eval env (Eq a b) = vTrue;
          evalEqFalse :
           forall env a b,
           eval env a <> eval env b <-> eval env (Eq a b) = vFalse;
          evalPlus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Plus iE jE) = eval env (Int (i + j));
          evalMinus :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Minus iE jE) = eval env (Int (i - j));
          evalTimes :
           forall env iE jE i j,
           eval env iE = eval env (Int i) ->
           eval env jE = eval env (Int j) ->
           eval env (Times iE jE) = eval env (Int (i * j));
          evalChoose :
           forall env x P,
           (exists value, eval (extendEnv env x value) P = vTrue) ->
           eval (extendEnv env x (eval env (Choose x P))) P = vTrue;
          evalChooseDet :
           forall env x P Q,
           eval env P = vTrue <-> eval env Q = vTrue ->
           eval env (Choose x P) = eval env (Choose x Q)}.

Definition isTheorem (L : EpsilonLogic) (t : Term) :=
  forall env, L.(eval) env t = L.(vTrue).*)


Program Definition identity_A (a : A) : Term.
Proof.
  apply dep_elim_A_gen with (a := a) (P := fun _ => Term); intros.
  - apply identity. apply (existT _ t H).
  - induction H0; intros.
    + apply (AddBool.Bool b).
    + apply (AddBool.Eq t1 t2).
    + apply (AddBool.Eq t1 t2).
    + apply (AddBool.Eq t1 t2).
    + apply (AddBool.Plus t1 t2).
    + apply (AddBool.Plus t1 t2).
    + apply (AddBool.Plus t1 t2).
    + apply (AddBool.Times t1 t2).
    + apply (AddBool.Times t1 t2).
    + apply (AddBool.Times t1 t2).
    + apply (AddBool.Minus t1 t2).
    + apply (AddBool.Minus t1 t2).
    + apply (AddBool.Minus t1 t2).
    + apply (AddBool.Choose a0 t).
Defined.

Repair A B in identity_A as identity.
Print identity.

Program Definition free_vars_A (a : A) : list Identifier.
Proof.
  apply dep_elim_A_gen with (a := a) (P := fun _ => list Identifier); intros.
  - apply free_vars. apply (existT _ t H).
  - induction H0; intros.
    + apply [].
    + apply (IHyes_bools ++ H t2 n).
    + apply (H t1 n ++ IHyes_bools). 
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (IHyes_bools ++ H t2 n).
    + apply (H t1 n ++ IHyes_bools).
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (IHyes_bools ++ H t2 n).
    + apply (H t1 n ++ IHyes_bools).
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (IHyes_bools ++ H t2 n).
    + apply (H t1 n ++ IHyes_bools).
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (filter (fun y => if id_eq_dec a0 y then false else true) IHyes_bools).
Defined.

Repair A B in free_vars_A as free_vars.
Print dep_elim_B_gen.

Definition free_vars_delta (a : Term) : list Identifier :=
  let H := (fun (t : Term) (H : no_bools t) => AddBoolProofs.free_vars (existT no_bools t H)) in
  dep_elim_A_lifted
    (fun _ : Term => list Identifier)
    H
  (fun (t : Term) (H0 : yes_bools t) =>
   yes_bools_rec 
     (fun (t0 : Term) (_ : yes_bools t0) => list Identifier)
     (fun _ : bool => [])
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools : list Identifier)
        (n : no_bools t2) => IHyes_bools ++ H t2 n)
     (fun (t1 t2 : Term) (n : no_bools t1) (_ : yes_bools t2)
        (IHyes_bools : list Identifier) => H t1 n ++ IHyes_bools)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools1 : list Identifier)
        (_ : yes_bools t2) (IHyes_bools2 : list Identifier) =>
      IHyes_bools1 ++ IHyes_bools2)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools : list Identifier)
        (n : no_bools t2) => IHyes_bools ++ H t2 n)
     (fun (t1 t2 : Term) (n : no_bools t1) (_ : yes_bools t2)
        (IHyes_bools : list Identifier) => H t1 n ++ IHyes_bools)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools1 : list Identifier)
        (_ : yes_bools t2) (IHyes_bools2 : list Identifier) =>
      IHyes_bools1 ++ IHyes_bools2)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools : list Identifier)
        (n : no_bools t2) => IHyes_bools ++ H t2 n)
     (fun (t1 t2 : Term) (n : no_bools t1) (_ : yes_bools t2)
        (IHyes_bools : list Identifier) => H t1 n ++ IHyes_bools)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools1 : list Identifier)
        (_ : yes_bools t2) (IHyes_bools2 : list Identifier) =>
      IHyes_bools1 ++ IHyes_bools2)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools : list Identifier)
        (n : no_bools t2) => IHyes_bools ++ H t2 n)
     (fun (t1 t2 : Term) (n : no_bools t1) (_ : yes_bools t2)
        (IHyes_bools : list Identifier) => H t1 n ++ IHyes_bools)
     (fun (t1 t2 : Term) (_ : yes_bools t1) (IHyes_bools1 : list Identifier)
        (_ : yes_bools t2) (IHyes_bools2 : list Identifier) =>
      IHyes_bools1 ++ IHyes_bools2)
     (fun (a0 : Identifier) (t0 : Term) (_ : yes_bools t0)
        (IHyes_bools : list Identifier) =>
      filter (fun y : string => if id_eq_dec a0 y then false else true)
        IHyes_bools) t H0) a.

Lemma test:
  free_vars_delta = free_vars.
Proof.
  auto.
Defined.

Program Definition free_vars_manual (a : Term) : list Identifier.
Proof.
  induction a.
  - apply [i].
  - apply [].
  - apply (IHa1 ++ IHa2).
  - apply [].
  - apply (IHa1 ++ IHa2).
  - apply (IHa1 ++ IHa2).
  - apply (IHa1 ++ IHa2).
  - apply (filter (fun y : string => if id_eq_dec i y then false else true) IHa).
Defined.

Lemma testOther:
  forall t, free_vars_delta t = free_vars_manual t.
Proof.
  intros t. unfold free_vars_delta.
  unfold dep_elim_A_lifted. unfold dep_elim_B.
  assert (forall t a, AddBoolProofs.free_vars (existT no_bools t a) = free_vars_manual t).
  - induction a; simpl; auto.
    + rewrite <- IHa1. rewrite <- IHa2; auto.
    + rewrite <- IHa1. rewrite <- IHa2; auto.
    + rewrite <- IHa1. rewrite <- IHa2; auto.
    + rewrite <- IHa1. rewrite <- IHa2; auto.
    + rewrite <- IHa; auto.
  - remember (split_dec t). induction s; simpl; auto.
    induction b; simpl; auto.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb1; simpl; auto.
      * rewrite <- IHb2; simpl; auto. apply split_dec_right_OK.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb1; simpl; auto.
      * rewrite <- IHb2; simpl; auto. apply split_dec_right_OK.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb1; simpl; auto.
      * rewrite <- IHb2; simpl; auto. apply split_dec_right_OK.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto.
      * f_equal. apply H.
      * apply split_dec_right_OK.
    + rewrite <- IHb1; simpl; auto.
      * rewrite <- IHb2; simpl; auto. apply split_dec_right_OK.
      * apply split_dec_right_OK.
    + rewrite <- IHb; simpl; auto. apply split_dec_right_OK.
Defined.

(* OK so it's very ugly and slow, but correct.
   How can we recover the fast version for free?
   Maybe let's start with a more general correpsondence? *)

End AddBoolProofsExt.

