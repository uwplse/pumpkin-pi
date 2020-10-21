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
  constrs_a = dep_constr_A_0 dep_constr_A_1 dep_constr_A_2 dep_constr_A_3 dep_constr_A_4 dep_constr_A_5 dep_constr_A_6 dep_constr_A_7;
  constrs_b = dep_constr_B_0 dep_constr_B_1 dep_constr_B_2 dep_constr_B_3 dep_constr_B_4 dep_constr_B_5 dep_constr_B_6 dep_constr_B_7;
  elim_a = dep_elim_A;
  elim_b = dep_elim_B;
  eta_a = eta_A;
  eta_b = eta_B;
  iota_a = iota_A_0 iota_A_1 iota_A_2 iota_A_3 iota_A_4 iota_A_5 iota_A_6 iota_A_7;
  iota_b = iota_B_0 iota_B_1 iota_B_2 iota_B_3 iota_B_4 iota_B_5 iota_B_6 iota_B_7
}.

Program Definition dep_elim_A_gen:
  forall (P : A -> Type) (f0 : forall (t : AddBool.Term) (H : no_bools t), P (inl (existT _ t H)))
    (f1 : (forall (t : AddBool.Term) (H : no_bools t), P (inl (existT _ t H))) -> forall (t : AddBool.Term) (H : yes_bools t), P (inr (existT _ t H)))
    (a : A), P (eta_A a).
Proof.
  intros. apply dep_elim_A; intros; auto.
  - apply f0.
  - apply f1; auto.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - apply f0.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - induction a0.
    + apply f0.
    + apply f1. apply f0.
Defined.

Unset DEVOID lift type. (* silly unification bug *)
Repair A B in dep_elim_A as dep_elim_A_lifted.
Print dep_elim_A_lifted.
Print dep_elim_A_gen.

Definition gen_elim_A_P (P : A -> Type) := fun (a0 : A) => P a0.
Repair A B in gen_elim_A_P as gen_elim_B_P.

Definition gen_elim_A_0 (P : A -> Type) (f0 : forall (t : AddBool.Term) (H : no_bools t),
        P (inl (existT (fun t0 : AddBool.Term => no_bools t0) t H))) :=
(fun i : Identifier => f0 (AddBool.Var i) (nb1 i)).
Repair A B in gen_elim_A_0 as gen_elim_B_0.

Definition gen_elim_A_parts (P : A -> Type)
(f0 : forall (t : AddBool.Term) (H : no_bools t),
        P (inl (existT (fun t0 : AddBool.Term => no_bools t0) t H)))
  (f1 : (forall (t : AddBool.Term) (H : no_bools t),
         P (inl (existT (fun t0 : AddBool.Term => no_bools t0) t H))) ->
        forall (t : AddBool.Term) (H : yes_bools t),
        P (inr (existT (fun t0 : AddBool.Term => yes_bools t0) t H))) 
  (a : A) : P (eta_A a) :=
dep_elim_A (gen_elim_A_P P)
  (fun i : Identifier => f0 (AddBool.Var i) (nb1 i))
  (fun b : bool => f1 f0 (AddBool.Bool b) (yb1 b))
  (fun (a0 : A) (X : P (eta_A a0)) (a1 : A) (X0 : P (eta_A a1)) =>
   sum_rect
     (fun a2 : {t : AddBool.Term & no_bools t} + {t : AddBool.Term & yes_bools t}
      => P (eta_A a2) -> P (eta_A (dep_constr_A_2 a2 a1)))
     (fun (a2 : {t : AddBool.Term & no_bools t}) (_ : P (eta_A (inl a2))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_2 (inl a2) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f0
            (projT1
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Eq (projT1 a2) (projT1 s))
                  (nb2 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Eq (projT1 a2) (projT1 s))
                  (nb2 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Eq (projT1 a2) (projT1 s))
                  (yb2right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Eq (projT1 a2) (projT1 s))
                  (yb2right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      end X0)
     (fun (b : {t : AddBool.Term & yes_bools t}) (_ : P (eta_A (inr b))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_2 (inr b) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Eq (projT1 b) (projT1 s))
                  (yb2left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Eq (projT1 b) (projT1 s))
                  (yb2left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Eq (projT1 b) (projT1 s))
                  (yb2 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Eq (projT1 b) (projT1 s))
                  (yb2 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      end X0) a0 X) (fun z : Z => f0 (AddBool.Int z) (nb3 z))
  (fun (a0 : A) (X : P (eta_A a0)) (a1 : A) (X0 : P (eta_A a1)) =>
   sum_rect
     (fun a2 : {t : AddBool.Term & no_bools t} + {t : AddBool.Term & yes_bools t}
      => P (eta_A a2) -> P (eta_A (dep_constr_A_4 a2 a1)))
     (fun (a2 : {t : AddBool.Term & no_bools t}) (_ : P (eta_A (inl a2))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_4 (inl a2) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f0
            (projT1
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Plus (projT1 a2) (projT1 s))
                  (nb4 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Plus (projT1 a2) (projT1 s))
                  (nb4 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Plus (projT1 a2) (projT1 s))
                  (yb3right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Plus (projT1 a2) (projT1 s))
                  (yb3right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      end X0)
     (fun (b : {t : AddBool.Term & yes_bools t}) (_ : P (eta_A (inr b))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_4 (inr b) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Plus (projT1 b) (projT1 s))
                  (yb3left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Plus (projT1 b) (projT1 s))
                  (yb3left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Plus (projT1 b) (projT1 s))
                  (yb3 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Plus (projT1 b) (projT1 s))
                  (yb3 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      end X0) a0 X)
  (fun (a0 : A) (X : P (eta_A a0)) (a1 : A) (X0 : P (eta_A a1)) =>
   sum_rect
     (fun a2 : {t : AddBool.Term & no_bools t} + {t : AddBool.Term & yes_bools t}
      => P (eta_A a2) -> P (eta_A (dep_constr_A_5 a2 a1)))
     (fun (a2 : {t : AddBool.Term & no_bools t}) (_ : P (eta_A (inl a2))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_5 (inl a2) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f0
            (projT1
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Times (projT1 a2) (projT1 s))
                  (nb5 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Times (projT1 a2) (projT1 s))
                  (nb5 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Times (projT1 a2) (projT1 s))
                  (yb4right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Times (projT1 a2) (projT1 s))
                  (yb4right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      end X0)
     (fun (b : {t : AddBool.Term & yes_bools t}) (_ : P (eta_A (inr b))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_5 (inr b) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Times (projT1 b) (projT1 s))
                  (yb4left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Times (projT1 b) (projT1 s))
                  (yb4left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Times (projT1 b) (projT1 s))
                  (yb4 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Times (projT1 b) (projT1 s))
                  (yb4 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      end X0) a0 X)
  (fun (a0 : A) (X : P (eta_A a0)) (a1 : A) (X0 : P (eta_A a1)) =>
   sum_rect
     (fun a2 : {t : AddBool.Term & no_bools t} + {t : AddBool.Term & yes_bools t}
      => P (eta_A a2) -> P (eta_A (dep_constr_A_6 a2 a1)))
     (fun (a2 : {t : AddBool.Term & no_bools t}) (_ : P (eta_A (inl a2))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_6 (inl a2) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f0
            (projT1
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Minus (projT1 a2) (projT1 s))
                  (nb6 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => no_bools t)
                  (AddBool.Minus (projT1 a2) (projT1 s))
                  (nb6 (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Minus (projT1 a2) (projT1 s))
                  (yb5right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Minus (projT1 a2) (projT1 s))
                  (yb5right (projT1 a2) (projT1 s) (projT2 a2) (projT2 s))))
      end X0)
     (fun (b : {t : AddBool.Term & yes_bools t}) (_ : P (eta_A (inr b))) =>
      match
        a1 as s return (P (eta_A s) -> P (eta_A (dep_constr_A_6 (inr b) s)))
      with
      | inl s =>
          fun _ : P (eta_A (inl s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Minus (projT1 b) (projT1 s))
                  (yb5left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Minus (projT1 b) (projT1 s))
                  (yb5left (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      | inr s =>
          fun _ : P (eta_A (inr s)) =>
          f1 f0
            (projT1
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Minus (projT1 b) (projT1 s))
                  (yb5 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
            (projT2
               (existT (fun t : AddBool.Term => yes_bools t)
                  (AddBool.Minus (projT1 b) (projT1 s))
                  (yb5 (projT1 b) (projT1 s) (projT2 b) (projT2 s))))
      end X0) a0 X)
  (fun (i : Identifier) (a0 : A) (X : P (eta_A a0)) =>
   sum_rect
     (fun a1 : {t : AddBool.Term & no_bools t} + {t : AddBool.Term & yes_bools t}
      => P (eta_A a1) -> P (eta_A (dep_constr_A_7 i a1)))
     (fun (a1 : {t : AddBool.Term & no_bools t}) (_ : P (eta_A (inl a1))) =>
      f0
        (projT1
           (existT (fun t : AddBool.Term => no_bools t)
              (AddBool.Choose i (projT1 a1)) (nb7 i (projT1 a1) (projT2 a1))))
        (projT2
           (existT (fun t : AddBool.Term => no_bools t)
              (AddBool.Choose i (projT1 a1)) (nb7 i (projT1 a1) (projT2 a1)))))
     (fun (b : {t : AddBool.Term & yes_bools t}) (_ : P (eta_A (inr b))) =>
      f1 f0
        (projT1
           (existT (fun t : AddBool.Term => yes_bools t)
              (AddBool.Choose i (projT1 b)) (yb6 i (projT1 b) (projT2 b))))
        (projT2
           (existT (fun t : AddBool.Term => yes_bools t)
              (AddBool.Choose i (projT1 b)) (yb6 i (projT1 b) (projT2 b))))) a0 X)
  a.

Repair A B in dep_elim_A_gen as dep_elim_B_gen.

Print dep_elim_A_gen.

Lemma dep_elim_B_gen:
  forall (P : B -> Type) (f0 : forall (t : AddBool.Term) (H : no_bools t), P t)
    (f1 : (forall (t : AddBool.Term) (H : no_bools t), P t) -> forall (t : AddBool.Term) (H : yes_bools t), P t)
    (b : B), P b.
Proof.
  intros. apply dep_elim_B; intros; auto.
  - apply f0.
  - apply f1; auto.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - apply f0.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - induction a0, a1.
    + apply f0. 
    + apply f1. apply f0. 
    + apply f1. apply f0.
    + apply f1. apply f0.
  - induction a0.
    + apply f0.
    + apply f1. apply f0.
Defined.


(* TODO iota, equiv, proof, save config, use *)
(* TODO then one more ...
Definition A := AddBool.Term.
Definition B := True.
*)

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

Import Curious.

Program Definition identity_A (a : A) : Term.
Proof.
  apply dep_elim_A with (a := a) (P := fun _ => Term).
  - intros s. apply identity. apply s.
  - intros. induction s; intros. induction p; intros.
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

Program Definition identity (t : Term) : Term.
Proof.
  apply gen_elim_B with (b := t) (P := fun _ => Term).
  - intros. apply identity. apply s.
  - intros. induction s; intros. induction p; intros.
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
    + apply (AddBool.Choose a t).
Defined.

Program Definition free_vars (t : Term) : list Identifier.
Proof.
  apply gen_elim_B with (b := t) (P := fun _ => list Identifier).
  - intros. apply free_vars. apply s.
  - intros IH s. induction s; intros. induction p; intros.
    + apply [].
    + apply (IHp ++ IH (existT _ t2 n)). 
    + apply (IH (existT _ t1 n) ++ IHp). 
    + apply (IHp1 ++ IHp2).
    + apply (IHp ++ IH (existT _ t2 n)). 
    + apply (IH (existT _ t1 n) ++ IHp). 
    + apply (IHp1 ++ IHp2).
    + apply (IHp ++ IH (existT _ t2 n)). 
    + apply (IH (existT _ t1 n) ++ IHp). 
    + apply (IHp1 ++ IHp2).
    + apply (IHp ++ IH (existT _ t2 n)). 
    + apply (IH (existT _ t1 n) ++ IHp). 
    + apply (IHp1 ++ IHp2).
    + apply (filter (fun y => if id_eq_dec a y then false else true) IHp).
Defined.

Print dep_elim_B.

Program Definition free_vars_manual (t : Term) : list Identifier.
Proof.
  induction t.
  - apply [i].
  - apply [].
  - apply (IHt1 ++ IHt2).
  - apply [].
  - apply (IHt1 ++ IHt2).
  - apply (IHt1 ++ IHt2).
  - apply (IHt1 ++ IHt2).
  - apply (filter (fun y => if id_eq_dec i y then false else true) IHt).
Defined.


Lemma foo:
  forall t, free_vars t = free_vars_manual t.
Proof.
  intros t. unfold free_vars. unfold free_vars_manual.
  unfold gen_elim_B. unfold dep_elim_B. simpl.
  apply gen_elim_B with (b := t).
  - intros. unfold dep_constr_B_0. 
    induction s. simpl. induction (split_dec x).
   unfold AddBoolProofs.free_vars. simpl.
    induction a; simpl; auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa. auto.
  - simpl. unfold AddBoolProofs.free_vars. simpl.
    induction b; simpl; auto.
    + rewrite IHb. auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa1. rewrite IHa2. auto.
    + rewrite IHa. auto.

