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
Program Definition dep_constr_A_0 (i : Identifier) : A.
Proof.
  unfold A. intros. left. exists (AddBool.Var i). constructor.
Defined.
Program Definition dep_constr_A_1 (b : bool) : A.
Proof.
  unfold A. right. exists (AddBool.Bool b). constructor.
Defined.
Program Definition dep_constr_A_2 (a1 a2 : A) : A.
Proof.
  unfold A in *. induction a1, a2.
  - left. exists (AddBool.Eq (projT1 a) (projT1 s)). apply (nb2 (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Eq (projT1 a) (projT1 s)). apply (yb2right (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Eq (projT1 b) (projT1 s)). apply (yb2left (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
  - right. exists (AddBool.Eq (projT1 b) (projT1 s)). apply (yb2 (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
Defined.
Program Definition dep_constr_A_3 (z : Z) : A.
Proof.
  unfold A. left. exists (AddBool.Int z). constructor.
Defined.
Program Definition dep_constr_A_4 (a1 a2 : A) : A.
Proof.
  unfold A in *. induction a1, a2.
  - left. exists (AddBool.Plus (projT1 a) (projT1 s)). apply (nb4 (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Plus (projT1 a) (projT1 s)). apply (yb3right (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Plus (projT1 b) (projT1 s)). apply (yb3left (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
  - right. exists (AddBool.Plus (projT1 b) (projT1 s)). apply (yb3 (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
Defined.
Program Definition dep_constr_A_5 (a1 a2 : A) : A.
Proof.
  unfold A in *. induction a1, a2.
  - left. exists (AddBool.Times (projT1 a) (projT1 s)). apply (nb5 (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Times (projT1 a) (projT1 s)). apply (yb4right (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Times (projT1 b) (projT1 s)). apply (yb4left (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
  - right. exists (AddBool.Times (projT1 b) (projT1 s)). apply (yb4 (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
Defined.
Program Definition dep_constr_A_6 (a1 a2 : A) : A.
Proof.
  unfold A in *. induction a1, a2.
  - left. exists (AddBool.Minus (projT1 a) (projT1 s)). apply (nb6 (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Minus (projT1 a) (projT1 s)). apply (yb5right (projT1 a) (projT1 s) (projT2 a) (projT2 s)).
  - right. exists (AddBool.Minus (projT1 b) (projT1 s)). apply (yb5left (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
  - right. exists (AddBool.Minus (projT1 b) (projT1 s)). apply (yb5 (projT1 b) (projT1 s) (projT2 b) (projT2 s)).
Defined.
Program Definition dep_constr_A_7 (i : Identifier) (a : A) : A.
Proof.
  unfold A in *. induction a.
  - left. exists (AddBool.Choose i (projT1 a)). apply (nb7 i (projT1 a) (projT2 a)).
  - right. exists (AddBool.Choose i (projT1 b)). apply (yb6 i (projT1 b) (projT2 b)).
Defined.

Definition dep_constr_B_0 (i : Identifier) : B := AddBool.Var i.
Definition dep_constr_B_1 (b : bool) : B := AddBool.Bool b.
Definition dep_constr_B_2 (b1 b2 : B) : B := AddBool.Eq b1 b2.
Definition dep_constr_B_3 (z : Z) : B := AddBool.Int z.
Definition dep_constr_B_4 (b1 b2 : B) : B := AddBool.Plus b1 b2.
Definition dep_constr_B_5 (b1 b2 : B) : B := AddBool.Times b1 b2.
Definition dep_constr_B_6 (b1 b2 : B) : B := AddBool.Minus b1 b2.
Definition dep_constr_B_7 (i : Identifier) (b : B) : B := AddBool.Choose i b.

Program Definition eta_A (a : A) : A.
Proof.
  unfold A in *. induction a.
  - left. apply (existT _ (projT1 a) (projT2 a)).
  - right. apply (existT _ (projT1 b) (projT2 b)).
Defined.
Definition eta_B (b : B) := b.

Program Definition dep_elim_A (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (a : A)
: P (eta_A a).
Proof.
  assert (forall (t : AddBool.Term) (H : no_bools t), P (inl (existT _ t H))).
  - intros. induction H.
    + apply f0.
    + apply (f2 (inl (existT _ t1 H)) IHno_bools1 (inl (existT _ t2 H0)) IHno_bools2).
    + apply f3.
    + apply (f4 (inl (existT _ t1 H)) IHno_bools1 (inl (existT _ t2 H0)) IHno_bools2).
    + apply (f5 (inl (existT _ t1 H)) IHno_bools1 (inl (existT _ t2 H0)) IHno_bools2).
    + apply (f6 (inl (existT _ t1 H)) IHno_bools1 (inl (existT _ t2 H0)) IHno_bools2).
    + apply (f7 a0 (inl (existT _ t H)) IHno_bools).
  - assert ((forall (t : AddBool.Term) (H : no_bools t), P (inl (existT _ t H))) -> forall (t : AddBool.Term) (H : yes_bools t), P (inr (existT _ t H))).
    + intros. induction H.
      * apply f1.
      * apply (f2 (inr (existT _ t1 H)) IHyes_bools (inl (existT _ t2 n)) (X t2 n)).
      * apply (f2 (inl (existT _ t1 n)) (X t1 n) (inr (existT _ t2 H)) IHyes_bools).
      * apply (f2 (inr (existT _ t1 H)) IHyes_bools1 (inr (existT _ t2 H0)) IHyes_bools2).
      * apply (f4 (inr (existT _ t1 H)) IHyes_bools (inl (existT _ t2 n)) (X t2 n)).
      * apply (f4 (inl (existT _ t1 n)) (X t1 n) (inr (existT _ t2 H)) IHyes_bools).
      * apply (f4 (inr (existT _ t1 H)) IHyes_bools1 (inr (existT _ t2 H0)) IHyes_bools2).
      * apply (f5 (inr (existT _ t1 H)) IHyes_bools (inl (existT _ t2 n)) (X t2 n)).
      * apply (f5 (inl (existT _ t1 n)) (X t1 n) (inr (existT _ t2 H)) IHyes_bools).
      * apply (f5 (inr (existT _ t1 H)) IHyes_bools1 (inr (existT _ t2 H0)) IHyes_bools2).
      * apply (f6 (inr (existT _ t1 H)) IHyes_bools (inl (existT _ t2 n)) (X t2 n)).
      * apply (f6 (inl (existT _ t1 n)) (X t1 n) (inr (existT _ t2 H)) IHyes_bools).
      * apply (f6 (inr (existT _ t1 H)) IHyes_bools1 (inr (existT _ t2 H0)) IHyes_bools2).
      * apply (f7 a0 (inr (existT _ t H)) IHyes_bools). 
    + induction a.
      * induction a. apply X.
      * induction b. apply X0. apply X.
Defined.

Definition dep_elim_B (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall b : B, P b -> forall b0 : B, P b0 -> P (dep_constr_B_2 b b0))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall b : B, P b -> forall b0 : B, P b0 -> P (dep_constr_B_4 b b0))
  (f5 : forall b : B, P b -> forall b0 : B, P b0 -> P (dep_constr_B_5 b b0))
  (f6 : forall b : B, P b -> forall b0 : B, P b0 -> P (dep_constr_B_6 b b0))
  (f7 : forall (i : Identifier) (b : B), P b -> P (dep_constr_B_7 i b))
  (b : B)
: P b :=
  AddBool.Term_rect P f0 f1 f2 f3 f4 f5 f6 f7 b.

Lemma iota_A_0 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (i : Identifier) (Q : P (dep_constr_A_0 i) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_0 i))) 
: Q (f0 i).
Proof.
  intros. apply H.
Defined.

Program Definition iota_A_1 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (b : bool) (Q : P (dep_constr_A_1 b) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_1 b))) 
: Q (f1 b).
Proof.
  intros. apply H.
Defined.

Lemma iota_A_2 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (a1 a2 : A) (Q : P (eta_A (dep_constr_A_2 a1 a2)) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_2 a1 a2))) 
: Q (f2 a1 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. induction a1, a2.
  - induction a, s. apply H.
  - induction a, s. apply H.
  - induction b, s; apply H.
  - induction b, s; apply H.
Defined.

Lemma iota_A_3 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (z : Z) (Q : P (dep_constr_A_3 z) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_3 z))) 
: Q (f3 z).
Proof.
  intros. apply H.
Defined.

Lemma iota_A_4 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (a1 a2 : A) (Q : P (eta_A (dep_constr_A_4 a1 a2)) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_4 a1 a2))) 
: Q (f4 a1 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. induction a1, a2.
  - induction a, s. apply H.
  - induction a, s. apply H.
  - induction b, s; apply H.
  - induction b, s; apply H.
Defined.

Lemma iota_A_5 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (a1 a2 : A) (Q : P (eta_A (dep_constr_A_5 a1 a2)) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_5 a1 a2))) 
: Q (f5 a1 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. induction a1, a2.
  - induction a, s. apply H.
  - induction a, s. apply H.
  - induction b, s; apply H.
  - induction b, s; apply H.
Defined.

Lemma iota_A_6 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  (a1 a2 : A) (Q : P (eta_A (dep_constr_A_6 a1 a2)) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_6 a1 a2))) 
: Q (f6 a1 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. induction a1, a2.
  - induction a, s. apply H.
  - induction a, s. apply H.
  - induction b, s; apply H.
  - induction b, s; apply H.
Defined.

Lemma iota_A_7 (P : A -> Type)
  (f0 : forall i : Identifier, P (dep_constr_A_0 i))
  (f1 : forall b : bool, P (dep_constr_A_1 b))
  (f2 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_A_3 z))
  (f4 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_4 a a0)))
  (f5 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0)  -> P (eta_A (dep_constr_A_5 a a0)))
  (f6 : forall a : A, P (eta_A a) -> forall a0 : A, P (eta_A a0) -> P (eta_A (dep_constr_A_6 a a0)))
  (f7 : forall (i : Identifier) (a : A), P (eta_A a) -> P (eta_A (dep_constr_A_7 i a)))
  i (a : A) (Q : P (eta_A (dep_constr_A_7 i a)) -> Type)
  (H : Q (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_A_7 i a))) 
: Q (f7 i a (dep_elim_A P f0 f1 f2 f3 f4 f5 f6 f7 a)).
Proof.
  intros. induction a.
  - induction a. apply H.
  - induction b. apply H.
Defined.

Program Definition iota_B_0 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  i (Q : P (dep_constr_B_0 i) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_0 i))) 
: Q (f0 i).
Proof.
  intros. apply H.
Defined.

Program Definition iota_B_1 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  (b : bool) (Q : P (dep_constr_B_1 b) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_1 b))) 
: Q (f1 b).
Proof.
  intros. apply H.
Defined.

Lemma iota_B_2 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  (a1 a2 : B) (Q : P (eta_B (dep_constr_B_2 a1 a2)) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_2 a1 a2))) 
: Q (f2 a1 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. apply H.
Defined.

Lemma iota_B_3 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  (z : Z) (Q : P (dep_constr_B_3 z) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_3 z))) 
: Q (f3 z).
Proof.
  intros. apply H.
Defined.

Lemma iota_B_4 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  (a1 a2 : B) (Q : P (eta_B (dep_constr_B_4 a1 a2)) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_4 a1 a2))) 
: Q (f4 a1 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. apply H.
Defined.

Lemma iota_B_5 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  (a1 a2 : B) (Q : P (eta_B (dep_constr_B_5 a1 a2)) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_5 a1 a2))) 
: Q (f5 a1 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. apply H.
Defined.

Lemma iota_B_6 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  (a1 a2 : B) (Q : P (eta_B (dep_constr_B_6 a1 a2)) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_6 a1 a2))) 
: Q (f6 a1 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a1) a2 (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a2)).
Proof.
  intros. apply H.
Defined.

Lemma iota_B_7 (P : B -> Type)
  (f0 : forall i : Identifier, P (dep_constr_B_0 i))
  (f1 : forall b : bool, P (dep_constr_B_1 b))
  (f2 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_2 a a0)))
  (f3 : forall z : Z, P (dep_constr_B_3 z))
  (f4 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_4 a a0)))
  (f5 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0)  -> P (eta_B (dep_constr_B_5 a a0)))
  (f6 : forall a : B, P (eta_B a) -> forall a0 : B, P (eta_B a0) -> P (eta_B (dep_constr_B_6 a a0)))
  (f7 : forall (i : Identifier) (a : B), P (eta_B a) -> P (eta_B (dep_constr_B_7 i a)))
  i (a : B) (Q : P (eta_B (dep_constr_B_7 i a)) -> Type)
  (H : Q (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 (dep_constr_B_7 i a))) 
: Q (f7 i a (dep_elim_B P f0 f1 f2 f3 f4 f5 f6 f7 a)).
Proof.
  intros. apply H.
Defined.

Program Definition f : A -> B.
Proof.
  intros a. apply dep_elim_A with (P := fun _ => B); intros.
  - apply dep_constr_B_0. auto.
  - apply dep_constr_B_1. auto.
  - apply dep_constr_B_2.
    + apply X.
    + apply X0.
  - apply dep_constr_B_3. auto.
  - apply dep_constr_B_4.
    + apply X.
    + apply X0.
  - apply dep_constr_B_5.
    + apply X.
    + apply X0.
  - apply dep_constr_B_6.
    + apply X.
    + apply X0.
  - apply dep_constr_B_7; auto.
  - apply a.
Defined.

Program Definition g : B -> A.
Proof.
  intros b. apply dep_elim_B with (P := fun _ => A); intros.
  - apply dep_constr_A_0. auto.
  - apply dep_constr_A_1. auto.
  - apply dep_constr_A_2.
    + apply X.
    + apply X0.
  - apply dep_constr_A_3. auto.
  - apply dep_constr_A_4.
    + apply X.
    + apply X0.
  - apply dep_constr_A_5.
    + apply X.
    + apply X0.
  - apply dep_constr_A_6.
    + apply X.
    + apply X0.
  - apply dep_constr_A_7; auto.
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

