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

Preprocess Module User5Session19 as OldProofs.

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
Repair Module New.Term no_bools in NewProofs as AddBoolProofs { 
  opaque 
    NewProofs.Coq_Init_Datatypes_app NewProofs.Coq_Init_Logic_not
    NewProofs.Top_id_eq_dec NewProofs.Coq_Lists_List_filter
}.

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

(*
 * TODO can probably automate this part:
 *)
Lemma bools_dec:
  forall (t : AddBool.Term),
    no_bools t + yes_bools t.
Proof.
  intros t. induction t.
  - left. constructor.
  - right. constructor.
  - induction IHt1, IHt2.
    + constructor. constructor; auto.
    + right. apply yb2right; auto.
    + right. apply yb2left; auto.
    + right. apply yb2; auto.
  - left. constructor.
  - induction IHt1, IHt2.
    + constructor. constructor; auto.
    + right. apply yb3right; auto.
    + right. apply yb3left; auto.
    + right. apply yb3; auto.
  - induction IHt1, IHt2.
    + constructor. constructor; auto.
    + right. apply yb4right; auto.
    + right. apply yb4left; auto.
    + right. apply yb4; auto.
  - induction IHt1, IHt2.
    + constructor. constructor; auto.
    + right. apply yb5right; auto.
    + right. apply yb5left; auto.
    + right. apply yb5; auto.
  - induction IHt.
    + left. constructor. auto.
    + right. constructor. auto.
Defined.

(*
 * TODO can probably automate this part:
 *)
Lemma split_rect:
  forall (P : AddBool.Term -> Type) (f0 : forall t : AddBool.Term, no_bools t -> P t)
    (f1 : (forall t : AddBool.Term, no_bools t -> P t) -> forall t : AddBool.Term, Curious.yes_bools t -> P t)
    (t : AddBool.Term), P t.
Proof.
  intros. induction t.
  - apply (f0 (AddBool.Var i) (nb1 i)).
  - apply f1; auto. constructor.
  - induction (bools_dec t1), (bools_dec t2).
    + apply f0. constructor; auto.
    + apply f1; auto. apply yb2right; auto.
    + apply f1; auto. apply yb2left; auto.
    + apply f1; auto. apply yb2; auto.
  - apply (f0 (AddBool.Int z) (nb3 z)).
  - induction (bools_dec t1), (bools_dec t2).
    + apply f0. constructor; auto.
    + apply f1; auto. apply yb3right; auto.
    + apply f1; auto. apply yb3left; auto.
    + apply f1; auto. apply yb3; auto.
  - induction (bools_dec t1), (bools_dec t2).
    + apply f0. constructor; auto.
    + apply f1; auto. apply yb4right; auto.
    + apply f1; auto. apply yb4left; auto.
    + apply f1; auto. apply yb4; auto.
  - induction (bools_dec t1), (bools_dec t2).
    + apply f0. constructor; auto.
    + apply f1; auto. apply yb5right; auto.
    + apply f1; auto. apply yb5left; auto.
    + apply f1; auto. apply yb5; auto.
  - induction (bools_dec t).
    + apply f0. constructor; auto.
    + apply f1; auto. apply yb6; auto.
Defined.

End Curious.

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

Program Definition identity (t : Term) : Term.
Proof.
  apply Curious.split_rect.
  - intros t0 H. apply (projT1 (identity (existT _ t0 H))).
  - intros IH t0 H. induction H; intros.
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
  - apply t.
Defined.

Program Definition free_vars (t : Term) : list Identifier.
Proof.
  apply Curious.split_rect.
  - intros t0 H. apply (free_vars (existT _ t0 H)).
  - intros IH t0 H. induction H; intros.
    + apply [].
    + apply (IHyes_bools ++ IH t2 n). 
    + apply (IH t1 n ++ IHyes_bools). 
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (IHyes_bools ++ IH t2 n). 
    + apply (IH t1 n ++ IHyes_bools). 
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (IHyes_bools ++ IH t2 n). 
    + apply (IH t1 n ++ IHyes_bools). 
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (IHyes_bools ++ IH t2 n). 
    + apply (IH t1 n ++ IHyes_bools). 
    + apply (IHyes_bools1 ++ IHyes_bools2).
    + apply (filter (fun y => if id_eq_dec a y then false else true) IHyes_bools).
  - apply t.
Defined.

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

(* TODO the result is gross, though, and inefficient---how can we automate getting from the other thing to the thing
   we want? *)
(* TODO maybe try lifting from that along an equivalence between
 * (sigT (fun (t : AddBool.term) => no_bools t + yes_bools t)) and AddBool.term.
 * We can use a split eliminator and lift to the normal one?
 *)
