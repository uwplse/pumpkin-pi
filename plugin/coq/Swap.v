(*
 * Tests for swapping/moving constructors
 *)

Require Import List.
Require Import String.
Require Import ZArith.

Import ListNotations.

Require Import Ornamental.Ornaments.
Set DEVOID search prove equivalence.
Set DEVOID lift type.

(* TODO test outcomes (if #changes, will break, whereas now won't change) *)
(* TODO try w/ dependent indices too *)
(* TODO clean & make tutorial-like *)

(* --- Swap the only constructor --- *)

Inductive list' (T : Type) : Type :=
| cons' : T -> list' T -> list' T
| nil' : list' T.

Preprocess Module List as List_pre { opaque (* ignore these: *)
  (* dependent elimination only: *)
  RelationClasses.StrictOrder_Transitive
  RelationClasses.StrictOrder_Irreflexive
  RelationClasses.Equivalence_Symmetric
  RelationClasses.Equivalence_Transitive
  RelationClasses.PER_Symmetric
  RelationClasses.PER_Transitive
  RelationClasses.Equivalence_Reflexive
  (* proofs about these match over the above opaque terms, and would fail: *)
  Nat.add
  Nat.sub
}.
Lift Module list list' in List_pre as List'.

Lemma my_lemma:
  forall (T : Type) (l : list' T),
    List'.Coq_Init_Datatypes_app T l (nil' T) = List'.Coq_Init_Datatypes_app T (nil' T) l.
Proof.
  intros T l. induction l.
  - simpl. simpl in IHl. rewrite IHl. reflexivity.
  - reflexivity.
Defined.

Lift list' list in my_lemma as my_lemma_lifted.

(* --- An ambiguous swap --- *)

(*
 * This type comes from the REPLICA benchmarks.
 * This is a real user change (though there were other
 * changes at the same time). We don't include the user's
 * admitted theorems.
 *)

Definition Identifier := string.
Definition id_eq_dec := string_dec.

Inductive Term : Set :=
  | Var : Identifier -> Term
  | Int : Z -> Term
  | Eq : Term -> Term -> Term
  | Plus : Term -> Term -> Term
  | Times : Term -> Term -> Term
  | Minus : Term -> Term -> Term
  | Choose : Identifier -> Term -> Term.

Module User5Session19.

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

Preprocess Module User5Session19 as User5Session19_pre.

Inductive Term' : Set :=
  | Var' : Identifier -> Term'
  | Eq' : Term' -> Term' -> Term'
  | Int' : Z -> Term'
  | Plus' : Term' -> Term' -> Term'
  | Times' : Term' -> Term' -> Term'
  | Minus' : Term' -> Term' -> Term'
  | Choose' : Identifier -> Term' -> Term'.

(*
 * Note the swap here is ambiguous because we don't know
 * which constructor we swapped Int with. It could have been Eq,
 * but also Plus, Times, or Minus. So we should drop into
 * proof mode and ask the user when this happens.
 *)

Fail Find ornament Term Term'. (* for now, we tell the user to pick one via an error *)
Find ornament Term Term' { mapping 0 }. (* we pick one this way *)

(*
 * We can now lift everything:
 *)
Lift Module Term Term' in User5Session19_pre as User5Session19'.

(* --- A more ambiguous swap --- *)

(*
 * We can continue down that line but this time swap two
 * constructors with the same type.
 *)

Inductive Term'' : Set :=
  | Var'' : Identifier -> Term''
  | Eq'' : Term'' -> Term'' -> Term''
  | Int'' : Z -> Term''
  | Minus'' : Term'' -> Term'' -> Term''
  | Plus'' : Term'' -> Term'' -> Term''
  | Times'' : Term'' -> Term'' -> Term''
  | Choose'' : Identifier -> Term'' -> Term''.

Find ornament Term' Term'' { mapping 8 }.

Lift Module Term' Term'' in User5Session19' as User5Session19''.

(* --- Note that we can do several swaps at once --- *)

Inductive Term''' : Set :=
  | Var''' : Identifier -> Term'''
  | Eq''' : Term''' -> Term''' -> Term'''
  | Int''' : Z -> Term'''
  | Minus''' : Term''' -> Term''' -> Term'''
  | Plus''' : Term''' -> Term''' -> Term'''
  | Times''' : Term''' -> Term''' -> Term'''
  | Choose''' : Identifier -> Term''' -> Term'''.

Find ornament Term Term''' { mapping 8 }.

Lift Module Term Term''' in User5Session19_pre as User5Session19'''.

(* --- Renaming --- *)

(*
 * Note that renaming constructors is just the identity swap.
 *)

Inductive Expr : Set :=
  | Name : Identifier -> Expr
  | Equal : Expr -> Expr -> Expr
  | Number : Z -> Expr
  | Subtract : Expr -> Expr -> Expr
  | Add : Expr -> Expr -> Expr
  | Multiply : Expr -> Expr -> Expr
  | Choice : Identifier -> Expr -> Expr.

Find ornament Term''' Expr { mapping 0 }.

Lift Module Term''' Expr in User5Session19''' as CustomRenaming.

(* --- Large and ambiguous --- *)

(*
 * TODO explain
 * TODO then implement w/ "Save ornament" to try to prove section/retraction 
 *)

Inductive Enum : Set :=
| e1 : Enum
| e2 : Enum
| e3 : Enum
| e4 : Enum
| e5 : Enum
| e6 : Enum
| e7 : Enum
| e8 : Enum
| e9 : Enum
| e10 : Enum
| e11 : Enum
| e12 : Enum
| e13 : Enum
| e14 : Enum
| e15 : Enum
| e16 : Enum
| e17 : Enum
| e18 : Enum
| e19 : Enum
| e20 : Enum
| e21 : Enum
| e22 : Enum
| e23 : Enum
| e24 : Enum
| e25 : Enum
| e26 : Enum
| e27 : Enum
| e28 : Enum
| e29 : Enum
| e30 : Enum.

Inductive Enum' : Set :=
| e1' : Enum'
| e2' : Enum'
| e3' : Enum'
| e4' : Enum'
| e5' : Enum'
| e6' : Enum'
| e7' : Enum'
| e8' : Enum'
| e9' : Enum'
| e10' : Enum'
| e11' : Enum'
| e12' : Enum'
| e13' : Enum'
| e14' : Enum'
| e15' : Enum'
| e16' : Enum'
| e17' : Enum'
| e18' : Enum'
| e19' : Enum'
| e20' : Enum'
| e21' : Enum'
| e22' : Enum'
| e23' : Enum'
| e24' : Enum'
| e25' : Enum'
| e26' : Enum'
| e27' : Enum'
| e28' : Enum'
| e29' : Enum'
| e30' : Enum'.

Find ornament Enum Enum' { mapping 0 }.

Definition is_e10 (e : Enum) :=
match e with
| e10 => True
| _ => False
end.

Preprocess is_e10 as is_e10_pre.
Lift Enum Enum' in is_e10_pre as is_e10'.

Lemma e10'_is_e10':
  is_e10' e10'.
Proof.
  reflexivity.
Defined.

(* --- Custom mapping --- *)

(*
 * If the mapping we want doesn't show up in the top 50 candidates, we can
 * supply our own using "Save ornament". For now, we need to give both functions,
 * and it doesn't prove anything for us; later, should be able to automatically
 * invert the function and prove section/retraction (TODO).
 *)

Program Definition Enum_Enum' : Enum -> Enum'.
Proof.
  intros e. induction e.
  - apply e30'.
  - apply e29'.
  - apply e28'.
  - apply e27'.
  - apply e26'.
  - apply e25'.
  - apply e24'.
  - apply e23'.
  - apply e22'.
  - apply e21'.
  - apply e20'.
  - apply e19'.
  - apply e18'.
  - apply e17'.
  - apply e16'.
  - apply e15'.
  - apply e14'.
  - apply e13'.
  - apply e12'.
  - apply e11'.
  - apply e10'.
  - apply e9'.
  - apply e8'.
  - apply e7'.
  - apply e6'.
  - apply e5'.
  - apply e4'.
  - apply e3'.
  - apply e2'.
  - apply e1'.
Defined.

(*
 * DEVOID can automatically infer the opposite direction
 *)
Save ornament Enum Enum' { promote = Enum_Enum' }.

Definition is_e3 (e : Enum) :=
match e with
| e3 => True
| _ => False
end.

Preprocess is_e3 as is_e3_pre.
Lift Enum Enum' in is_e3_pre as is_e28'.

Lemma e28'_is_e28':
  is_e28' e28'.
Proof.
  reflexivity.
Defined.

Definition is_e3' (e : Enum') :=
match e with
| e3' => True
| _ => False
end.

Preprocess is_e3' as is_e3'_pre.
Lift Enum' Enum in is_e3'_pre as is_e28.

Lemma e28_is_e28:
  is_e28 e28.
Proof.
  reflexivity.
Defined.

(*
 * Likewise, we can just provide forget (could also do both):
 *)
Program Definition Enum'_Enum : Enum' -> Enum.
Proof.
  intros e. induction e.
  - apply e30.
  - apply e29.
  - apply e28.
  - apply e27.
  - apply e26.
  - apply e25.
  - apply e24.
  - apply e23.
  - apply e22.
  - apply e21.
  - apply e20.
  - apply e19.
  - apply e18.
  - apply e17.
  - apply e16.
  - apply e15.
  - apply e14.
  - apply e13.
  - apply e12.
  - apply e11.
  - apply e10.
  - apply e9.
  - apply e8.
  - apply e7.
  - apply e6.
  - apply e5.
  - apply e4.
  - apply e3.
  - apply e2.
  - apply e1.
Defined.

Save ornament Enum Enum' { forget = Enum'_Enum }.

Definition is_e2' (e : Enum') :=
match e with
| e2' => True
| _ => False
end.

Preprocess is_e2' as is_e2'_pre.
Lift Enum' Enum in is_e2'_pre as is_e29.

Lemma e29_is_e29:
  is_e29 e29.
Proof.
  reflexivity.
Defined.

Definition is_e2 (e : Enum) :=
match e with
| e2 => True
| _ => False
end.

Preprocess is_e2 as is_e2_pre.
Lift Enum Enum' in is_e2_pre as is_e29'.

Lemma e29'_is_e29':
  is_e29' e29'.
Proof.
  reflexivity.
Defined.


