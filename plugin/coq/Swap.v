(*
 * DEVOID supports swapping and renaming constructors!
 * Here are some examples.
 *)

Require Import List.
Require Import String.
Require Import ZArith.
Require Import Vector.

Import ListNotations.

Require Import Ornamental.Ornaments.
Set DEVOID search prove equivalence.
Set DEVOID lift type.

(* --- Swap the only constructor --- *)

(*
 * Here we simply flip the constructors of list and then
 * lift the entire list module:
 *)
Inductive list' (T : Type) : Type :=
| cons' : T -> list' T -> list' T
| nil' : list' T.

(* Preprocess for lifting: *)
Preprocess Module List as List_pre { opaque (* ignore these nested modules: *)
  RelationClasses
  Nat Coq.Init.Nat 
  Coq.Init.Logic Coq.Init.Peano
  Coq.Init.Datatypes.list_ind Coq.Init.Datatypes.list_rect Coq.Init.Datatypes.list_rec
  Coq.Init.Datatypes.nat_ind Coq.Init.Datatypes.nat_rect Coq.Init.Datatypes.nat_rec
  eq_ind eq_ind_r eq_rec eq_rec_r eq_rect eq_rect_r
}.

(* Lift the whole list module: *)
Repair Module list list' in List_pre as List' { 
opaque (* ignore these, just for speed *)
  RelationClasses.Equivalence_Reflexive
  RelationClasses.reflexivity
  Nat.add
  Nat.sub
  Nat.lt_eq_cases
  Nat.compare_refl
  Nat.lt_irrefl
  Nat.le_refl
  Nat.bi_induction
  Nat.central_induction
  Nat.sub_succ;
hint (* some tacic hints for better scripts *)
  "auto"
}.

(* That should generate tactics for a whole bunch of these, but just to check
   the paper example (has explicit A whereas paper has implicit A,
   and passes in a tactic hint to try auto instead of reflexivity): *)
Repair list list' in List_pre.rev_app_distr as rev_app_distr' { hint "auto" }. 
(* The tactics for section and retraction are in the output of Repair Module above
   (at the top). *)

(* Example from the overview that shows append is OK *)
Definition swap := List'.list_to_list'.
Definition app' := List'.Coq_Init_Datatypes_app.
Definition app := List_pre.Coq_Init_Datatypes_app.
Lemma app_ok:
  forall T (l1 l2 : list T),
    swap T (app T l1 l2) =
    app' T (swap T l1) (swap T l2).
Proof.
  intros. induction l1.
  - auto.
  - simpl. rewrite IHl1. reflexivity.
Defined.
(*
 * We get this for free, whereas the original tactic script doesn't work here,
 * so even for a single proof we save development time.
 * We have all of the updated functions and proofs here with no additional effort.
 * To get tactics that match the original style, though, we might still need
 * to tweak the original script.
 *
 * So we get a significant time savings over manually fixing the entire standard 
 * library (no time for every single function and proof, while a number of the
 * functions and proofs break), but for now at some cost to readability.
 * See this video for a comparison: https://www.youtube.com/watch?v=JINV13wNgIQ
 *
 * If we want readable proofs that match the original style, we may need to tweak
 * the output tactic scripts, which may add back some effort (though for the proof
 * above it is simple).
 *)

(* The tactics for section and retraction are in the output of Repair Module. *)

(* A small test in the opposite direction that doesn't rely on caching: *)
Lemma my_lemma:
  forall (T : Type) (l : list' T),
    List'.Coq_Init_Datatypes_app T l (nil' T) = List'.Coq_Init_Datatypes_app T (nil' T) l.
Proof.
  intros T l. induction l.
  - simpl. simpl in IHl. rewrite IHl. reflexivity.
  - reflexivity.
Defined.

Repair list' list in my_lemma as my_lemma_lifted.

(* Trying the above suggested tactics:*)
Lemma my_lemma_lifted_test:
  forall (T : Type) (l : list T),
   List_pre.Coq_Init_Datatypes_app T l [] =
   List_pre.Coq_Init_Datatypes_app T [] l.
Proof.
  intros T l. induction l as [ |t l0 IHl].
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Defined.

(* --- Composing with algebraic ornaments --- *)

(*
 * We can compose this with an algebraic ornament:
 *)
Inductive vector' (T : Type) : nat -> Type :=
| consV' : T -> forall (n : nat), vector' T n -> vector' T (S n)
| nilV' : vector' T 0.

(* Suggested tactics sometimes aren't useful for dependent types yet, so we use Lift: *)
Lift list' vector' in List'.Coq_Init_Datatypes_app as appV'.
Lift list' vector' in my_lemma as my_lemmaV'.

Lift vector' Vector.t in appV' as appV.
Lift vector' Vector.t in my_lemmaV' as my_lemmaV.

(*
 * Note that these commute:
 *)
Lift list Vector.t in List_pre.Coq_Init_Datatypes_app as appV2.
Lift list Vector.t in my_lemma_lifted as my_lemmaV2.

Lemma test_app_commutes:
  appV = appV2.
Proof.
  reflexivity.
Qed.

Lemma test_my_lemma_commutes:
  my_lemmaV = my_lemmaV2.
Proof.
  reflexivity.
Qed.

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
 * We can now lift everything (failures are just silly attempts to lift record
 * projections twice;  safe to ignore them):
 *)
Lift Module Term Term' in User5Session19_pre as User5Session19'.
(*
 * Suggested tactics here would need some work (can generate them with Repair,
 * they just aren't very useful yet).
 *)

Lemma test_eval_eq_true_or_false:
  forall (L : User5Session19'.EpsilonLogic)
         env
         (t1 t2 : Term'),
       User5Session19'.eval L env (Eq' t1 t2) = User5Session19'.vTrue L \/
       User5Session19'.eval L env (Eq' t1 t2) = User5Session19'.vFalse L.
Proof.
  exact User5Session19'.eval_eq_true_or_false.
Qed.

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

(*
 * We can now lift everything (failures are just silly attempts to lift record
 * projections twice; safe to ignore them):
 *)
Lift Module Term' Term'' in User5Session19' as User5Session19''.

Lemma test_eval_eq_true_or_false_2:
  forall (L : User5Session19''.EpsilonLogic)
         env
         (t1 t2 : Term''),
       User5Session19''.eval L env (Eq'' t1 t2) = User5Session19''.vTrue L \/
       User5Session19''.eval L env (Eq'' t1 t2) = User5Session19''.vFalse L.
Proof.
  exact User5Session19''.eval_eq_true_or_false.
Qed.

(* --- Note that we can do several swaps at once --- *)

(*
 * This just skips an intermediate step and lifts from Term' directly to Term'',
 * though we redefine it as Term''' to break caching.
 *)

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

Lemma test_eval_eq_true_or_false_3:
  forall (L : User5Session19'''.EpsilonLogic)
         env
         (t1 t2 : Term'''),
       User5Session19'''.eval L env (Eq''' t1 t2) = User5Session19'''.vTrue L \/
       User5Session19'''.eval L env (Eq''' t1 t2) = User5Session19'''.vFalse L.
Proof.
  exact User5Session19'''.eval_eq_true_or_false.
Qed.

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

(*
 * We can now lift everything (failures are just silly attempts to lift record
 * projections twice; safe to ignore them):
 *)
Lift Module Term''' Expr in User5Session19''' as CustomRenaming.

Lemma test_eval_equal_true_or_false:
  forall (L : CustomRenaming.EpsilonLogic)
         env
         (e1 e2 : Expr),
       CustomRenaming.eval L env (Equal e1 e2) = CustomRenaming.vTrue L \/
       CustomRenaming.eval L env (Equal e1 e2) = CustomRenaming.vFalse L.
Proof.
  exact CustomRenaming.eval_eq_true_or_false.
Qed.

(* --- Large and ambiguous --- *)

(*
 * Here there are so many possible swaps that it makes no sense
 * to show all of them. We show 50. The first one is renaming:
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
 * supply our own using "Save ornament". We only need to provide "Save ornament"
 * with one of two directions. It can find the other for us and prove
 * the equivalence!
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
Defined.

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
Lift Enum' Enum in is_e3'_pre as is_e18.

Lemma e18_is_e18:
  is_e18 e18.
Proof.
  reflexivity.
Defined.

(*
 * The effort here is comparable since we supply the function, which is exactly
 * as hard as writing the updated functions for each of these. Though it would
 * likely save us development time to use PUMPKIN Pi if we were to look at not 
 * just functions, but also proofs, especially more complex proofs. Still, this 
 * scales to large ambiguous types without much overhead, just a single function.
 * We could just as well have provided forget.
 *
 * Do note that if you change the equivalence when you run
 * "Save ornament", this will not clear cached lifted terms,
 * which may give you confusing results later if you lift using
 * two different equivalences between the same types at different
 * points in your code that depend on one another. If this is a
 * problem for you, let us know and we can make it possible to
 * clear the lifting cache.
 *)
