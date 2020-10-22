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
 * Let's do more of the REPLICA benchmark and see what happens.
 * We start with the swap from Swap.v, then add the bool constructor.
 *
 * This is going to walk through more steps than actually needed long-term,
 * just to show the thought process.
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

(* --- What's new? --- *)

(*
 * To capture the new information, the first thing we are going to do is split
 * extended AddBool type in half: the left projection and the right projection,
 * essentially. We should be able to produce these automatically, I believe,
 * but for now let's write them manually.
 *)

(*
 * The left projection is straightforward---just use the same structure as
 * the old type, but index by the new type. I think Conor McBride said this
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




