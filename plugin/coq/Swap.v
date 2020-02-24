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

(* TODO run w/ tests once done *)
(* TODO try w/ dependent indices too *)

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
 * changes at the same time).
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

Find ornament Term' Term'' { mapping 3 }.

(* --- Note that we can do several swaps at once --- *)

Inductive Term''' : Set :=
  | Var''' : Identifier -> Term'''
  | Eq''' : Term''' -> Term''' -> Term'''
  | Int''' : Z -> Term'''
  | Minus''' : Term''' -> Term''' -> Term'''
  | Plus''' : Term''' -> Term''' -> Term'''
  | Times''' : Term''' -> Term''' -> Term'''
  | Choose''' : Identifier -> Term''' -> Term'''.

Find ornament Term Term''' { mapping 3 }.

(* --- Renaming --- *)

(*
 * Note from the above that renaming constructors is just the identity swap.
 *)

Inductive Term'''' : Set :=
  | Var'''' : Identifier -> Term''''
  | Eq'''' : Term'''' -> Term'''' -> Term''''
  | Num'''' : Z -> Term''''
  | Minus'''' : Term'''' -> Term'''' -> Term''''
  | Plus'''' : Term'''' -> Term'''' -> Term''''
  | Times'''' : Term'''' -> Term'''' -> Term''''
  | Choose'''' : Identifier -> Term'''' -> Term''''.

Find ornament Term''' Term'''' { mapping 0 }.

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





