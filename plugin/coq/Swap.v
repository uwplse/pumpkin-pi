(*
 * Tests for swapping/moving constructors
 *)

Require Import List.
Require Import String.
Require Import ZArith.
Require Import List.

Import ListNotations.

Require Import Ornamental.Ornaments.
Set DEVOID search prove equivalence.

(* TODO run w/ tests once done *)

(* --- Swap the only constructor --- *)

Inductive list' (T : Type) : Type :=
| cons' : T -> list' T -> list' T
| nil' : list' T.

Find ornament list list' as swap_list.

Check swap_list.
Check swap_list_inv.
Check swap_list_section.
Check swap_list_retraction.

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

Fail Find ornament Term' Term''. (* WIP *)

(* --- Renaming --- *)

(*
 * Note from the above that renaming constructors is just the identity swap.
 *)

Inductive Term''' : Set :=
  | Var''' : Identifier -> Term'''
  | Eq''' : Term''' -> Term''' -> Term'''
  | Num''' : Z -> Term'''
  | Minus''' : Term''' -> Term''' -> Term'''
  | Plus''' : Term''' -> Term''' -> Term'''
  | Times''' : Term''' -> Term''' -> Term'''
  | Choose''' : Identifier -> Term''' -> Term'''.

Fail Find ornament Term'' Term'''. (* WIP *)


(* TODO try w/ dependent indices too *)