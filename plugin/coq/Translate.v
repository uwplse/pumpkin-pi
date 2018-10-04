Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

Arguments consV {A}.
Arguments nilV {A}.

Definition empty (A : Type) (xs : list A) : bool :=
  match xs with
  | cons _ _ => false
  | nil => true
  end.
Translate matches in empty as empty'.
Lift list vector in empty' as emptyV'.

Definition emptyV (A : Type) (xs : {n:nat & vector A n}) : bool :=
  match projT2 xs with
  | consV _ _ _ => false
  | nilV => true
  end.
Translate matches in emptyV as emptyV''.

(* Note: headV and tailV use different methods to reason about the index in
 * order to improve coverage of potentially tricky edge cases.
 *)

Definition headV (A : Type) (n : nat) (xs : vector A (S n)) : A :=
  match xs in vector _ n return (match n with S _ => True | O => False end) -> A with
  | consV _ x _ => True_rect x
  | nilV => False_rect A
  end
    I.
Translate matches in headV as headV'.

Definition tailV (A : Type) (n : nat) (xs : vector A (S n)) : vector A n :=
  match xs in vector _ (S n) return vector A n with
  | consV _ _ xs => xs
  end.
Translate matches in tailV as tailV'.