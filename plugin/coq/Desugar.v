Add LoadPath "coq".
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import List.

Arguments consV {A}.
Arguments nilV {A}.

(** Simple examples, using only match terms (no fix) **)

Definition empty (A : Type) (xs : list A) : bool :=
  match xs with
  | cons _ _ => false
  | nil => true
  end.
Desugar empty as empty'.
Lift list vector in empty' as emptyV'.

Definition emptyV (A : Type) (xs : {n:nat & vector A n}) : bool :=
  match projT2 xs with
  | consV _ _ _ => false
  | nilV => true
  end.
Desugar emptyV as emptyV''.

(* NOTE: Using tricky index reasoning to cover edge case. *)
Definition headV (A : Type) (n : nat) (xs : vector A (S n)) : A :=
  match xs in vector _ n return (match n with S _ => True | O => False end) -> A with
  | consV _ x _ => True_rect x
  | nilV => False_rect A
  end
    I.
Desugar headV as headV'.

Definition tailV (A : Type) (n : nat) (xs : vector A (S n)) : vector A n :=
  match xs in vector _ (S n) return vector A n with
  | consV _ _ xs => xs
  end.
Desugar tailV as tailV'.

(** Simple examples, using fix and match terms **)

Desugar length as length'.
Desugar app as app'.
Desugar list_prod as list_prod'.
