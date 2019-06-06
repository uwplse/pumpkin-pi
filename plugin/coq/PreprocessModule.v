Require Import Ornamental.Ornaments.
Require List.

(*
 * NOTE: Any serious bug is likely to cause a typing error, and comparing the
 * exact output against some reference would give negligible further assurance
 * at the cost of unwieldiness. It would be very difficult to translate terms
 * only partially while preserving well-typedness.
 *)
Preprocess Module List as List' {include length, app}.

Print List'.


Eval compute in List.app.

(* 
    = fun A : Type =>
       fix app (l m : list A) {struct l} : list A :=
         match l with
         | nil => m
         | (a :: l1)%list => (a :: app l1 m)%list
         end
     : forall A : Type, list A -> list A -> list A
*)

Print List'.app.

Eval compute in List'.app.

(* 
 fun (A : Type) (l : list A) =>
       (fix F (l0 : list A) : list A -> list A :=
          match l0 with
          | nil => fun m : list A => m
          | (y :: l1)%list => fun m : list A => (y :: F l1 m)%list
          end) l
*)

Print nat_ind.

Program Definition nat_rect' :
forall (A : Type) (P : A -> Type) (pr : A -> nat) 
       (f : forall (a : A), pr a = 0 -> P a) 
       (f0 : forall (a : A), forall n : nat, (forall a', pr a' = n -> P a') -> (pr a = S n -> P a)),
forall (a : A), P a.
Proof.
  intros. remember (pr a). symmetry in Heqn. induction n in a, Heqn.
  - auto.
  - eapply f0; eauto.
Defined.

Print nat_rect'.

Eval compute in plus.

Preprocess Nat.add as plus'.
Print plus'.

(* 
fix add (n m : nat) {struct n} : nat :=
         match n with
         | 0 => m
         | S p => S (add p m)
         end
     : nat -> nat -> nat
*)

Definition plus'' : nat -> nat -> nat :=
fun n m : nat =>
nat_rect' (nat * nat) (fun _ : nat * nat => nat) fst (fun (m : nat * nat) _ => snd m)
  (fun (a : nat * nat) (n : nat) (add : forall (m : nat * nat), fst m = n -> nat) _ => 
  S (add (n, snd a) eq_refl)) (n, m).

Eval compute in plus''.

(* (f0 : forall (a : A), forall n : nat, (forall a', pr a' = n -> P a') -> (pr a = S n -> P a)),*)

fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | S n0 => f0 n0 (F n0)
  end.

Theorem foo:
  List.app = List'.app.
Proof.
  reflexivity.
Qed.

Eval compute in List.nth_error.

(*

     = fun A : Type =>
       fix nth_error (l : list A) (n : nat) {struct n} : 
       option A :=
         match n with
         | 0 => match l with
                | nil => None
                | (x :: _)%list => Some x
                end
         | S n0 =>
             match l with
             | nil => None
             | (_ :: l0)%list => nth_error l0 n0
             end
         end
     : forall A : Type, list A -> nat -> option A
*)

Print List'.nth_error.

Require Import Vector.

Print Vector.append.

Preprocess Vector.append as append'.

Print append'.
