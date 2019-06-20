(*
 * This file explains the assumptions from Section 3 in more detail,
 * and demonstrates some failing examples.
 *
 * These assumptions are not core to the type theory or to the
 * original definition of algebraic ornaments. Accordingly, this 
 * file can be viewed as a suite of test cases we'd eventually 
 * like to pass.
 *)

Require Import Ornamental.Ornaments.
Require Import List.

(* --- Same number of constructors --- *)

(*
 * We require that B has the same number of constructors in
 * the same order as A. We cannot, for example,
 * find this ornament:
 *)

Inductive vector3 (T : Type) : nat -> Type :=
| nilV3 : vector3 T 0
| nilV3' : vector3 T 0
| consV3 : forall (n : nat), T -> vector3 T n -> vector3 T (S n).

Fail Find ornament list vector3 as ltv3.

(* --- Same order of constructors --- *)

Definition vector_flip (T : Type) : nat -> Type :=
| consV : forall (n : nat), T -> vector_flip T n -> vector_flip T (S n)
- 


 * This restriction exists to simplify
 * search. S
 *)

(* 
B has the same number of constructors in the same order as A ,
I B is not A ,
A and B do not contain recursive references to themselves under products, and
for every recursive reference to A in A , there is exactly one new hypothesis in B , which
is exactly the new index of the corresponding recursive reference in B .*)


(* --- --- *)

(* t is well-typed and fully η -expanded,
t does not apply promote or forget , and
t does not reference B*)

(* he specification for
the forgetful direction is similar, with extra restrictions on how B is used within t .*)
