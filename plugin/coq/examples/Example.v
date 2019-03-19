Require Import Vector.
Require Import List.

Require Import Ornamental.Ornaments.

From Coq Require Import ssreflect ssrbool ssrfun.

(*
 * Here is our library that we will lift.
 *)
Module hs_to_coq'.

(* From:
 * https://github.com/antalsz/hs-to-coq/blob/master/base/GHC/List.v
 *)
Definition zip {a} {b} : list a -> list b -> list (a * b)%type :=
  fix zip arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, _bs => nil
           | _as, nil => nil
           | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
end.

(* From:
 * https://github.com/antalsz/hs-to-coq/blob/master/core-semantics-no-values/semantics.v
 *)
Fixpoint zip_with {A} {B} {C} (f : A -> B -> C) (s : list A) (t : list B) : list C :=
  match s , t with
    | a :: s' , b :: t' => f a b :: zip_with f s' t'
    | _       , _       => nil
end.

Theorem zip_with_is_zip {A} {B} :
  zip_with (@pair A B) =2 zip.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

End hs_to_coq'.

(* --- Preprocess --- *)

Desugar Module hs_to_coq' as hs_to_coq.

(* --- Search --- *)

Find ornament list Vector.t as ltv.

(* --- Lift --- *)

Lift list Vector.t in hs_to_coq.zip as zipV'.
Lift list Vector.t in hs_to_coq.zip_with as zip_withV'.
Lift list Vector.t in hs_to_coq.zip_with_is_zip as zip_with_is_zipV'.

(* --- Unpack --- *)

Require Import Coq.Logic.EqdepFacts.

(* TODO add in Nate's automation here *)
Definition zipV {a} {b} {n1} (v1 : Vector.t a n1) {n2} (v2 : Vector.t b n2) :=
  projT2 (zipV' a b (existT _ n1 v1) (existT _ n2 v2)).

Definition zip_withV {A} {B} {C} (f : A -> B -> C) {n1} (v1 : Vector.t A n1) {n2} (v2 : Vector.t B n2) :=
  projT2 (zip_withV' A B C f (existT _ n1 v1) (existT _ n2 v2)).

(* TODO this is the thing you need everywhere for automation *)
Lemma rewrite_proj :
  forall {A} {T : A -> Type} (s : sigT T), 
    s = existT _ (projT1 s) (projT2 s).
Proof.
  intros. induction s. auto.
Defined.

Program Definition zip_with_is_zipV {A} {B} {n1} (v1 : Vector.t A n1) {n2} (v2 : Vector.t B n2) :=
  eq_sigT_eq_dep _ _ _ _ 
    (zip_withV pair v1 v2) 
    (zipV v1 v2)
    (zip_with_is_zipV' A B (existT _ n1 v1) (existT _ n2 v2)).
Next Obligation. apply rewrite_proj. Qed.
Next Obligation. apply rewrite_proj. Qed.

Check zip_with_is_zipV.

(* For any two vectors of the same length, we get a vector of the same length *)
Eval compute in (zipV (Vector.cons nat 2 0 (Vector.nil nat)) (Vector.cons nat 1 0 (Vector.nil nat))).

(*
 * Obligations for the user-friendly version.
 * First, just prove the indexer is what we want assuming an equality
 * n1 = n2. This will involve just inducting over each argument in order,
 * and the rest is straightforward: Make use of the equality,
 * base case holds by definition, and the inductive case uses f_equal
 * to make use of the inductive hypothesis.
 *)
Lemma zipV_uf_aux:
  forall {a} {b} {n1} (v1 : Vector.t a n1) {n2} (v2 : Vector.t b n2),
    n1 = n2 ->
    projT1 (zipV' a b (existT _ n1 v1) (existT _ n2 v2)) = n1.
Proof.
  induction v1, v2; intros; inversion H. 
  - auto.
  - simpl. f_equal. apply IHv1. auto.
Defined.

(* So one user-friendly version is just: *)
Program Definition zipV_uf {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) :=
  zipV v1 v2
: Vector.t (a * b) n.
Next Obligation.
  auto using zipV_uf_aux.
Defined.

(* Similarly: *)
Lemma zip_withV_uf_aux:
  forall {A} {B} {C} f {n1} (v1 : Vector.t A n1) {n2} (v2 : Vector.t B n2) ,
    n1 = n2 ->
    projT1 (zip_withV' A B C f (existT _ n1 v1) (existT _ n2 v2)) = n1.
Proof.
  induction v1, v2; intros; inversion H. 
  - auto.
  - simpl. f_equal. apply IHv1. auto.
Defined.

(* And: *)
Program Definition zip_withV_uf {A} {B} {C} f {n} (v1 : Vector.t A n) (v2 : Vector.t B n) :=
  zip_withV f v1 v2
: Vector.t C n.
Next Obligation.
  auto using zip_withV_uf_aux.
Defined.

(* TODO ideally, figure out proof too *)
(*
Lemma zip_with_is_zipV_uf :
  forall {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    zip_withV_uf pair v1 v2 = zipV_uf v1 v2.
Proof.
  ??
Defined.
*)

(* Client code *)

Definition BVand' {n : nat} (v1 : Vector.t bool n) (v2 : Vector.t bool n) : Vector.t bool n := 
  zip_withV_uf andb v1 v2.

(*  TODO maybe use proof, and maybe interface back with lists