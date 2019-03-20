Require Import Vector.
Require Import List.

Require Import Ornamental.Ornaments.

(* TODO clean up, move the user-friendly index stuff *)

From Coq Require Import ssreflect ssrbool ssrfun.

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

Print eqrel.

Theorem zip_with_is_zip {A} {B} :
  zip_with (@pair A B) =2 zip.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

End hs_to_coq'.


(* --- Preprocess --- *)

Preprocess Module hs_to_coq' as hs_to_coq.

(* --- Search --- *)

Find ornament list Vector.t as ltv.

(* --- Lift --- *)

Lift list Vector.t in hs_to_coq.zip as zipV'.
Lift list Vector.t in hs_to_coq.zip_with as zip_withV'.
Lift list Vector.t in hs_to_coq.zip_with_is_zip as zip_with_is_zipV'.

(* --- Unpack --- *)

Require Import Coq.Logic.EqdepFacts.

Unpack zipV' as zipV.
Unpack zip_withV' as zip_withV.
Unpack zip_with_is_zipV' as zip_with_is_zipV.

(* Enable implicit arguments *)
Arguments zipV {_ _} {_} _ {_} _.
Arguments zip_withV {_ _ _} _ {_} _ {_} _.
Arguments zip_with_is_zipV {_ _} {_} _ {_} _.

(* For any two vectors of the same length, we get a vector of the same length *)
Eval compute in (zipV (Vector.cons nat 2 0 (Vector.nil nat)) (Vector.cons nat 1 0 (Vector.nil nat))).

(*
 * Obligations for the user-friendly version.
 * Some aux lemmas first:
 *)
Lemma vector_nil:
  forall {a} (v : Vector.t a 0),
     v = Vector.nil a.
Proof.
  intros a. apply Vector.case0. auto.
Qed.

Lemma vector_hd_tl:
  forall {a} {n} v,
    v = Vector.cons a (Vector.hd v) n (Vector.tl v).
Proof.
  intros a. apply Vector.caseS. auto.
Qed.

(* So one user-friendly version is just: *)
Program Definition zipV_uf {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) :=
  zipV v1 v2
: Vector.t (a * b) n.
Next Obligation.
  induction n.
  - rewrite (vector_nil v1).
    rewrite (vector_nil v2).
    auto.
  - rewrite (vector_hd_tl v1).
    rewrite (vector_hd_tl v2).
    simpl. f_equal. apply IHn.
Defined.

(* And this is super formulaic: *)
Program Definition zip_withV_uf {A} {B} {C} f {n} (v1 : Vector.t A n) (v2 : Vector.t B n) :=
  zip_withV f v1 v2
: Vector.t C n.
Next Obligation.
  induction n.
  - rewrite (vector_nil v1).
    rewrite (vector_nil v2).
    auto.
  - rewrite (vector_hd_tl v1).
    rewrite (vector_hd_tl v2).
    simpl. f_equal. apply IHn.
Defined.

(* TODO clean up and make a methodology; show similarly for the other ones   *)

(* Client code *)

Definition BVand' {n : nat} (v1 : Vector.t bool n) (v2 : Vector.t bool n) : Vector.t bool n :=
  zip_withV_uf andb v1 v2.

(*  TODO maybe use proof, and maybe interface back with lists *)