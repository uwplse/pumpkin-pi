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
Definition zipV {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) :=
  projT2 (zipV' a b (existT _ n v1) (existT _ n v2)).

Definition zip_withV {A} {B} {C} {n} (f : A -> B -> C) (v1 : Vector.t A n) (v2 : Vector.t B n) :=
  projT2 (zip_withV' A B C f (existT _ n v1) (existT _ n v2)).

Check sigT.

(* TODO this is the thing you need everywhere for automation *)
Lemma rewrite_proj :
  forall {A} {T : A -> Type} (s : sigT T), 
    s = existT _ (projT1 s) (projT2 s).
Proof.
  intros. induction s. auto.
Defined.

Program Definition zip_with_is_zipV {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n) :=
  eq_sigT_eq_dep _ _ _ _ 
    (zip_withV pair v1 v2) 
    (zipV v1 v2)
    (zip_with_is_zipV' A B (existT _ n v1) (existT _ n v2)).
Next Obligation. apply rewrite_proj. Qed.
Next Obligation. apply rewrite_proj. Qed.

Check zip_with_is_zipV.

(* For any two vectors, we get a vector of the same length *)
Eval compute in (zipV (Vector.cons nat 2 0 (Vector.nil nat)) (Vector.cons nat 1 0 (Vector.nil nat))).

(*
 * Obligations for the user-friendly version.
 * Some aux lemmas first:
 *)
Lemma vector_nil:
  forall {a} (v : Vector.t a 0),
     v = Vector.nil a.
Proof.
  intros a. eapply Vector.case0. eauto.
Qed.

Lemma vector_hd_tl:
  forall {a} {n} v,
    v = Vector.cons a (Vector.hd v) n (Vector.tl v).
Proof.
  intros a. eapply Vector.caseS. eauto.
Qed.

(* Then it's very formulaic to show this: *)
Lemma user_obligation1:
  forall a b n v1 v2,
    (projT1 (zipV' a b (existT _ n v1) (existT _ n v2))) = n.
Proof.
  intros. induction n.
  - rewrite (vector_nil v1). 
    rewrite (vector_nil v2).
    auto.
  - rewrite (vector_hd_tl v1). 
    rewrite (vector_hd_tl v2).
    simpl. f_equal. apply IHn.
Defined.

(* So one user-friendly version is just: *)
Definition zipV_uf {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) :
  Vector.t (a * b) n.
Proof.
  pose proof (zipV v1 v2) as z. simpl in z.
  rewrite user_obligation1 in z.
  auto.
Defined.

Print zipV_uf.

(* TODO clean up and make a methodology; show similarly for the other ones *)

(* Client code *)

Definition BVand' {n : nat} :=
  @zip_withV _ _ _ n andb.

(*  TODO maybe use proof, and maybe interface back with lists