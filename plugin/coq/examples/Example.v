Require Import Vector.
Require Import List.

Require Import Ornamental.Ornaments.

From Coq Require Import ssreflect ssrbool ssrfun.

Import EqNotations.

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

Preprocess Module hs_to_coq' as hs_to_coq.

(* --- Search --- *)

Find ornament list Vector.t as ltv.

(* --- Lift --- *)

Lift list Vector.t in hs_to_coq.zip as zipV'.
Lift list Vector.t in hs_to_coq.zip_with as zip_withV'.
Lift list Vector.t in hs_to_coq.zip_with_is_zip as zip_with_is_zipV'.

(* Here are our lifted types: *)
Check zipV'.
Check zip_withV'.
Check zip_with_is_zipV'.

(* --- Unpack --- *)

Unpack zipV' as zipV.
Unpack zip_withV' as zip_withV.
Unpack zip_with_is_zipV' as zip_with_is_zipV.

(* Enable implicit arguments *)
Arguments zipV {_ _} {_} _ {_} _.
Arguments zip_withV {_ _ _} _ {_} _ {_} _.
Arguments zip_with_is_zipV {_ _} {_} _ {_} _.

(* Here are our unpacked types: *)
Check zipV.
Check zip_withV.
Check zip_with_is_zipV.

(* --- Interface --- *)

(* For any two vectors of the same length, we get a vector of the same length *)
Eval compute in (zipV (Vector.cons nat 2 0 (Vector.nil nat)) (Vector.cons nat 1 0 (Vector.nil nat))).

(*
 * However, this type isn't actually what we want. The user-friendly
 * versions of the functions are simple to recover. 
 *
 * First, we will prove the indexer is what we want assuming an equality
 * n1 = n2. This will follow by induction over each argument,
 * and the rest will be straightforward: Substitute in the equality,
 * at which point the base case will hold by definition, and
 * the inductive case will follow by f_equal and the inductive hypothesis.
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

Lemma zip_withV_uf_aux:
  forall {A} {B} {C} f {n1} (v1 : Vector.t A n1) {n2} (v2 : Vector.t B n2) ,
    n1 = n2 ->
    projT1 (zip_withV' A B C f (existT _ n1 v1) (existT _ n2 v2)) = n1.
Proof.
  induction v1, v2; intros; inversion H.
  - auto.
  - simpl. f_equal. apply IHv1. auto.
Defined.

(* Our user friendly versions then follow by simple rewriting: *)
Definition zipV_uf {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) : Vector.t (a * b) n :=
  rew (zipV_uf_aux v1 v2 eq_refl) in (zipV v1 v2).

Definition zip_withV_uf {A} {B} {C} f {n} (v1 : Vector.t A n) (v2 : Vector.t B n) : Vector.t C n :=
  rew (zip_withV_uf_aux f v1 v2 eq_refl) in (zip_withV f v1 v2).

(*
 * For proofs, we have to deal with dependent equality.
 * This is more challenging. Essentially, we have to relate
 * our other equalities. In the case of nat, the easiest
 * way to do this is to use the fact that nats form an hset
 * (credit to Jasper Hugunin). Then, we don't actually need any information
 * about how our auxiliary equalities are formed. Otherwise,
 * the way those equalities are formed will matter.
 *)
From Coq Require Import EqdepFacts Eqdep_dec Arith.

Lemma zip_with_is_zipV_uf_aux :
  forall  {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    zip_withV_uf_aux pair v1 v2 eq_refl =
    eq_trans
      (eq_sigT_fst (eq_dep_eq_sigT_red _ _ _ _ _ _ (zip_with_is_zipV v1 v2)))
      (zipV_uf_aux v1 v2 eq_refl).
Proof.
  auto using (UIP_dec Nat.eq_dec).
Defined.

(*
 * Our theorem then follows:
 *)
Lemma zip_with_is_zipV_uf :
  forall {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    zip_withV_uf pair v1 v2 = zipV_uf v1 v2.
Proof.
  intros. unfold zip_withV_uf, zipV_uf, zipV.
  pose proof (eq_sigT_snd (eq_dep_eq_sigT_red _ _ _ _ _ _ (zip_with_is_zipV v1 v2))).
  simpl in *. rewrite <- H, zip_with_is_zipV_uf_aux. 
  apply eq_trans_rew_distr.
Defined.

(* Client code can then call our functions and proofs, for example: *)

Definition BVand' {n : nat} (v1 : Vector.t bool n) (v2 : Vector.t bool n) : Vector.t bool n :=
  zip_withV_uf andb v1 v2.
