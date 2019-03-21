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

(* 
 * TODO We must redefine these, since we need them not to be opaque
 * if the user wants to avoid using UIP at a given type to produce 
 * user-friendly proofs. The unpack automation should use these 
 * non-opaque versions. We should move these appropriately.
 *)
Definition eq_dep_eq_sigT (U : Type) (P : U -> Type) (p q : U) (x : P p) (y : P q) (H : eq_dep U P p x q y) : existT P p x = existT P q y :=
  match H in (eq_dep _ _ _ _ q0 y0) return (existT P p x = existT P q0 y0) with
  | eq_dep_intro _ _ _ _ => erefl (existT P p x)
  end.

Definition eq_sigT_eq_dep (U : Type) (P : U -> Type) (p q : U) (x : P p) (y : P q) (H : existT P p x = existT P q y) : eq_dep U P p x q y :=
  @eq_ind_r _
    (existT _ q y)
    (fun s => eq_dep U P (projT1 s) (projT2 s) q y)
    (eq_dep_intro U P q y) 
    (existT _ p x) 
    H.

Definition eq_dep_trans (U : Type) (P : U -> Type) (p q r : U) (x : P p) (y : P q) (z : P r) (H : eq_dep U P p x q y) : eq_dep U P q y r z -> eq_dep U P p x r z :=
  match H in (eq_dep _ _ _ _ q0 p0) return (eq_dep U P q0 p0 r z -> eq_dep U P p x r z) with
  | eq_dep_intro _ _ _ _ => id
  end.

Definition eq_dep_sym (U : Type) (P : U -> Type) (p q : U) (x : P p) (y : P q) (H : eq_dep U P p x q y) : eq_dep U P q y p x :=
  match H in (eq_dep _ _ _ _ q0 p0) return (eq_dep U P q0 p0 p x) with
  | eq_dep_intro _ _ _ _ => eq_dep_intro U P p x
  end.

Program Definition zip_with_is_zipV {A} {B} {n1} (v1 : Vector.t A n1) {n2} (v2 : Vector.t B n2) :=
  eq_sigT_eq_dep _ _ _ _ 
    (zip_withV pair v1 v2) 
    (zipV v1 v2)
    (zip_with_is_zipV' A B (existT _ n1 v1) (existT _ n2 v2)).
Next Obligation. apply rewrite_proj. Defined.
Next Obligation. apply rewrite_proj. Defined.

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

Import EqNotations.

(* So one user-friendly version is just: *)
Definition zipV_uf {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) : Vector.t (a * b) n :=
  rew (zipV_uf_aux v1 v2 eq_refl) in (zipV v1 v2).

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
Definition zip_withV_uf {A} {B} {C} f {n} (v1 : Vector.t A n) (v2 : Vector.t B n) : Vector.t C n :=
  rew (zip_withV_uf_aux f v1 v2 eq_refl) in (zip_withV f v1 v2).

(*
 * For proofs, we have to deal with dependent equality.
 * Here's a lemma that can help us. It basically relates the
 * auxiliary lemmas from the other proofs.
 *
 * Via Jasper Hugunin, one way we can show this is using the fact 
 * that nats form an hset. Then, we don't actually need any information
 * about how our auxiliary equalities are formed.
 *)

From Coq Require Import Eqdep_dec Arith.

(*
 * Connect our user-friendly and generated functions.
 *)
Lemma zip_with_is_zipV_uf_aux1:
  forall {A} {B} {C} (f : A -> B -> C) {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    eq_dep _ _ _ (zip_withV_uf f v1 v2) _ (zip_withV f v1 v2).
Proof.
  intros. apply eq_sigT_eq_dep. apply eq_sigT_sig_eq. 
  econstructor. apply rew_opp_l.
Defined.

Lemma zip_with_is_zipV_uf_aux2:
  forall {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    eq_dep _ _ _ (zipV_uf v1 v2) _ (zipV v1 v2).
Proof.
  intros. apply eq_sigT_eq_dep. apply eq_sigT_sig_eq. 
  econstructor. apply rew_opp_l.
Defined.

(*
 * Now state the aux lemma
 *)
Lemma zip_with_is_zipV_uf_aux:
  forall {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    eq_dep _ _ _ (zip_withV_uf pair v1 v2) _ (zipV_uf v1 v2).
Proof.
  intros. eapply eq_dep_trans.
  - apply zip_with_is_zipV_uf_aux1.
  - eapply eq_dep_trans.
    + apply zip_with_is_zipV.
    + apply eq_dep_sym. apply zip_with_is_zipV_uf_aux2.
Defined.

(*
 * Then we can get our theorem (TODO clean):
 *)
Lemma zip_with_is_zipV_uf :
  forall {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n),
    zip_withV_uf pair v1 v2 = zipV_uf v1 v2.
Proof.
  intros.
  pose (eq_sigT_snd (eq_dep_eq_sigT _ _ _ _ _ _ (zip_with_is_zipV_uf_aux v1 v2))).
  rewrite <- e.
  induction v1.
  - simpl.
  unfold eq_sigT_fst. unfold eq_dep_eq_sigT. simpl.
  induction v1.
  - simpl.  
  unfold eq_sigT_fst.
  apply eq_sym.
  apply eq_sigT_snd.
  unfold zip_with_is_zipV_uf_aux .
  simpl.
  unfold eq_dep_trans.
  simpl.
  compute.
  reflexivity.
  destruct e.
  simpl.

  pose (eq_sigT_snd (eq_dep_eq_sigT _ _ _ _ _ _ (zip_with_is_zipV_uf_aux v1 v2))).

  rewrite <- e.
  unfold eq_sigT_fst.
  simpl.
  unfold eq_dep_eq_sigT.
  unfold zip_with_is_zipV_uf_aux
  simpl.  
  auto.
  simpl in H.

  inversion H. destruct H2.

 unfold zip_withV_uf. unfold zipV_uf.
  pose (eq_sigT_snd (eq_dep_eq_sigT _ _ _ _ _ _ (zip_with_is_zipV v1 v2))).
  rewrite <- e. unfold zip_with_is_zipV. simpl.
  simpl in e.
  rewrite <- e.
  rewrite <- eq_trans_rew_distr.
  unfold zip_with_is_zipV.
  simpl.
  rewrite zip_with_is_zipV_uf_aux_uip.

Defined.

(* Client code *)

Definition BVand' {n : nat} (v1 : Vector.t bool n) (v2 : Vector.t bool n) : Vector.t bool n := 
  zip_withV_uf andb v1 v2.
