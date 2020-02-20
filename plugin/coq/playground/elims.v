Add LoadPath "coq/playground".
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

Notation vector := Vector.t.
Notation nilV := Vector.nil.
Notation consV := Vector.cons.

Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.
Set DEVOID lift type.

From Coq Require Import ssreflect ssrbool ssrfun.
Import EqNotations.

(*
 * Attempt at understanding why lifting eliminators is OK, formally.
 *)

(* --- Algebraic ornaments --- *)

Definition sigT_vect_rect (A : Type) (P : {H : nat & vector A H} -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (l : {H : nat & vector A H}),
        P (existT (vector A) (projT1 l) (projT2 l)) ->
        P (existT (vector A) (S (projT1 l)) (consV A a (projT1 l) (projT2 l)))) 
  (l : {H : nat & vector A H}) :=
VectorDef.t_rect 
  A
  (fun (n : nat) (t : vector A n) => P (existT (vector A) n t))
  pnil
  (fun (h : A) (n : nat) (t : vector A n) (H : P (existT (vector A) n t)) =>
    pcons h (existT (vector A) n t) H) 
  (projT1 l) 
  (projT2 l).

Lift list vector in list_rect as sigT_vect_rect_lifted.
Lift vector list in sigT_vect_rect_lifted as list_rect_lifted.

Lemma lift_list_rect_correct: sigT_vect_rect_lifted = sigT_vect_rect.
Proof.
  reflexivity.
Qed.

Lemma lift_sigT_vect_rect_correct: list_rect_lifted = list_rect.
Proof.
  reflexivity.
Qed.

Definition list_rect_eta (A : Type) (P : list A -> Type)
  (pnil : P nil)
  (pcons : forall (a : A) (l : list A),
        P l ->
        P (cons a l))
  (l : list A) :=
@list_rect
  A
  (fun (l : list A) => P l)
  pnil
  (fun (h : A) (l : list A) (H : P l) =>
    pcons h l H) 
  l.

Definition path_rect_ltv_inv (A : Type) (P : list A -> Type) (s : sigT (vector A)):=
  P (list_to_t_inv A s).

Definition path_rect_ltv (A : Type) (P : sigT (vector A) -> Type) (l : list A):=
  P (list_to_t A l).

Definition list_rect_eta_1 (A : Type) (P : list A -> Type)
  (pnil : P nil)
  (pcons : forall (a : A) (l : list A),
        P l ->
        P (cons a l))
  (s : sigT (vector A)) :=
@list_rect
  A
  P
  pnil
  (fun (h : A) (l : list A) (H : P l) =>
    pcons h l H) 
  (list_to_t_inv A s).

Definition list_rect_eta_2 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : (path_rect_ltv A P) nil)
  (pcons : forall (a : A) (l : list A),
        (path_rect_ltv A P) l ->
        (path_rect_ltv A P) (cons a l))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : (path_rect_ltv A P) l) =>
    pcons h l H) 
  (list_to_t_inv A s).

Lemma path_rect_coh:
  forall (A : Type) (P : sigT (vector A) -> Type) (l : list A),
    (path_rect_ltv A P) l = P (list_to_t A l).
Proof.
  reflexivity.
Qed.

Definition list_rect_eta_3 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (list_to_t A nil))
  (pcons : forall (a : A) (l : list A),
        P (list_to_t A l) ->
        P (list_to_t A (cons a l)))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
    pcons h l H) 
  (list_to_t_inv A s).

Lemma refold_cons:
  forall (A : Type) (P : sigT (vector A) -> Type) (l : list A) (a : A),
    (list_to_t A (cons a l)) = existT (vector A) (S (list_to_t_index A l)) (consV A a (list_to_t_index A l) (projT2 (list_to_t A l))).
Proof.
  reflexivity.
Qed.

Definition list_rect_eta_4 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (list_to_t A nil))
  (pcons : forall (a : A) (l : list A),
        P (list_to_t A l) ->
        P (existT (vector A) (S (list_to_t_index A l)) (consV A a (list_to_t_index A l) (projT2 (list_to_t A l)))))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
    pcons h l H) 
  (list_to_t_inv A s).

Definition list_rect_eta_5 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P s->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
    pcons h (list_to_t A l) H) 
  (list_to_t_inv A s).

Check eq_rect.

Lemma path_ind_retract:
  forall A P (s : sigT (vector A)),
    path_rect_ltv A P (list_to_t_inv A s) ->
    P s.
Proof.
  intros. apply (@eq_rect (sigT (vector A)) (list_to_t A (list_to_t_inv A s)) _ X s (list_to_t_retraction A s)). 
Defined.

Definition list_rect_eta_6 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P s->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
path_ind_retract
  A
  P
  s
  (@list_rect
    A
    (path_rect_ltv A P)
    pnil
    (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
      pcons h (list_to_t A l) H) 
    (list_to_t_inv A s)).

Lemma path_ind_eta:
  forall A P (s : sigT (vector A)),
    P s ->
    P (existT (vector A) (projT1 s) (projT2 s)).
Proof.
  intros. induction s. auto.
Defined.

Definition list_rect_eta_7 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P s ->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
path_ind_eta
  A
  P
  s
  (path_ind_retract
    A
    P
    s
    (@list_rect
      A
      (path_rect_ltv A P)
      pnil
      (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
        pcons h (list_to_t A l) H) 
      (list_to_t_inv A s))).

Definition list_rect_eta_8 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P (existT (vector A) (projT1 s) (projT2 s)) ->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
path_ind_eta
  A
  P
  s
  (path_ind_retract
    A
    P
    s
    (@list_rect
      A
      (path_rect_ltv A P)
      pnil
      (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
        pcons h (list_to_t A l) H) 
      (list_to_t_inv A s))).

(* ^ This general form is what works. What we get is because of some equality: *)

Lemma sigT_vect_rect_correct:
  forall A P pnil pcons s,
    sigT_vect_rect A P pnil pcons s =
    list_rect_eta_8 A P pnil pcons s.
Proof.
  (* ??? *)
Abort.

(* ^ May not need propositional equality here; try in HoTT *)

(* --- Unpacked equiv --- *)

Definition pltv (T : Type) (n : nat) (pl : { l : list T & list_to_t_index T l = n }) : vector T n :=
  @eq_rect 
    nat
    (list_to_t_index T (projT1 pl))
    (vector T)
    (list_rect
      (fun l0 : list T => vector T (list_to_t_index T l0))
      (nilV T)
      (fun (a : T) (l0 : list T) (IHl : vector T (list_to_t_index T l0)) => 
         consV T a (list_to_t_index T l0) IHl)
      (projT1 pl))
    n
    (projT2 pl).  

Definition vtl (T : Type) (n : nat) (v : vector T n) :=
  VectorDef.t_rect 
    T
    (fun (n0 : nat) (_ : vector T n0) => {l : list T & list_to_t_index T l = n0})
    (existT (fun l : list T => list_to_t_index T l = 0) nil eq_refl)
    (fun (h : T) (n0 : nat) (_ : vector T n0) (IHv : {l : list T & list_to_t_index T l = n0}) =>
      existT 
        (fun l : list T => list_to_t_index T l = S n0) 
        (h :: projT1 IHv)
        (eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl (projT2 IHv)))
    n
    v.

(*
 * Will want to simplify these, but here's the gist
 * (some help from Jason Gross: https://github.com/uwplse/ornamental-search/issues/39)
 *)
Lemma pltv_section:
  forall T n pl, vtl T n (pltv T n pl) = pl.
Proof.
  intros T. assert (forall (l : list T), vtl T (list_to_t_index T l) (pltv T (list_to_t_index T l) (existT _ l eq_refl)) = existT _ l eq_refl).
  - induction l; intros.
    + reflexivity.
    + unfold pltv in IHl. unfold pltv. simpl in *. rewrite IHl. reflexivity.
  - intros n pl. induction pl. specialize (H x). 
    unfold pltv. simpl. rewrite <- p. apply H.
Defined.

(* ^ Term is so ugly, which may get in the way of generating; think about what lemmas we need *)

Lemma pltv_retraction:
  forall T n v, pltv T n (vtl T n v) = v.
Proof.
  induction v.
  - reflexivity.
  - unfold pltv. simpl. generalize dependent (vtl T n v). intros s H.
    induction s. simpl. subst. simpl. reflexivity.
Defined.

Program Definition plist_rect : (* Give the list proof motive a dummy eq proof at eq_refl *)
  forall (A : Type) (P : forall n : nat, { l : list A & list_to_t_index A l = n } -> Type),
    P 0 (existT _ (@nil A) eq_refl) ->
    (forall (h : A) (n : nat) (t : { l : list A & list_to_t_index A l = n }), P n t -> P (S n) (existT _ (@cons A h (projT1 t)) (f_equal S (projT2 t)))) ->
    forall (n : nat) (t : { l : list A & list_to_t_index A l = n }), P n t.
Proof.
  intros. assert (forall (l : list A), P (list_to_t_index A l) (existT _ l eq_refl)).
  - induction l. (* Proof about lists and their lengths *)
    + apply X.
    + apply (X0 a (list_to_t_index A l) (existT _ l eq_refl) IHl).
  - induction t. rewrite <- p. apply X1. (* Rewrite to be the nice length *)
Defined.

Program Definition plist_easy_rect :
  forall (A : Type) (P : list A -> Type) (n : nat) (Q : forall (n : nat) (l : list A), P l -> Type),
    forall (list_proof : forall (l : list A), P l), (* list proof *)
    forall (length_proof : forall (l : list A), list_to_t_index A l = n -> Q n l (list_proof l)), (* length proof *)
    forall (pl : { l : list A & list_to_t_index A l = n }),
      Q n (projT1 pl) (list_proof (projT1 pl)). (* packed proof *)
Proof.
  intros A P n Q list_proof length_proof pl.
  apply (length_proof (projT1 pl) (projT2 pl)).
Defined.

(*
 * From Example.v:
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

Preprocess Module hs_to_coq' as hs_to_coq.

Lemma zip_index':
  forall {a} {b} (l1 : list a) (l2 : list b),
    list_to_t_index _ l1 = list_to_t_index _ l2 ->
    list_to_t_index _ (hs_to_coq.zip a b l1 l2) = list_to_t_index _ l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Preprocess zip_index' as zip_index.

Program Definition zip_pl:
  forall {a} {b} {n : nat},
    { l1 : list a & list_to_t_index a l1 = n } ->
    { l2 : list b & list_to_t_index b l2 = n } ->
    { l3 : list (a * b) & list_to_t_index (a * b) l3 = n }.
Proof.
  intros a b n pl1 pl2. pose proof plist_easy_rect as H.
  specialize (H a (fun l1 => list (a * b)) n).
  specialize (H (fun (n : nat) (l : list a) (zipped : list (a * b)) => {l3 : list (a * b) & list_to_t_index (a * b) l3 = n})).
  apply (H (fun l1 => hs_to_coq.zip a b l1 (projT1 pl2))).
  - intros l1 zipped_invariant. 
    exists (hs_to_coq.zip a b l1 (projT1 pl2)). (* list function *)
    rewrite <- zipped_invariant.
    apply (zip_index a b l1 (projT1 pl2)). (* length invariant *)
    rewrite (projT2 pl2).
    apply zipped_invariant.
  - apply pl1.
Defined.

Lemma zip_with_index':
  forall {A} {B} {C} f (l1 : list A) (l2 : list B),
    list_to_t_index _ l1 = list_to_t_index _ l2 ->
    list_to_t_index _ (hs_to_coq.zip_with A B C f l1 l2) = list_to_t_index _ l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Preprocess zip_with_index' as zip_with_index.

Program Definition zip_with_pl:
  forall {A} {B} {C} (f : A -> B -> C) {n : nat},
    { l1 : list A & list_to_t_index A l1 = n } ->
    { l2 : list B & list_to_t_index B l2 = n } ->
    { l3 : list C & list_to_t_index C l3 = n }.
Proof.
  intros A B C f n pl1 pl2. pose proof plist_easy_rect as H.
  specialize (H A (fun l1 => list C) n).
  specialize (H (fun (n : nat) (l : list A) (zipped : list C) => {l3 : list C & list_to_t_index C l3 = n})).
  apply (H (fun l1 => hs_to_coq.zip_with A B C f l1 (projT1 pl2))).
  - intros l1 zipped_invariant.
    exists (hs_to_coq.zip_with A B C f l1 (projT1 pl2)). (* list function *)
    rewrite <- zipped_invariant.
    apply (zip_with_index A B C f l1 (projT1 pl2)). (* length invariant *)
    rewrite (projT2 pl2).
    apply zipped_invariant.
  - apply pl1.
Defined.

From Coq Require Import Eqdep_dec Arith.

(*
 * Aside: Before we do zip_with_is_zip_pl, I want to show you a proof of UIP over 
 * the index that doesn't rely on UIP holding on the type of the indexer itself.
 * I will generalize this soon and use it elsewhere, but this should be derivable
 * for any algebraic ornament. We will need this for zip_with_is_zip_pl (well,
 * we'll need UIP on the indexer, for which UIP on the type is sufficient, but 
 * better to have something that works for any algebraic ornament).
 *)

(*
 * If we can show this in general, it will help us. But I don't know how to do that:
 *)
Lemma coh_refl:
  forall A (l : list A),
    list_to_t_coh A l = eq_refl.
Proof.
  reflexivity.
Defined.

Lemma lift_pres_refl:
  forall A (l : list A) (H : list_to_t_index A l = list_to_t_index A l),
    H = @eq_refl _ (list_to_t_index A l) ->
    rew <- (list_to_t_coh A l) in H = @eq_refl _ (projT1 (list_to_t A l)).
Proof.
  intros A l H Heq. subst. reflexivity.
Defined.

Lemma lift_pres_refl_inv:
  forall A (l : list A) (H : list_to_t_index A l = list_to_t_index A l),
    rew <- (list_to_t_coh A l) in H = @eq_refl _ (projT1 (list_to_t A l)) ->
    H = @eq_refl _ (list_to_t_index A l).
Proof.
  intros A l H Heq. unfold list_to_t_coh in Heq. simpl in Heq.
  rewrite <- Heq. reflexivity.
Defined.

Lemma list_pres_eq:
  forall A (l1 l2 : list A),
    l1 = l2 ->
    list_to_t A l1 = list_to_t A l2.
Proof.
  intros A l1 l2 H. subst. reflexivity.
Defined.

Lemma list_pres_eq_ind:
  forall A x1 x2, list_to_t_index A x1 = list_to_t_index A x2 -> projT1 (list_to_t A x1) = projT1 (list_to_t A x2).
Proof.
  intros. rewrite list_to_t_coh. rewrite H. reflexivity.
Defined.

Lemma section_coh:
  forall (A : Type) (n : nat) (l : list A) (H : list_to_t_index A l = n),
    rew <- [fun l : list A => list_to_t_index A l = n]
       list_to_t_section A l in H = 
    rew [fun (l : list A) => list_to_t_index A l = n]
      (eq_sym (list_to_t_section A l)) in
      (eq_sym (rew [fun (n : nat) => n = list_to_t_index A l] H in
      (list_to_t_coh A l))).
Proof.
  intros. destruct H. simpl. reflexivity.
Defined.

Lemma list_pres_eq_unpacked:
  forall A (n : nat) (pl1 pl2: { l : list A & list_to_t_index A l = n}),
    projT1 pl1 = projT1 pl2 ->
    pl1 = pl2.
Proof.
  intros. 
  remember (projT1 pl1) as l1. remember (projT1 pl2) as l2.
  remember (projT2 pl1) as pf1. remember (projT2 pl2) as pf2.
  remember (list_to_t A l1) as pv1. remember (list_to_t A l2) as pv2.
  remember (list_pres_eq A l1 l2 H).
  remember (list_to_t_section A l1).
  remember (list_to_t_section A l2).
  remember (list_to_t_coh A l1).
  remember (list_to_t_coh A l2).
  remember (list_to_t_coh A (list_to_t_inv A (list_to_t A l1))).
  remember (list_to_t_coh A (list_to_t_inv A (list_to_t A l2))).
  remember (existT _ (list_to_t_inv A (list_to_t A (projT1 pl1))) (rew <- (list_to_t_section A (projT1 pl1)) in pf1)).
  remember (existT _ (list_to_t_inv A (list_to_t A (projT1 pl2))) (rew <- (list_to_t_section A (projT1 pl2)) in pf2)).
  destruct pl1, pl2.
  assert (existT (fun l : list A => list_to_t_index A l = n) x e6 = s).
  - rewrite Heqs. subst. simpl in *. subst.  
    simpl. rewrite section_coh. simpl.
    eapply EqdepFacts.eq_sigT_sig_eq.
    exists (eq_sym (list_to_t_section A x0)). reflexivity.
  - assert (existT (fun l : list A => list_to_t_index A l = n) x0 e7 = s0).
    + rewrite Heqs0. destruct e7. subst. simpl in *. subst. 
      simpl. rewrite section_coh. simpl.
      eapply EqdepFacts.eq_sigT_sig_eq.
      exists (eq_sym (list_to_t_section A x0)). reflexivity.
    + destruct Heqpf1. destruct Heqpf2.
      destruct Heql1. destruct Heql2.
      assert (s = s0).
      * rewrite Heqs0. rewrite Heqs.  apply EqdepFacts.eq_sigT_sig_eq.
        exists (eq_trans (eq_trans e0 H) (eq_sym e1)).
        unfold eq_rect_r.
        Search eq_trans.
        rewrite Heqe0. rewrite Heqe1.
        rewrite eq_trans_rew_distr.
        rewrite eq_trans_rew_distr. f_equal.
        destruct pf2. simpl. subst. simpl in *.
        pose proof (@Adjoint.commute_homotopy_id (list A) (fun l => list_to_t_inv A (list_to_t A l)) (list_to_t_section A) l2 l2).
        rewrite <- eq_trans_rew_distr. pose proof (H eq_refl).

apply EqdepFacts.eq_sigT_sig_eq.
      
      
     


Lemma list_uip_index:
  forall (T : Type) (n : nat) (p1 p2 : {l : list T & list_to_t_index T l = n}),
  
    projT1 p1 = projT1 p2 ->
    p1 = p2.
Proof.
  intros T n p1 p2 H. apply UIP_dec. 
Defined.

Lemma list_uip_index_refl:
  forall (T : Type) (l : list T) (s: sigT (fun (n : nat) => list_to_t_index T l = n))
    (coh : projT1 s = list_to_t_index T l), 
    rew coh in projT2 s = eq_refl.
Proof.
  intros T l s coh. pose proof (list_uip_index T l s (existT _ (list_to_t_index T l) eq_refl)).
  pose proof (projT2_eq (@eq_refl _ s)).
  destruct s1. destruct s2. simpl in *. subst.
  specialize (H0 (existT _ (list_to_t_index T l) eq_refl) (existT _ (list_to_t_index T l) H)).
  
  pose proof (H0 eq_refl).
  apply UIP_dec.
  intros. destruct x. destruct y. subst.
  left. reflexivity.
Defined.

(*
 * Still figuring out how to get there, but some relevant facts. Let's start
 * with lists, but not rely on any properties of the natural numbers or of the
 * particular coherence proof we have.
 *)
Lemma indexer_proj_rew: 
  forall (T : Type) (l : list T) (pv : sigT (vector T)), list_to_t T l = pv -> pv = existT _ (list_to_t_index T l) (projT2 (list_to_t T l)).
Proof.
  intros T l pv H.
  assert (pv = existT _ (projT1 (list_to_t T l)) (projT2 (list_to_t T l))).
  - rewrite H. rewrite <- sigT_eta. reflexivity.
  - assert (pv = existT _ (projT1 (list_to_t T (list_to_t_inv T pv))) (projT2 (list_to_t T (list_to_t_inv T pv)))).
    + eapply eq_trans.
      * apply H0.
      * rewrite <- sigT_eta. rewrite <- sigT_eta. rewrite <- H. rewrite list_to_t_section. reflexivity.
    + rewrite H1 in H0. pose proof (projT2_eq H0). unfold projT1_eq in H2.
        replace (projT2
       (existT [eta vector T] (projT1 (list_to_t T (list_to_t_inv T pv)))
          (projT2 (list_to_t T (list_to_t_inv T pv))))) with (projT2 (list_to_t T (list_to_t_inv T pv)))
        in H2 by reflexivity.
       replace (projT2
       (existT [eta vector T] (projT1 (list_to_t T l)) (projT2 (list_to_t T l))))
        with (projT2 (list_to_t T l)) in H2 by reflexivity.
       rewrite H1. eapply eq_sigT.
       replace (projT2
  (existT [eta vector T] (projT1 (list_to_t T (list_to_t_inv T pv)))
     (projT2 (list_to_t T (list_to_t_inv T pv)))))
       with (projT2 (list_to_t T (list_to_t_inv T pv))) by reflexivity.
     replace (projT2 (existT [eta vector T] (list_to_t_index T l) (projT2 (list_to_t T l))))
       with (projT2 (list_to_t T l)) by reflexivity.
     apply H2.
Defined.
(*
 * ^ I don't know what to show after this. This fact gets us not only that
 * the first projection is always the indexer like coherence, but also that
 * we can rewrite by the first equality. Which tells us something I think, but
 * not sure what.
 *)

Lemma zip_with_is_zip_pl :
  forall {A} {B} {n} (pl1 : { l1 : list A & list_to_t_index A l1 = n }) (pl2 : { l2 : list B & list_to_t_index B l2 = n }),
    zip_with_pl pair pl1 pl2 = zip_pl pl1 pl2.
Proof.
  intros A B n pl1 pl2. pose proof plist_easy_rect as H.
  specialize (H A (fun l1 => hs_to_coq.zip_with A B (A * B) pair l1 (projT1 pl2) = hs_to_coq.zip A B l1 (projT1 pl2)) n).
  specialize (H (fun n l1 H => zip_with_pl pair pl1 pl2 = zip_pl pl1 pl2)).
  apply (H (fun l1 => hs_to_coq.zip_with_is_zip A B l1 (projT1 pl2))).
  - intros l1 zip_with_is_zip_invariant. (* v list proof invariant *)
    unfold zip_with_pl, zip_pl, plist_easy_rect.
    induction pl1. induction pl2. simpl in *.
    apply EqdepFacts.eq_sigT_sig_eq.
    exists (hs_to_coq.zip_with_is_zip A B x x0). (* list proof *)
    auto using (UIP_dec Nat.eq_dec). (* <- same thing shows up here, need to prove about fold *)
  - apply pl1.
Defined.

(*
 * Not bad, but could be simpler.
 *)

(* ^ TODO so we can implement that transport, but then the question becomes how to interface
   this and separate proofs over lists and proofs about their lengths, and automatically
   combine them into this form *)

(* --- What about splitting constructors? --- *)

Inductive list2 (T : Type) :=
| nil2 : list2 T
| cons2 : T -> list2 T -> list2 T
| never : False -> list2 T.

Program Definition list_to_list2 : forall (T : Type) (l : list T), list2 T.
Proof.
  intros. induction l.
  - apply nil2.
  - apply cons2.
    + apply a.
    + apply IHl.
Defined.

Program Definition list2_to_list : forall (T : Type) (l : list2 T), list T.
Proof.
  intros. induction l.
  - apply nil.
  - apply cons.
    + apply t.
    + apply IHl.
  - inversion f.
Defined.

Theorem list_to_list2_section:
  forall (T : Type) (l : list T), list2_to_list T (list_to_list2 T l) = l.
Proof.
  intros. induction l.
  - auto.
  - simpl. rewrite IHl. auto.
Defined.

Theorem list_to_list2_retraction:
  forall (T : Type) (l : list2 T), list_to_list2 T (list2_to_list T l) = l.
Proof.
  intros. induction l.
  - auto.
  - simpl. rewrite IHl. auto.
  - inversion f.
Defined.

Lemma list2_list_rect :
  forall (A : Type) (P : list2 A -> Type),
    P (nil2 A) ->
    (forall (a : A) (l : list2 A) (IH : P l),
      P (cons2 A a l)) ->
    forall (l : list2 A), P l.
Proof.
  intros A P pnil2 pcons2 l. induction l.
  - apply pnil2.
  - apply pcons2. apply IHl.
  - inversion f.
Defined.

Definition transport_nil:
  forall (A : Type) (P : list2 A -> Type),
    P (list_to_list2 A nil) ->
    P (nil2 A).
Proof.
  intros. apply X.
Defined.

Definition transport_nil_inv:
  forall (A : Type) (P : list2 A -> Type),
    P (nil2 A) ->
    P (list_to_list2 A nil).
Proof.
  intros. apply X.
Defined.

Definition transport_cons:
  forall (A : Type) (P : list2 A -> Type) (l : list2 A) (a : A),
    P (list_to_list2 A (cons a (list2_to_list A l))) ->
    P (cons2 A a l).
Proof.
  intros. simpl in X. rewrite list_to_list2_retraction in X. apply X.
Defined.

Definition transport_cons_inv:
  forall (A : Type) (P : list2 A -> Type) (l : list2 A) (a : A),
    P (cons2 A a l) ->
    P (list_to_list2 A (cons a (list2_to_list A l))).
Proof.
  intros. simpl. rewrite list_to_list2_retraction. apply X.
Defined.

(*
 * Definitely follows patterns from the equivalences, but still not sure
 * exactly what is happening here.
 *)

(* --- Let's see --- *)

Inductive Foo : nat -> Type :=
| f : forall (n : nat), Foo n.

Inductive Bar : nat -> Type :=
| f1 : Bar 0
| f2 : forall (n : nat), Bar n -> Bar (S n).

Program Definition Foo_to_Bar : forall (n : nat), Foo n -> Bar n.
Proof.
  intros. induction H.
  - induction n.
    + apply f1.
    + apply f2. apply IHn.
Defined.

Program Definition Bar_to_Foo : forall (n : nat), Bar n -> Foo n.
Proof.
  intros. apply f.
Defined.

Theorem Foo_to_Bar_section:
  forall (n : nat) (f : Foo n), Bar_to_Foo n (Foo_to_Bar n f) = f.
Proof.
  intros. induction f0.
  - induction n.
    + auto.
    + auto.
Defined.

Theorem Foo_to_Bar_retraction:
  forall (n : nat) (b : Bar n), Foo_to_Bar n (Bar_to_Foo n b) = b.
Proof.
  intros. induction b.
  - auto.
  - simpl. simpl in IHb. rewrite IHb. auto.
Defined.

Check Foo_rect.

Lemma Bar_nat_rect:
  forall (n : nat) (b : Bar n),
    nat_rect Bar f1 (fun (n : nat) (IHn : Bar n) => f2 n IHn) n = b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. rewrite IHb. reflexivity.
Defined.

Lemma Bar_Foo_rect:
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (nat_rect Bar f1 (fun _ IHn => f2 _ IHn) n)) -> (* <-- looks like repacking *)
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b. rewrite <- Bar_nat_rect. apply pf0. 
Defined.

(* So repacking really is dependent elimination! *)

Lemma Foo_Bar_rect:
  forall P : forall n : nat, Foo n -> Type,
    P 0 (f 0) ->
    (forall (n : nat) (f0 : Foo n), P n (f n) -> P (S n) (f (S n))) ->
    forall (n : nat) (b : Foo n), P n (f n).
Proof.
  intros P pf1 pf2 n f. induction f.
  - induction n.
    + apply pf1.
    + apply (pf2 n (f n)). apply IHn.
Defined.

(* Also note how each of these corresponds to Foo_to_Bar and Bar_to_Foo, respectively. *)



