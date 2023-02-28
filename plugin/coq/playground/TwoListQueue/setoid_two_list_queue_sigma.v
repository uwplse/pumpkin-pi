Require Import List Bool.
Import ListNotations.
Import Equivalence.
Require Import Morphisms.
Require Import Specif.
Require Import StructTact.StructTactics.
Module TwoListQueue.

Definition raw_queue (A : Type) := (list A * list A) % type.

Definition app_rev {A : Type} (q : raw_queue A) : list A :=
  match q with
  | (f, b) => f ++ (rev b)
  end.

Definition raw_equiv {A : Type} (q1 q2 : raw_queue A) : Prop :=
  app_rev q1 = app_rev q2.

(* https://www.cis.upenn.edu/~plclub/blog/2020-05-15-Rewriting-in-Coq/
https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
 *)
#[export] Instance raw_equiv_refl {A : Type} : Reflexive (@raw_equiv A).
Proof.
  unfold Reflexive.
  reflexivity.
Qed.

#[export] Instance raw_equiv_sym {A : Type} : Symmetric (@raw_equiv A).
Proof.
  unfold Symmetric.
  intros.
  symmetry.
  apply H.
Qed.

#[export] Instance raw_equiv_trans {A : Type} : Transitive (@raw_equiv A).
Proof.
  unfold Transitive.
  intros.
  unfold raw_equiv.
  rewrite H.
  apply H0.
Qed.

#[export] Instance raw_equiv_equiv {A : Type} : Equivalence (@raw_equiv A).
Proof.
  split;
  [apply raw_equiv_refl
  |apply raw_equiv_sym
  |apply raw_equiv_trans].
Qed.

  
Definition rep_ok {A : Type} (q : raw_queue A) : Prop :=
  match q with
  | (f, b) => f = [] -> b = []
  end.

Definition raw_empty {A : Type} : raw_queue A := ([],[]).
Definition raw_is_empty {A : Type} (q : raw_queue A) : bool :=
  match q with
  | ([], b) => true
  | (_::_, b) => false
  end.

Definition raw_enq {A : Type} (a : A) (q : raw_queue A) : raw_queue A :=
  match q with
  | ([], b) => ([a], b)
  | (h::t, b) => (h::t, a::b)
  end.

Definition raw_deq {A : Type} (q : raw_queue A) : raw_queue A :=
  match q with
  | ([], b) => ([], b)
  | (h::[], b) => (List.rev b, [])
  | (h::t, b) => (t, b)
  end.

Definition raw_peek {A : Type} (q : raw_queue A) : option A :=
  match q with
  | ([], b) => None
  | (h::t, b) => Some h
  end.

Theorem rep_ok_empty : forall (A : Type),
    rep_ok (@raw_empty A).
Proof.
  intros.
  simpl.
  trivial.
Qed.

Theorem rep_ok_enq : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> rep_ok (raw_enq a q).
Proof.
  intros.
  unfold rep_ok.
  destruct q.
  simpl.
  destruct l.
  - intros.
    unfold rep_ok in H.
    apply H.
    reflexivity.
  - intros.
    discriminate.
Qed.


Theorem rep_ok_deq : forall (A : Type) (q : raw_queue A),
    rep_ok q -> rep_ok (raw_deq q).
Proof.
  intros.
  destruct q.
  destruct l.
  - apply H.
  - simpl.
    destruct l.
    + simpl.
      intros.
      reflexivity.
    + simpl.
      intros.
      discriminate.
Qed.

Theorem raw_empty_is_empty : forall (A : Type),
    raw_is_empty (@raw_empty A) = true.
Proof.
  reflexivity.
Qed.

Theorem raw_enq_not_empty : forall (A : Type) (a : A) (q : raw_queue A),
    raw_is_empty (raw_enq a q) = false.
Proof.
  intros. destruct q. destruct l; reflexivity.
Qed.

Theorem raw_no_peek_empty : forall (A : Type),
  raw_peek (@raw_empty A) = None.
Proof.
  reflexivity.
Qed.

(*
Lemma is_empty_implies_empty : forall (A : Type) (q : queue A),
    rep_ok q -> is_empty q = true -> q = empty.
Proof.
  intros.
  destruct q.
  destruct l.
  - simpl in H.
    assert (l0 = []).
    auto.
    rewrite -> H1.
    reflexivity.
  - simpl in H0.
    discriminate.
Qed.
*)

Theorem raw_peek_singleton : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = true -> raw_peek (raw_enq a q) = Some a.
Proof.
  intros.
  destruct q.
  simpl.
  destruct l.
  - reflexivity.
  - discriminate.
Qed.

Theorem raw_peek_enq_nonempty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = false -> raw_peek (raw_enq a q) = raw_peek q.
Proof.
  intros.
  destruct q.
  simpl.
  destruct l.
  - discriminate.
  - reflexivity.
Qed.

(*
Theorem deq_singleton : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> is_empty q = true -> deq (enq a q) = q.
Proof.
  intros.
  apply is_empty_implies_empty in H0.
  rewrite H0.
  reflexivity.
  apply H.
Qed.
 *)

Theorem raw_deq_singleton : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = true -> raw_equiv (raw_deq (raw_enq a q)) q.
Proof.
  intros.
  unfold raw_equiv.
  destruct q.
  destruct l.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - discriminate.
Qed.
    
Theorem raw_deq_enq_nonempty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = false -> raw_equiv (raw_deq (raw_enq a q)) (raw_enq a (raw_deq q)).
Proof.
  intros.
  unfold raw_equiv.
  destruct q.
  unfold app_rev.
  destruct l; try discriminate.
  simpl.
  destruct l; try reflexivity.
  simpl.
  destruct l0; try reflexivity.
  simpl.
  destruct (rev l0 ++ [a1]); try reflexivity.
  rewrite app_nil_r.
  reflexivity.
Qed.

(** Queue with representation invariant enforced. **)

Definition queue (A : Type) := sig (@rep_ok A) % type.

Definition equiv {A : Type} (q1 q2 : queue A) :=
  raw_equiv (proj1_sig q1) (proj1_sig q2).

#[export] Instance equiv_refl {A : Type} : Reflexive (@equiv A).
Proof.
  intros x.
  apply raw_equiv_refl.
Qed.

#[export] Instance equiv_sym {A : Type} : Symmetric (@equiv A).
Proof.
  unfold Symmetric.
  intros x y.
  apply raw_equiv_sym.
Qed.

#[export] Instance equiv_trans {A : Type} : Transitive (@equiv A).
Proof.
  unfold Transitive.
  unfold equiv.
  intros x y z.
  apply raw_equiv_trans.
Qed.

#[export] Instance equiv_equiv {A : Type} : Equivalence (@equiv A).
Proof.
  split;
  [apply equiv_refl
  |apply equiv_sym
  |apply equiv_trans].
Qed.

Definition empty {A : Type} : queue A :=
  (exist rep_ok (@raw_empty A) (@rep_ok_empty A)). 

Definition is_empty {A : Type} (q : queue A) :=
  raw_is_empty (proj1_sig q).

Definition enq {A : Type} (a : A) (q : queue A) :=
  match q with
  | exist _ x p => exist rep_ok (raw_enq a x) (rep_ok_enq A a x p)
  end.

Definition deq {A : Type} (q : queue A) :=
  match q with
  | exist _ x p => exist rep_ok (raw_deq x) (rep_ok_deq A x p)
  end.

Definition peek {A : Type} (q : queue A) :=
  raw_peek (proj1_sig q).

Theorem empty_is_empty : forall (A : Type),
    is_empty (@empty A) = true.
Proof.
  apply raw_empty_is_empty.
Qed.

Theorem enq_not_empty : forall (A : Type) (a : A) (q : queue A),
    is_empty (enq a q) = false.
Proof.
  intros.
  destruct q.
  unfold is_empty.
  simpl.
  apply raw_enq_not_empty.
Qed.

Theorem no_peek_empty : forall (A : Type),
    peek (@empty A) = None.
Proof.
  apply raw_no_peek_empty.
Qed.

Theorem peek_singleton : forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> peek (enq a q) = Some a.
Proof.
  intros.
  destruct q.
  simpl.
  unfold peek.
  apply raw_peek_singleton; assumption.
Qed.

Theorem peek_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    is_empty q = false -> peek (enq a q) = peek q.
Proof.
  intros.
  destruct q.
  simpl.
  unfold peek.
  apply raw_peek_enq_nonempty; assumption.
Qed.

Theorem deq_singleton : forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> equiv (deq (enq a q)) q.
Proof.
  intros.
  destruct q.
  simpl.
  apply raw_deq_singleton; assumption.
Qed.

Theorem deq_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    is_empty q = false -> equiv (deq (enq a q)) (enq a (deq q)).
Proof.
  intros.
  destruct q.
  simpl.
  apply raw_deq_enq_nonempty; assumption.
Qed.

Theorem rep_ok_contradiction : forall (A : Type) (a : A) (l : list A),
    rep_ok ([], a :: l) -> False.
Proof.
  intros.
  simpl in H.
  assert (@nil A = []).
  reflexivity.
  apply H in H0.
  discriminate.
Qed.

Lemma rev_reduce : forall (A : Type) (y : A) (lst : list A),
  lst <> nil -> rev lst = (last lst y) :: (rev (removelast lst)).
Proof.
  intros. induction lst as [ | h t IH].
   - contradiction.
   - simpl. destruct t.
     * auto.
     * rewrite IH. auto. discriminate.
Qed.

Ltac bad_rep_ok H := apply rep_ok_contradiction in H; contradiction.

#[export] Instance enq_Proper {A : Type} (a : A) : Proper (equiv ==> equiv) (enq a).
Proof.
  intros q q' H.
  unfold equiv.
  destruct q, q'.
  simpl.
  destruct x, x0.
  simpl.
  unfold equiv in H.
  unfold raw_equiv in H.
  simpl in H.
  destruct l, l1; unfold raw_equiv; simpl in H; simpl.
  - f_equal.
    auto.
  - apply (f_equal (@rev A)) in H.
    rewrite rev_involutive in H.
    rewrite H in r.
    rewrite rev_reduce with (y := a) in r.
    bad_rep_ok r.
    discriminate.
  - apply (f_equal (@rev A)) in H.
    rewrite rev_involutive in H.
    rewrite <- H in r0.
    rewrite rev_reduce with (y := a) in r0.
    bad_rep_ok r0.
    discriminate.
  - repeat (rewrite app_assoc).
    rewrite app_comm_cons.
    rewrite H.
    reflexivity.
Qed.    

(**  
  destruct l, l0.
  - destruct l1.
    + destruct l2.
      * reflexivity.
      * apply rep_ok_contradiction in r0.
        contradiction.
    + discriminate.
  - destruct l1.
    + destruct l2.
      * apply rep_ok_contradiction in r.
        contradiction.
      * simpl in H.
        unfold raw_equiv.
        simpl.
        rewrite H.
        reflexivity.
    + apply rep_ok_contradiction in r.
      contradiction.
  - destruct l1.
    + destruct l2.
      * discriminate.
      * apply rep_ok_contradiction in r0.
        contradiction.
    + simpl in H.
      rewrite app_nil_r in H.
      rewrite H.
      unfold raw_equiv.
      simpl.
      rewrite app_assoc.
      reflexivity.
  - destruct l1.
    + destruct l2.
      * discriminate.
      * apply rep_ok_contradiction in r0.
        contradiction.
    + simpl in H.
      unfold raw_equiv.
      simpl.
      rewrite app_assoc.
      rewrite app_comm_cons.
      rewrite H.
      rewrite <- app_comm_cons.
      rewrite <- app_assoc.
      reflexivity.
Qed.
 **)

Theorem rep_ok_first_empty : forall (A : Type) (l : list A), rep_ok ([],l) -> l = [].
Proof.
  intros.
  destruct l; auto.
Qed.  

#[export] Instance deq_Proper {A : Type} : Proper ((@equiv A) ==> (@equiv A)) deq.
Proof.
  unfold equiv.
  intros q q' H.
  destruct q, q'.
  simpl.
  destruct x, x0.
  simpl.
  simpl in H.
  unfold raw_equiv.
  destruct l;
    try apply rep_ok_first_empty in r;
    subst.
  - unfold raw_equiv in H.
    simpl in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H.
    rewrite H.
    apply (f_equal (@rev A)) in H0.
    rewrite rev_involutive in H0.
    simpl in H0.
    rewrite H0.
    reflexivity.
  - destruct l1.
    + apply rep_ok_first_empty in r0.
      subst.
      unfold raw_equiv in H.
      simpl in H.
      discriminate.
    + destruct l, l1;
        try (unfold raw_equiv in H);
        simpl in H;
        simpl;
        inversion H;
        try rewrite app_nil_r;
        reflexivity.
Qed.

#[export] Instance peek_Proper {A : Type} : Proper ((@equiv A) ==> (@eq (option A))) peek.
Proof.
  intros q q' H.
  unfold equiv in H.
  destruct q, q'.
  unfold raw_equiv in H.
  simpl in H.
  destruct x, x0.
  unfold peek.
  simpl.
  destruct l, l1.
  - reflexivity.
  - apply rep_ok_first_empty in r.
    subst.
    discriminate.
  - apply rep_ok_first_empty in r0.
    subst.
    discriminate.
  - simpl in H.
    inversion H.
    reflexivity.
Qed.

#[export] Instance is_empty_Proper {A : Type} : Proper ((@equiv A) ==> (@eq bool)) is_empty.
Proof.
  intros q q' H.
  unfold equiv in H.
  destruct q, q'.
  destruct x, x0.
  unfold is_empty.
  simpl.
  unfold raw_equiv in H.
  destruct l, l1; try reflexivity; simpl in H.
  - apply rep_ok_first_empty in r.
    subst.
    discriminate.
  - apply rep_ok_first_empty in r0.
    subst.
    discriminate.
Qed.  
  
End TwoListQueue.
