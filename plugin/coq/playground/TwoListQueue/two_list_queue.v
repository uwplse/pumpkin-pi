Require Import List Bool.
Import ListNotations.
Module TwoListQueue.

Definition queue (A : Type) := (list A * list A) % type.
Definition rep_ok {A : Type} (q : queue A) : Prop :=
  match q with
  | (f, b) => f = [] -> b = []
  end.

Definition empty {A : Type} : queue A := ([],[]).
Definition is_empty {A : Type} (q : queue A) : bool :=
  match q with
  | ([], b) => true
  | (_::_, b) => false
  end.

Definition enq {A : Type} (a : A) (q : queue A) : queue A :=
  match q with
  | ([], b) => ([a], b)
  | (h::t, b) => (h::t, a::b)
  end.

Definition deq {A : Type} (q : queue A) : queue A :=
  match q with
  | ([], b) => ([], b)
  | (h::[], b) => (List.rev b, [])
  | (h::t, b) => (t, b)
  end.

Definition peek {A : Type} (q : queue A) : option A :=
  match q with
  | ([], b) => None
  | (h::t, b) => Some h
  end.

Definition app_rev {A : Type} (q : queue A) : list A :=
  match q with
  | (f, b) => f ++ (rev b)
  end.

Definition equiv {A : Type} (q1 q2 : queue A) : Prop :=
  app_rev q1 = app_rev q2.

Theorem rep_ok_empty : forall (A : Type),
    rep_ok (@empty A).
Proof.
  intros.
  simpl.
  trivial.
Qed.

Theorem rep_ok_enq : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> rep_ok (enq a q).
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

Theorem rep_ok_deq : forall (A : Type) (q : queue A),
    rep_ok q -> rep_ok (deq q).
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

Theorem empty_is_empty : forall (A : Type),
    is_empty (@empty A) = true.
Proof.
  reflexivity.
Qed.

Theorem enq_not_empty : forall (A : Type) (a : A) (q : queue A),
    is_empty (enq a q) = false.
Proof.
  intros. destruct q. destruct l; reflexivity.
Qed.

Theorem no_peek_empty : forall (A : Type),
  peek (@empty A) = None.
Proof.
  reflexivity.
Qed.

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

Theorem peek_singleton : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> is_empty q = true -> peek (enq a q) = Some a.
Proof.
  intros.
  destruct q.
  simpl.
  destruct l.
  - reflexivity.
  - discriminate.
Qed.

Theorem peek_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> is_empty q = false -> peek (enq a q) = peek q.
Proof.
  intros.
  destruct q.
  simpl.
  destruct l.
  - discriminate.
  - reflexivity.
Qed.

Theorem deq_singleton : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> is_empty q = true -> deq (enq a q) = q.
Proof.
  intros.
  apply is_empty_implies_empty in H0.
  rewrite H0.
  reflexivity.
  apply H.
Qed.

Theorem deq_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> is_empty q = false -> equiv (deq (enq a q)) (enq a (deq q)).
Proof.
  intros.
  unfold equiv.
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
  
End TwoListQueue.
