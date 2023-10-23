Require Import List Relation_Definitions Morphisms Setoid.
Import ListNotations.

Module OneListQueue.

  Parameter A : Type.
  Definition queue := list A.
  Definition depConstrEmpty : queue := [].
  Definition depConstrInsert (a : A) (q : queue) : queue := a :: q.
  Print list_rect.
  Definition depElim (P : queue -> Type) (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    (forall (x : queue), P x) :=
    list_rect P pEmpty pInsert.
  
End OneListQueue.

Module TwoListQueue.
  Parameter A : Type.
  Definition queue := (list A * list A) % type.
  Definition insOrder (q : queue) :=
    match q with
    | (l1, l2) => l1 ++ rev l2
    end.
  Definition eq_queue (q1 q2 : queue) : Prop :=
    insOrder q1 = insOrder q2.
  (*https://coq.inria.fr/refman/addendum/generalized-rewriting.html*)
  Theorem eq_queue_refl : reflexive _ eq_queue.
  Proof.
    intros q. reflexivity.
  Qed.
  Theorem eq_queue_sym : symmetric _ eq_queue.
  Proof.
    intros q1 q2 H. symmetry. apply H.
  Qed.
  Theorem eq_queue_trans : transitive _ eq_queue.
  Proof.
    intros q1 q2 q3. unfold eq_queue. intros H1 H2. rewrite H1. apply H2.
  Qed.
  Add Parametric Relation : queue eq_queue
    reflexivity proved by eq_queue_refl
    symmetry proved by eq_queue_sym
    transitivity proved by eq_queue_trans
    as eq_queue_rel.
  
  Definition depConstrEmpty : queue := ([],[]).

  Definition depConstrInsert (a : A) (q : queue) : queue :=
    match q with
    | (l1, l2) => (a :: l1, l2)
    end.

  Add Parametric Morphism (a : A) : (depConstrInsert a)
      with signature eq_queue ==> eq_queue as insert_mor.
  Proof.
    unfold eq_queue.
    intros q1 q2 H.
    destruct q1.
    destruct q2.
    simpl.
    f_equal.
    apply H.
  Qed.

  Notation "q1 [=] q2" := (eq_queue q1 q2) (at level 50). (* I picked this number arbitrarily does it matter*)

  Theorem shift : forall (a : A) (l1 l2 : list A), ((l1 ++ [a]), l2) [=] (l1, (l2 ++ [a])).
  Proof.
    intros.
    unfold eq_queue.
    simpl.
    rewrite rev_app_distr.
    rewrite app_assoc.
    reflexivity.
  Qed.

  (**below two lemmas adapted from standard library*)
  Lemma rev_list_rect : forall P:list A-> Type,
    P [] ->
    (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
    forall l:list A, P (rev l).
  Proof.
    intros P ? ? l; induction l; auto.
  Defined.

    Theorem rev_involutive : forall (A : Type) (l : list A), rev (rev l) = l.
  Proof.
    exact (fun (A : Type) (l : list A) =>
list_ind (fun l0 : list A => rev (rev l0) = l0)
  eq_refl
  (fun (a : A) (l0 : list A) (IHl : rev (rev l0) = l0)
   =>
   eq_ind_r (fun l1 : list A => l1 = a :: l0)
     (eq_ind_r (fun l1 : list A => a :: l1 = a :: l0)
        eq_refl IHl) (rev_unit (rev l0) a)) l).
  Defined. 

  Theorem rev_rect : forall P:list A -> Type,
    P [] ->
    (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof.
    intros P ? ? l. rewrite <- (rev_involutive A l).
    apply (rev_list_rect P); cbn; auto.
  Defined. 

  Theorem depElim (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P) (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    (forall (x : queue), P x).
  Proof.
    intros.
    destruct x.
    induction l as [ | b l].
    - induction l0 as [ | a l0] using rev_rect.
      + apply pEmpty.
      + apply (pInsert a ([], l0)) in IHl0.
        pose proof (shift a nil l0).
        apply p in H.
        rewrite <- H.
        apply IHl0.
    - apply (pInsert b (l, l0)) in IHl.
      apply IHl.
  Defined.

Print rev_involutive.

Theorem iotaEmptyEq (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    depElim P p pEmpty pInsert depConstrEmpty = pEmpty.
  Proof.
    reflexivity.
  Qed.

Theorem iotaInsertEq (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) (a : A) (q : queue) :
    depElim P p pEmpty pInsert (depConstrInsert a q)
    = pInsert a q (depElim P p pEmpty pInsert q).
  Proof.
    destruct q.
    reflexivity.
  Qed.
    
End TwoListQueue.
