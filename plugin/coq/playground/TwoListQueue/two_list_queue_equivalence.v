Require Import List Relation_Definitions Morphisms Setoid.
Import ListNotations.
Require Import EqdepFacts.

Module OneListQueue.

  (* Parameter A : Type.*)
  Definition A : Type := nat.
  Definition queue := list A.
  Definition depConstrEmpty : queue := [].
  Definition depConstrInsert (a : A) (q : queue) : queue := a :: q.
  Print list_rect.
  Definition depElim (P : queue -> Type) (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    (forall (x : queue), P x) :=
    list_rect P pEmpty pInsert.
  Definition depElimProp (P : queue -> Prop) (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    (forall (x : queue), P x) :=
    list_rect P pEmpty pInsert.
  Definition depRec (C : Type) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C) :
    (forall (x : queue), C) :=
    list_rect (fun _ => C) pEmpty pInsert.

  Definition enqueue (a : A) (q : queue) : queue :=
    depConstrInsert a q.

  Definition dequeueHelp (outer : A) (q : queue) (m : option (queue * A)) : option (queue * A) :=
  @option_rect
    (queue * A)
    (fun _ => option (queue * A))
    (fun (p : (queue * A)) => Some (depConstrInsert outer (fst p) , (snd p)))
    (Some (depConstrEmpty, outer))
    m .

  Definition dequeue : queue -> option (queue * A) :=
    depRec (option (queue * A)) None dequeueHelp .
  Definition returnOrEnq (a : A) (m : option (queue * A)) : (queue * A) :=
    @option_rect
      (queue * A)
      (fun _ => prod queue A)
      (fun (p : (queue * A)) => (enqueue a (fst p), snd p))
      (depConstrEmpty, a)
      m.
End OneListQueue.

Module TwoListQueue.
  (* Parameter A : Type.*)
  Definition A : Type := nat.
  Parameter uip : UIP_ A.
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

  Definition canonicalize (q : queue) := (insOrder q, @nil A) .

  Theorem canonicalizeResp (q : queue) :
    canonicalize q [=] q.
  Proof.
    destruct q.
    unfold eq_queue.
    simpl.
    apply app_nil_r.
  Qed.

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

  Theorem depElim' (P : queue -> Type)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    (forall (x : queue), P (canonicalize x)).
  Proof.
    intros.
    destruct x.
    unfold canonicalize.
    simpl.
    induction (l ++ rev l0).
    - apply pEmpty.
    - apply (pInsert a (l1, []) IHl1).
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

  Theorem depRec (C : Type) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C) :
    (forall (x : queue), C).
  Proof.
    intros.
    destruct x.
    induction l as [ | b l].
    - induction l0 as [ | a l0] using rev_rect.
      + apply pEmpty.
      + apply (pInsert a ([], l0)) in IHl0.
        apply IHl0.
    - apply (pInsert b (l, l0)) in IHl.
      apply IHl.
  Defined.

  Theorem depRecCanonical (C : Type) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C)
    (pInsertRespectful : forall (a : A) (q1 q2 : queue) (c : C),
        q1 [=] q2 -> pInsert a q1 c = pInsert a q2 c) :
    forall (l0 l1 : list A),
      depRec C pEmpty pInsert (l0, l1) = depRec C pEmpty pInsert (l0 ++ rev l1, []).
  Proof.
    induction l0 as [ | a l0].
    - induction l1 as [ | b l1] using rev_rect.
      + reflexivity.
      + assert (([], l1) [=] ([] ++ rev l1, [])).
        unfold eq_queue.
        simpl.
        rewrite app_nil_r.
        reflexivity.
        eapply (pInsertRespectful b) in H.
        assert (pInsert b ([], l1) (depRec C pEmpty pInsert ([], l1)) = depRec C pEmpty pInsert ([], l1 ++ [b])).
        simpl.
        unfold rev_rect.
        unfold eq_rect.
        assert (depRec C pEmpty pInsert ([], l1 ++ [b]) = pInsert b ([], l1) (depRec C pEmpty pInsert ([], l1))).
        simpl.
        unfold rev_rect.
        unfold eq_rect.
        (*rewrite (uip l1 (rev(rev l1))).
        
        simpl.
        unfold rev_rect.
        apply pInsertRespectful.
        simpl.
        apply (f_equal (pInsert b)) in IHl1.
        simpl.
        unfold rev_rect.
        simpl.*)
  Admitted.
  
  Add Parametric Morphism (C : Type) (equiv : C -> C -> Prop) (equiv_equiv : Equivalence equiv) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C)
    (pInsertRespectful : forall (a : A) (q1 q2 : queue) (c : C),
        q1 [=] q2 -> pInsert a q1 c = pInsert a q2 c) :
    (depRec C pEmpty pInsert)
      with signature eq_queue ==> equiv as depRec_mor.
  Proof.
    intros.
    destruct x.
    unfold eq_queue in H.
    destruct y.
    simpl in H.
    rewrite depRecCanonical.
    rewrite H.
    rewrite <- depRecCanonical.
    reflexivity.
    apply pInsertRespectful.
    apply pInsertRespectful.
  Qed.
    
  
  (* Theorem depElimRespectful (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P) (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q))
    (q1 q2 : queue) :
  q1 [=] q2 -> depElim P p pEmpty pInsert q1 = depElim P p pEmpty pInsert q2.*)

Theorem iotaEmptyEq (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    depElim P p pEmpty pInsert depConstrEmpty = pEmpty.
  Proof.
    reflexivity.
  Defined.

Theorem iotaEmpty (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    forall (Q : P depConstrEmpty -> Type),
      (Q (depElim P p pEmpty pInsert depConstrEmpty)) -> (Q pEmpty).
  Proof.
    intros.
    rewrite iotaEmptyEq in X.
    apply X.
  Defined.

Theorem iotaEmptyRev (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
    forall (Q : P depConstrEmpty -> Type),
      (Q pEmpty) -> (Q (depElim P p pEmpty pInsert depConstrEmpty)).
  Proof.
    intros.
    rewrite iotaEmptyEq.
    apply X.
  Defined.

Theorem iotaInsertEq (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) (a : A) (q : queue) :
    depElim P p pEmpty pInsert (depConstrInsert a q)
    = pInsert a q (depElim P p pEmpty pInsert q).
  Proof.
    destruct q.
    reflexivity.
  Defined.

Theorem iotaInsert (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
  forall (a : A) (q : queue) (Q : P (depConstrInsert a q) -> Type), 
    Q (depElim P p pEmpty pInsert (depConstrInsert a q))
    -> Q (pInsert a q (depElim P p pEmpty pInsert q)).
  Proof.
    intros.
    rewrite iotaInsertEq in X.
    apply X.
  Defined.

Theorem iotaInsertRev (P : queue -> Type) `(p : Proper (queue -> Type) (eq_queue ==> eq) P)
    (pEmpty : P depConstrEmpty)
    (pInsert : forall (a : A) (q : queue), P q -> P (depConstrInsert a q)) :
  forall (a : A) (q : queue) (Q : P (depConstrInsert a q) -> Type),
    Q (pInsert a q (depElim P p pEmpty pInsert q))
    -> Q (depElim P p pEmpty pInsert (depConstrInsert a q)).
  Proof.
    intros.
    rewrite iotaInsertEq.
    apply X.
  Qed.

Definition enqueue (a : A) (q : queue) : queue :=
  depConstrInsert a q.

Instance enqueueProper (a : A) : Proper (eq_queue ==> eq_queue) (enqueue a).
Proof.
  intros q1 q2 H.
  unfold enqueue.
  apply insert_mor.
  apply H.
Qed.
  
Definition dequeueHelp (outer : A) (q : queue) (m : option (queue * A)) : option (queue * A) :=
  @option_rect
    (queue * A)
    (fun _ => option (queue * A))
    (fun (p : (queue * A)) => Some (depConstrInsert outer (fst p) , (snd p)))
    (Some (depConstrEmpty, outer))
    m .

Definition eq_deq_ret (p1 p2 : option (queue * A)) : Prop :=
  match p1, p2 with
  | None, None => True
  | Some _, None => False
  | None, Some _ => False
  | Some (q1, a1), Some (q2, a2) => (eq_queue q1 q2) /\ (a1 = a2)
  end.

Theorem eq_deq_ret_refl : reflexive _ eq_deq_ret.
Proof.
  intros q. unfold eq_deq_ret. destruct q.
  - destruct p.
    split; reflexivity.
  - reflexivity.
Qed.
Theorem eq_deq_ret_sym : symmetric _ eq_deq_ret.
Proof.
  intros q1 q2 H. unfold eq_deq_ret. destruct q1; destruct q2.
  - destruct p0. destruct p. split; symmetry; apply H.
  - unfold eq_deq_ret in H. destruct p in H. apply H.
  - unfold eq_deq_ret in H. contradiction.
  - apply I.
Qed.
Theorem eq_deq_ret_trans : transitive _ eq_deq_ret.
Proof.
  intros q1 q2 q3. destruct q1; destruct q2; unfold eq_deq_ret; intros H1 H2.
  - destruct p. destruct p0. destruct q3. destruct p. destruct H1; destruct H2. split.
    + rewrite H. rewrite H1. reflexivity.
    + rewrite H0. rewrite H2. reflexivity.
    + apply H2.
  - destruct p. contradiction.
  - destruct p. contradiction.
  - destruct q3; auto.
Qed.

Instance eq_deq_ret_equiv : Equivalence eq_deq_ret.
Proof.
  split.
  apply eq_deq_ret_refl.
  apply eq_deq_ret_sym.
  apply eq_deq_ret_trans.
Qed.
       
Definition dequeue : queue -> option (queue * A) :=
  depRec (option (queue * A)) None dequeueHelp .

Print Proper.

Instance dequeueProper : Proper (eq_queue ==> eq_deq_ret) dequeue.
Proof.
  intros q1 q2 H.
  unfold dequeue.
  apply depRec_mor; auto.
  apply eq_deq_ret_equiv.
Qed.

Theorem dequeueEmpty : dequeue depConstrEmpty = None.
Proof.
  reflexivity.
Qed.

Print option_rect.

Definition returnOrEnq (a : A) (m : option (queue * A)) : (queue * A) :=
  @option_rect
    (queue * A)
    (fun _ => prod queue A)
    (fun (p : (queue * A)) => (enqueue a (fst p), snd p))
    (depConstrEmpty, a)
    m.

Definition dequeueEnqueueType (a : A) (q : queue) := dequeue (enqueue a q) = Some (returnOrEnq a (dequeue q)).

End TwoListQueue.

Module Tests.
  Theorem testOLQ1 : OneListQueue.dequeue (OneListQueue.enqueue 4 (3 :: 2 :: 1 :: nil)) = Some (OneListQueue.returnOrEnq 4 (OneListQueue.dequeue (3 :: 2 :: 1 :: nil))).
  Proof. auto. Qed. 
End Tests.

Module Examples.
  Parameter A : Type.
  Theorem dequeueOLQ : OneListQueue.queue -> option (OneListQueue.queue * A).
  Proof.
    apply OneListQueue.depRec.
    * exact None.
    * intros. exact X.
  Defined.

  Theorem dequeueTLQ : TwoListQueue.queue -> option (TwoListQueue.queue * A).
  Proof.
    apply TwoListQueue.depRec.
    * exact None.
    * intros. exact X.
  Defined.


  Theorem dequeueEnqueueOLQ : forall (q: OneListQueue.queue), forall (a : OneListQueue.A), OneListQueue.dequeue (OneListQueue.enqueue a q) = Some (OneListQueue.returnOrEnq a (OneListQueue.dequeue q)). 
  Proof.
    intros. apply (OneListQueue.depElimProp (fun q => (forall a, OneListQueue.dequeue (OneListQueue.enqueue a q) = Some (OneListQueue.returnOrEnq a (OneListQueue.dequeue q))))).
    * auto.
    * intros. apply (@option_rect _ _).
      - intros. 
  Admitted.

End Examples.
