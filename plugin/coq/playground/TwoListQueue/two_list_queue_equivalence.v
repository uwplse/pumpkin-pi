Require Import List Relation_Definitions Morphisms Setoid.
Import ListNotations.
Require Import EqdepFacts.
Require Import UIPList.

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
  
  Theorem listEqRectEq : Eq_rect_eq (list A).
  Proof.
    apply Streicher_K__eq_rect_eq.
    apply UIP_refl__Streicher_K.
    apply UIP__UIP_refl.
    apply UIP_to_list.
    apply uip.
  Qed.
  
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

  Theorem rev_rect_iota (P : list A -> Type) (empty : P []) 
    (append : forall (x : A) (l : list A), P l -> P (l ++ [x]))
    (a : A) (l : list A) :
    append a l (rev_rect P empty append l) = rev_rect P empty append (l ++ [a]).
  Proof.
    rewrite <- (rev_involutive A l).
    pose (P' := fun (l : list A) => append a (rev l) (rev_rect P empty append (rev l)) = rev_rect P empty append (rev l ++ [a])).
    apply (rev_list_ind P').
    + unfold P'. simpl. unfold rev_rect. simpl.
      unfold eq_rect. Print eq_ind_r.
      simpl.
    give_up.
  Admitted.

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

  Definition depRec (C : Type) (pEmpty : C)
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

  Ltac canon := unfold eq_queue; simpl; try (rewrite app_nil_r; auto).

  Theorem depRecUnfoldInsert (C : Type) (eq_C : C -> C -> Prop) `(eq_C_equiv: Equivalence _ (eq_C)) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C)
    (pInsertRespectful : forall (a : A) (q1 q2 : queue) (c : C),
        q1 [=] q2 -> eq_C (pInsert a q1 c) (pInsert a q2 c)) :
    forall (a : A) (q1 q2 : queue),
      q1 [=] q2 -> eq_C (depRec C pEmpty pInsert (depConstrInsert a q1)) (pInsert a q2 (depRec C pEmpty pInsert q2)).
  Proof.
    intros.
    destruct q1 as (q1l, q1r).
    destruct q2 as (q2l, q2r).
    destruct q1l.
    - destruct q2l.
      + unfold eq_queue in H. unfold insOrder in H. rewrite 2 app_nil_l in H.
        pose proof (f_equal (@rev (A)) H).
        rewrite rev_involutive in H0.
        rewrite rev_involutive in H0.
        rewrite H0.
        unfold depRec at 1. (* should be solvable now *)
        give_up.
      + destruct q1r.
        * unfold eq_queue in H. discriminate.
        * assert (a1 :: q1r <> []) by discriminate.
          pose proof (@app_removelast_last A (a1 :: q1r) a1 H0).
          rewrite H1. rewrite H1 in H.
          assert (last (a1 :: q1r) a1 = a0). give_up. (* should be solvable *)
          rewrite H2. rewrite H2 in H.
          assert (removelast (a1 :: q1r) = q2r ++ rev q2l).
            unfold eq_queue in H. unfold insOrder in H. 
            rewrite app_nil_l in H. rewrite rev_unit in H.
            rewrite <- app_comm_cons in H.
            pose proof (@f_equal (list A) (list A) (fun x => (rev (@tl TwoListQueue.A x))) _ _ H).
            unfold tl in H3. rewrite rev_involutive in H3. rewrite rev_app_distr in H3. rewrite rev_involutive in H3. exact H3.
          rewrite H3. (* at some point I may need an inductive hyp *) give_up.
          
    - destruct q2l.
      + destruct q2r.
        * unfold eq_queue in H. discriminate.
        * give_up.
      + give_up.
  Admitted.

  Theorem depRecCanonical (C : Type) (eqC : C -> C -> Prop) `(eqC_equiv: Equivalence _ (eqC)) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C)
    (pInsertRespectful : forall (a : A), Proper (eq_queue ==> eqC ==> eqC) (pInsert a)) :
    forall (l0 l1 : list A),
      eqC (depRec C pEmpty pInsert (l0, l1)) (depRec C pEmpty pInsert (l0 ++ rev l1, [])).
  Proof.
    intros.
    induction l0 as [ | a l0].
    - induction l1 as [ | b l1] using rev_rect.
      + reflexivity.
      + simpl. rewrite rev_app_distr. simpl.
        rewrite <- rev_rect_iota.
        apply (pInsertRespectful b).
        * unfold eq_queue. simpl. rewrite app_nil_r. reflexivity.
        * apply IHl1.
    - simpl.
      apply (pInsertRespectful a).
      + unfold eq_queue.
        simpl.
        rewrite app_nil_r.
        reflexivity.
      + apply IHl0.
  Qed.
  
  Add Parametric Morphism (C : Type) (eqC : C -> C -> Prop) `(eqC_equiv : Equivalence _ eqC) (pEmpty : C)
    (pInsert : forall (a : A) (q : queue), C -> C)
    (pInsertRespectful : forall (a : A), Proper (eq_queue ==> eqC ==> eqC) (pInsert a)) :
    (depRec C pEmpty pInsert)
      with signature eq_queue ==> eqC as depRec_mor.
  Proof.
    intros.
    destruct x.
    destruct y.
    rewrite depRecCanonical; auto.
    unfold eq_queue in H.
    simpl in H.
    rewrite H.
    rewrite (depRecCanonical C eqC eqC_equiv pEmpty pInsert pInsertRespectful l1 l2).
    reflexivity.
  Qed.

  Theorem depElimProp (P : queue -> Prop) `(p : Proper (queue -> Prop) (eq_queue ==> iff) P) (pEmpty : P depConstrEmpty)
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

Definition eq_prod {A B : Type} (eqA : A -> A -> Prop) (eqB : B -> B -> Prop) (p1 p2 : A * B) : Prop :=
  match p1, p2 with
  | (a1 , b1) , (a2 , b2) => (eqA a1 a2) /\ (eqB b1 b2)
  end.

Theorem eq_prod_refl {A B : Type} (eqA : A -> A -> Prop) `(Reflexive _ eqA) (eqB : B -> B -> Prop) `(Reflexive _ eqB) : Reflexive (eq_prod eqA eqB).
Proof.
  intros q. unfold eq_prod. destruct q.
  split; reflexivity.
Qed.

Theorem eq_prod_sym {A B : Type} (eqA : A -> A -> Prop) `(Symmetric _ eqA) (eqB : B -> B -> Prop) `(Symmetric _ eqB) : Symmetric (eq_prod eqA eqB).
Proof.
  intros q1 q2 H1. unfold eq_prod.
  destruct q1.
  destruct q2.
  destruct H1.
  split; symmetry; auto.
Qed.

Theorem eq_prod_trans {A B : Type} (eqA : A -> A -> Prop) `(Transitive _ eqA) (eqB : B -> B -> Prop) `(Transitive _ eqB) : Transitive (eq_prod eqA eqB).
Proof.
  intros q1 q2 q3 H1 H2. unfold eq_prod.
  destruct q1.
  destruct q2.
  destruct q3.
  destruct H1.
  destruct H2.
  split.
  - apply (H a a0 a1); auto.
  - apply (H0 b b0 b1); auto.
Qed.

Theorem eq_prod_equiv {A B : Type} (eqA : A -> A -> Prop) `(Equivalence _ eqA) (eqB : B -> B -> Prop) `(Equivalence _ eqB) : Equivalence (eq_prod eqA eqB).
Proof.
  destruct H. destruct H0. split.
  - apply eq_prod_refl; auto.
  - apply eq_prod_sym; auto.
  - apply eq_prod_trans; auto.
Qed.

Definition eq_option {A : Type} (eqA : A -> A -> Prop) (m1 m2 : option A) : Prop :=
  match m1, m2 with
  | None, None => True
  | Some _, None => False
  | None, Some _ => False
  | Some a1, Some a2 => eqA a1 a2
  end.

Theorem eq_option_refl {A : Type} (eqA : A -> A -> Prop) `(Reflexive _ eqA) : Reflexive (eq_option eqA).
Proof.
  intros m. unfold eq_option. destruct m. reflexivity. apply I.
Qed.

Theorem eq_option_sym {A : Type} (eqA : A -> A -> Prop) `(Symmetric _ eqA) : Symmetric (eq_option eqA).
Proof.
  intros m1 m2 H0.
  unfold eq_option.
  destruct m1; destruct m2; auto.
Qed.

Theorem eq_option_trans {A : Type} (eqA : A -> A -> Prop) `(Transitive _ eqA) : Transitive (eq_option eqA).
Proof.
  intros m1 m2 m3 H0 H1.
  unfold eq_option.
  destruct m1; destruct m2; destruct m3; auto.
  - apply (H a a0 a1); auto.
  - unfold eq_option in H0.
    contradiction.
Qed.

Theorem eq_option_equiv {A : Type} (eqA : A -> A -> Prop) `(Equivalence _ eqA) : Equivalence (eq_option eqA).
Proof.
  destruct H. split.
  - apply eq_option_refl; auto.
  - apply eq_option_sym; auto.
  - apply eq_option_trans; auto.
Qed.

Definition eq_deq_ret := eq_option (@eq_prod queue A eq_queue eq).

Theorem eq_deq_ret_refl : reflexive _ eq_deq_ret.
Proof.
  unfold eq_deq_ret.
  apply eq_option_refl.
  apply eq_prod_refl.
  apply eq_queue_refl.
  auto.
Qed.

Theorem eq_deq_ret_sym : symmetric _ eq_deq_ret.
Proof.
  unfold eq_deq_ret.
  apply eq_option_sym.
  apply eq_prod_sym.
  apply eq_queue_sym.
  auto.
Qed.

Theorem eq_deq_ret_trans : transitive _ eq_deq_ret.
Proof.
  unfold eq_deq_ret.
  apply eq_option_trans.
  apply eq_prod_trans.
  apply eq_queue_trans.
  intros x y z H0 H1.
  rewrite H0.
  apply H1.
Qed.

Instance eq_deq_ret_equiv : Equivalence eq_deq_ret.
Proof.
  split.
  apply eq_deq_ret_refl.
  apply eq_deq_ret_sym.
  apply eq_deq_ret_trans.
Qed.

Definition dequeueHelpProper (a : A) :
  Proper (eq_queue ==> eq_deq_ret ==> eq_deq_ret) (dequeueHelp a).
Proof.
  intros q1 q2 H0 m1 m2 H1.
  destruct m1; destruct m2; simpl.
  - split.
    + apply insert_mor.
      destruct p.
      destruct p0.
      simpl.
      simpl in H1.
      destruct H1.
      apply H.
    + destruct p.
      destruct p0.
      simpl in H1.
      destruct H1.
      apply H1.
  - contradiction.
  - contradiction.
  - split; reflexivity.
Qed.  
       
Definition dequeue : queue -> option (queue * A) :=
  depRec (option (queue * A)) None dequeueHelp .

Print Proper.

Instance dequeueProper : Proper (eq_queue ==> eq_deq_ret) dequeue.
Proof.
  intros q1 q2 H.
  unfold dequeue.
  apply depRec_mor.
  apply eq_deq_ret_equiv.
  apply dequeueHelpProper.
  apply H.
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

Definition dequeueEnqueueType (a : A) (q : queue) := eq_deq_ret (dequeue (enqueue a q)) (Some (returnOrEnq a (dequeue q))).


(* destructs on a queue in the env *)
Ltac queuedestruct queue := 
  let qleft := fresh "x" in
  let qright := fresh "y" in
  destruct queue as (qleft, qright); try destruct qleft; try destruct qright.

Theorem dequeueEnqueueTypeProper (a : A) : Proper (eq_queue ==> iff) (dequeueEnqueueType a) .
Proof.
  intros q1 q2 H.
  unfold dequeueEnqueueType.
  split; intros H1.
  - assert (eq_deq_ret (dequeue (enqueue a q2)) (dequeue (enqueue a q1))).
    apply dequeueProper.
    apply enqueueProper.
    apply symmetry.
    apply H.
    assert (eq_deq_ret (Some (returnOrEnq a (dequeue q1))) (Some (returnOrEnq a (dequeue q2)))).
    * pose proof dequeueProper q1 q2 H. remember (dequeue q1) as dq1; destruct dq1; remember (dequeue q2) as dq2; destruct dq2; simpl.
      + destruct p. destruct p0. split. 
        assert (q [=] q0). apply H2. simpl. apply enqueueProper. apply H3.
        assert (a0 = a1). apply H2. simpl. apply H3.
      + unfold eq_deq_ret in H2. destruct p. contradiction.
      + destruct p. unfold eq_deq_ret in H2. contradiction.
      + split. apply (eq_queue_refl depConstrEmpty). reflexivity.
    * pose proof (eq_deq_ret_trans _ _ _ H0 H1). exact (eq_deq_ret_trans _ _ _ H3 H2).
  - assert (eq_deq_ret (dequeue (enqueue a q2)) (dequeue (enqueue a q1))).
    apply dequeueProper.
    apply enqueueProper.
    apply symmetry.
    apply H.
    assert (eq_deq_ret (Some (returnOrEnq a (dequeue q1))) (Some (returnOrEnq a (dequeue q2)))).
    * pose proof dequeueProper q1 q2 H. remember (dequeue q1) as dq1; destruct dq1; remember (dequeue q2) as dq2; destruct dq2; simpl.
      + destruct p. destruct p0. split. 
        assert (q [=] q0). apply H2. simpl. apply enqueueProper. apply H3.
        assert (a0 = a1). apply H2. simpl. apply H3.
      + unfold eq_deq_ret in H2. destruct p. contradiction.
      + destruct p. unfold eq_deq_ret in H2. contradiction.
      + split. apply (eq_queue_refl depConstrEmpty). reflexivity.
    * apply symmetry in H0. pose proof (eq_deq_ret_trans _ _ _ H0 H1). apply symmetry in H2. exact (eq_deq_ret_trans _ _ _ H3 H2).
Defined.

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
