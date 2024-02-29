Require Import Relation_Definitions Morphisms Lia List.
Import ListNotations.
Require Import EqdepFacts.
Require Import UIPList.
Require Import Coq.Program.Tactics.
Require Import Ornamental.Ornaments.
Require Import SetoidClass.

(* 
 * In this file, we define two representations of queues.
 * The first is just as a list; we enqueue onto the front,
 * and dequeue from the back.
 *)

Parameter A : Type.

Definition OLQ := list A.

(*
 * We define the side of the configuration corresponding to this type.
 *)

Definition depConstrOLQEmpty : OLQ := [].
Definition depConstrOLQInsert (a : A) (q : OLQ) : OLQ := a :: q.

(*
 * Notice that we have two eliminators. The first is not dependently typed,
 * but eliminates into Type, while the second is dependently typed but eliminates
 * into Prop. While we could write a single eliminator for OLQ, we need
 * two for our repair target TLQ, and the eliminators used for both the source
 * and target need their types to match.
 *)

Definition depRecOLQ (C : Type) (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) :
  (forall (x : OLQ), C) :=
  list_rect (fun _ => C) pEmpty pInsert.

Definition depElimPropOLQ (P : OLQ -> Prop) (pEmpty : P depConstrOLQEmpty)
  (pInsert : forall (a : A) (q : OLQ), P q -> P (depConstrOLQInsert a q)) :
  (forall (x : OLQ), P x) :=
  list_rect P pEmpty pInsert.

(* 
 * Below, we define the iota reduction rules. We only define them
 * for depRecOLQ, as we will not need to reduce applications of
 * depElimPropOLQ.
 *)

Theorem iotaRecOLQEmptyEq (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) :
  depRecOLQ C pEmpty pInsert depConstrOLQEmpty = pEmpty.
Proof.
  reflexivity.
Defined.

Theorem iotaRecOLQEmpty (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) :
  forall (Q : C -> Type),
    (Q (depRecOLQ C pEmpty pInsert depConstrOLQEmpty)) -> (Q pEmpty).
Proof.
  intros.
  rewrite iotaRecOLQEmptyEq in X.
  apply X.
Defined.

Theorem iotaRecOLQEmptyRev (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) :
  forall (Q : C -> Type),
    (Q pEmpty) -> (Q (depRecOLQ C pEmpty pInsert depConstrOLQEmpty)).
Proof.
  intros.
  rewrite iotaRecOLQEmptyEq.
  apply X.
Defined.

Theorem iotaRecOLQInsertEq (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) (a : A) (q : OLQ) :
  depRecOLQ C pEmpty pInsert (depConstrOLQInsert a q)
  = pInsert a q (depRecOLQ C pEmpty pInsert q).
Proof.
  reflexivity.
Defined.

Theorem iotaRecOLQInsert (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) (a : A) (q : OLQ) :
forall (a : A) (q : OLQ) (Q : C -> Type),
  Q (depRecOLQ C pEmpty pInsert (depConstrOLQInsert a q))
  -> Q (pInsert a q (depRecOLQ C pEmpty pInsert q)).
Proof.
  intros.
  rewrite iotaRecOLQInsertEq in X.
  apply X.
Defined.

Theorem iotaRecOLQInsertRev (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : OLQ), C -> C) (a : A) (q : OLQ) :
forall (a : A) (q : OLQ) (Q : C -> Type),
  Q (pInsert a q (depRecOLQ C pEmpty pInsert q))
  -> Q (depRecOLQ C pEmpty pInsert (depConstrOLQInsert a q)).
Proof.
  intros.
  rewrite iotaRecOLQInsertEq.
  apply X.
Qed.

(* 
 * We define eta, because the repair tool requires it,
 * but it is not used when transforming these terms,
 * so we just set it to the identity.
 *)

Definition etaOLQ (q : OLQ) := q.

(* 
 * Now, we define functions and theorems on this type,
 * explicitly using the constructors, eliminators,
 * and iota reduction rules we defined above,
 * and not the ones Coq generates automatically for the 
 * inductive type. This style of annotation is consistent with
 * prior work.
 *)

Definition enqueueOLQ (a : A) (q : OLQ) : OLQ :=
  depConstrOLQInsert a q.

Definition dequeueHelpOLQ (outer : A) (q : OLQ) (m : option (OLQ * A)) : option (OLQ * A) :=
@option_rect
  (OLQ * A)
  (fun _ => option (OLQ * A))
  (fun (p : (OLQ * A)) => Some (depConstrOLQInsert outer (fst p) , (snd p)))
  (Some (depConstrOLQEmpty, outer))
  m.

Definition dequeueOLQ : OLQ -> option (OLQ * A) :=
  depRecOLQ (option (OLQ * A)) None dequeueHelpOLQ.

Definition returnOrEnqOLQ (a : A) (m : option (OLQ * A)) : (OLQ * A) :=
  @option_rect
    (OLQ * A)
    (fun _ => prod OLQ A)
    (fun (p : (OLQ * A)) => (enqueueOLQ a (fst p), snd p))
    (depConstrOLQEmpty, a)
    m.

Theorem dequeueEmptyOLQ : (dequeueOLQ depConstrOLQEmpty) = None.
Proof.
  unfold dequeueOLQ.
  apply (iotaRecOLQEmptyRev _ _ dequeueHelpOLQ).
  reflexivity.
Qed.

Definition dequeueEnqueueTypeOLQ (a : A) (q : OLQ) := (dequeueOLQ (enqueueOLQ a q)) = (Some (returnOrEnqOLQ a (dequeueOLQ q))).

Theorem congOptionRect {A B C : Type} (a : A) (b : C -> A) (m : option C) (f : A -> B) :
  option_rect (fun _ => B) (fun x => f (b x)) (f a) m = f (option_rect (fun _ => A) b a m).
Proof.
  destruct m; reflexivity.
Qed.

Theorem dequeueEnqueueOLQ (a : A) (q : OLQ) : dequeueEnqueueTypeOLQ a q .
Proof.
  unfold dequeueEnqueueTypeOLQ.
  unfold dequeueOLQ.
  apply (iotaRecOLQInsertRev (option (OLQ * A)) None dequeueHelpOLQ a q).
  unfold dequeueHelpOLQ.
  unfold returnOrEnqOLQ.
  rewrite congOptionRect.
  reflexivity.
Defined.

(*
 * Here, we define a second representation of queues.
 * The pair (l1, l2) represents the queue l1 ++ (rev l2), if that
 * were a one list queue as defined above.
 * Multiple elements of this type represent the same queue, so 
 * we would want to think of it as a quotient, with 
 * [(l1, l2)] = [(l3, l4)] if l1 ++ (rev l2) = l3 ++ (rev l4).
 * Coq does not support quotient types, so instead we represent
 * this using a setoid.
 *)


Definition TLQ := prod (list A) (list A).

(*
 * We're assuming UIP here specifically on the type A. 
 * It gets used in the definition of our eliminator.
 * We do not assume it for all types, so we are not 
 * adding any axioms to our theory.
 *)

Parameter uip : UIP_ A.

Theorem listEqRectEq : Eq_rect_eq (list A).
Proof.
  apply Streicher_K__eq_rect_eq.
  apply UIP_refl__Streicher_K.
  apply UIP__UIP_refl.
  apply UIP_to_list.
  apply uip.
Qed.

(*
 * Here, we define the equivalence relation on TLQ,
 * and register it as an instance of the Equivalence typeclass
 * with Coq.
 *)

Definition insOrder (q : TLQ) :=
  match q with
  | (l1, l2) => l1 ++ rev l2
  end.

Definition eq_queue (q1 q2 : TLQ) : Prop :=
  insOrder q1 = insOrder q2.

Instance eq_queue_refl : Reflexive eq_queue.
Proof.
  intros q. reflexivity.
Qed.

Instance eq_queue_sym : Symmetric eq_queue.
Proof.
  intros q1 q2 H. symmetry. apply H.
Qed.

Instance eq_queue_trans : Transitive eq_queue.
Proof.
  intros q1 q2 q3. unfold eq_queue. intros H1 H2. rewrite H1. apply H2.
Qed.

Instance eq_queue_equiv : Equivalence eq_queue.
Proof.
  split.
  - apply eq_queue_refl.
  - apply eq_queue_sym.
  - apply eq_queue_trans.
Qed.

(*
 * We can officially declare an instance showing that TLQ forms a setoid
 * with eq_queue as the equivalence relation. However, this is not necessary
 * for any of our repair work. The automation we need derives from instances of
 * Equivalence and Proper, not Setoid.
 *)

Instance TLQ_setoid : Setoid TLQ := {equiv := eq_queue ; setoid_equiv := eq_queue_equiv}.

(* 
 * Now, we define the side of the configuration for TLQ.
 * We define several other theorems along the way to help define
 * the needed eliminators and iota-reduction rules.
 *)

Definition depConstrTLQEmpty : TLQ := ([],[]).

Definition depConstrTLQInsert (a : A) (q : TLQ) : TLQ :=
  match q with
  | (l1, l2) => (a :: l1, l2)
  end.

Instance depConstrInsertProper (a : A) :
  Proper (eq_queue ==> eq_queue) (depConstrTLQInsert a).
Proof.
  unfold eq_queue.
  intros q1 q2 H.
  destruct q1.
  destruct q2.
  simpl.
  f_equal.
  apply H.
Qed.

Notation "q1 [=] q2" := (eq_queue q1 q2) (at level 50).

Definition canonicalize (q : TLQ) := (insOrder q, @nil A) .

Theorem canonicalizeResp (q : TLQ) :
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

(* The below two lemmas are adapted from standard library, but made transparent. *)
Lemma rev_list_rect : forall P:list A-> Type,
  P [] ->
  (forall (a:A) (l:list A), P (rev l) -> P (rev (a :: l))) ->
  forall l:list A, P (rev l).
Proof.
  intros P ? ? l; induction l; auto.
Defined.

Remark rev_unit {A : Type} : forall (l:list A) (a:A), rev (l ++ a :: nil) = a :: rev l.
Proof.
  induction l.
  - reflexivity.
  - intros. simpl. rewrite IHl. reflexivity.
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

Lemma UIP_list_A:
  UIP_ (list A).
Proof.
  apply UIP_to_list. apply uip.
Qed.

Lemma rev_involutive':
  forall (l : list A) (a : A),
    rev (rev (l ++ [a])) = l ++ [a].
Proof.
  intros. rewrite rev_unit. simpl. rewrite rev_involutive. reflexivity.
Defined.

Lemma rev_involutive'_OK:
  forall (l : list A) (a : A), rev_involutive A (l ++ [a]) = rev_involutive' l a.
Proof.
 intros. pose proof (UIP_list_A). unfold UIP_ in H.
 specialize (H _ (l ++ [a]) (rev_involutive A (l ++ [a]))).
 unfold UIP_on_ in H. apply H.
Defined.

Theorem rev_rect_iota (P : list A -> Type) (empty : P []) 
  (append : forall (x : A) (l : list A), P l -> P (l ++ [x])) :
  forall (l : list A) (a : A),
    append a l (rev_rect P empty append l) = rev_rect P empty append (l ++ [a]).
Proof.
  intros l a. unfold rev_rect. rewrite rev_involutive'_OK. unfold rev_involutive'.
  destruct (rev_involutive A l). simpl. unfold eq_ind_r. simpl.
  destruct (eq_sym (rev_unit l a)). simpl. reflexivity.
Defined.

Definition depRecTLQ (C : Type) (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) :
  (forall (x : TLQ), C).
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

Theorem depRecTLQCanonical (C : Type) (eqC : C -> C -> Prop)
  `(eqC_equiv: Equivalence _ (eqC)) (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C)
  (pInsertRespectful : forall (a : A), Proper (eq_queue ==> eqC ==> eqC) (pInsert a)) :
  forall (l0 l1 : list A),
    eqC (depRecTLQ C pEmpty pInsert (l0, l1)) (depRecTLQ C pEmpty pInsert (l0 ++ rev l1, [])).
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

(*
 * Notice that we prove an instance of the Proper
 * typeclass showing that depRecTLQ is proper with respect to
 * our equivalence relations. This is important to allow
 * the setoid automation to automatically produce rewrite proofs.
 * In general, we should prove that all functions we define are Proper, 
 * but which functions must be proven proper for the automation
 * to function will vary on a case-by-case basis.
 *)

Instance depRecTLQProper (C : Type) (eqC : C -> C -> Prop)
  `(eqC_equiv : Equivalence _ eqC) (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C)
  (pInsertRespectful : forall (a : A), Proper (eq_queue ==> eqC ==> eqC) (pInsert a)) :
  Proper (eq_queue ==> eqC) (depRecTLQ C pEmpty pInsert).
Proof.
  intros x y H.
  destruct x.
  destruct y.
  rewrite depRecTLQCanonical; auto.
  unfold eq_queue in H.
  simpl in H.
  rewrite H.
  rewrite (depRecTLQCanonical C eqC eqC_equiv pEmpty pInsert pInsertRespectful l1 l2).
  reflexivity.
Qed.

(*
 * Notice that we do not prove that depElimPropTLQ is proper.
 * This is because its motive is dependently typed, and thus
 * not compatible with the built in setoid automation.
 * This is the primary reason for having two eliminators;
 * we need a dependent eliminator to Prop to prove theorems,
 * but a nondependent one to Type to easily do rewriting.
 *)

Theorem depElimPropTLQ (P : TLQ -> Prop)
  `(p : Proper (TLQ -> Prop) (eq_queue ==> iff) P) (pEmpty : P depConstrTLQEmpty)
  (pInsert : forall (a : A) (q : TLQ), P q -> P (depConstrTLQInsert a q)) :
  (forall (x : TLQ), P x).
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

Theorem iotaRecTLQEmptyEq (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) :
  depRecTLQ C pEmpty pInsert depConstrTLQEmpty = pEmpty.
Proof.
  reflexivity.
Defined.

Theorem iotaRecTLQEmpty (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) :
  forall (Q : C -> Type),
    (Q (depRecTLQ C pEmpty pInsert depConstrTLQEmpty)) -> (Q pEmpty).
Proof.
  intros.
  rewrite iotaRecTLQEmptyEq in X.
  apply X.
Defined.

Theorem iotaRecTLQEmptyRev (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) :
  forall (Q : C -> Type),
    (Q pEmpty) -> (Q (depRecTLQ C pEmpty pInsert depConstrTLQEmpty)).
Proof.
  intros.
  rewrite iotaRecTLQEmptyEq.
  apply X.
Defined.

Theorem iotaRecTLQInsertEq (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) (a : A) (q : TLQ) :
  depRecTLQ C pEmpty pInsert (depConstrTLQInsert a q)
  = pInsert a q (depRecTLQ C pEmpty pInsert q).
Proof.
  destruct q.
  reflexivity.
Defined.

Theorem iotaRecTLQInsert (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) (a : A) (q : TLQ) :
forall (a : A) (q : TLQ) (Q : C -> Type),
  Q (depRecTLQ C pEmpty pInsert (depConstrTLQInsert a q))
  -> Q (pInsert a q (depRecTLQ C pEmpty pInsert q)).
Proof.
  intros.
  rewrite iotaRecTLQInsertEq in X.
  apply X.
Defined.

Theorem iotaRecTLQInsertRev (C : Type)
  (pEmpty : C)
  (pInsert : forall (a : A) (q : TLQ), C -> C) (a : A) (q : TLQ) :
forall (a : A) (q : TLQ) (Q : C -> Type),
  Q (pInsert a q (depRecTLQ C pEmpty pInsert q))
  -> Q (depRecTLQ C pEmpty pInsert (depConstrTLQInsert a q)).
Proof.
  intros.
  rewrite iotaRecTLQInsertEq.
  apply X.
Qed.

Definition etaTLQ (q : TLQ) := q.

Definition eq_prod (A B : Type) (eqA : A -> A -> Prop)
  (eqB : B -> B -> Prop) (p1 p2 : A * B) : Prop :=
  match p1, p2 with
  | (a1 , b1) , (a2 , b2) => (eqA a1 a2) /\ (eqB b1 b2)
  end.

Instance eq_prod_refl (A B : Type) (eqA : A -> A -> Prop) `(Reflexive _ eqA) (eqB : B -> B -> Prop) `(Reflexive _ eqB) : Reflexive (eq_prod A B eqA eqB).
Proof.
  intros q. unfold eq_prod. destruct q.
  split; reflexivity.
Qed.

Instance eq_prod_sym (A B : Type) (eqA : A -> A -> Prop) `(Symmetric _ eqA) (eqB : B -> B -> Prop) `(Symmetric _ eqB) : Symmetric (eq_prod A B eqA eqB).
Proof.
  intros q1 q2 H1. unfold eq_prod.
  destruct q1.
  destruct q2.
  destruct H1.
  split; symmetry; auto.
Qed.

Instance eq_prod_trans (A B : Type) (eqA : A -> A -> Prop) `(Transitive _ eqA) (eqB : B -> B -> Prop) `(Transitive _ eqB) : Transitive (eq_prod A B eqA eqB).
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

Instance eq_prod_equiv (A B : Type) (eqA : A -> A -> Prop) `(Equivalence _ eqA) (eqB : B -> B -> Prop) `(Equivalence _ eqB) : Equivalence (eq_prod A B eqA eqB).
Proof.
  destruct H. destruct H0. split.
  - apply eq_prod_refl; auto.
  - apply eq_prod_sym; auto.
  - apply eq_prod_trans; auto.
Qed.

Definition eq_option (A : Type) (eqA : A -> A -> Prop) (m1 m2 : option A) : Prop :=
  match m1, m2 with
  | None, None => True
  | Some _, None => False
  | None, Some _ => False
  | Some a1, Some a2 => eqA a1 a2
  end.

Instance eq_option_refl (A : Type) (eqA : A -> A -> Prop) `(Reflexive _ eqA) : Reflexive (eq_option A eqA).
Proof.
  intros m. unfold eq_option. destruct m. reflexivity. apply I.
Qed.

Instance eq_option_sym (A : Type) (eqA : A -> A -> Prop) `(Symmetric _ eqA) : Symmetric (eq_option A eqA).
Proof.
  intros m1 m2 H0.
  unfold eq_option.
  destruct m1; destruct m2; auto.
Qed.

Instance eq_option_trans (A : Type) (eqA : A -> A -> Prop) `(Transitive _ eqA) : Transitive (eq_option A eqA).
Proof.
  intros m1 m2 m3 H0 H1.
  unfold eq_option.
  destruct m1; destruct m2; destruct m3; auto.
  - apply (H a a0 a1); auto.
  - unfold eq_option in H0.
    contradiction.
Qed.

Instance eq_option_equiv (A : Type) (eqA : A -> A -> Prop) `(Equivalence _ eqA) : Equivalence (eq_option A eqA).
Proof.
  destruct H. split.
  - apply eq_option_refl; auto.
  - apply eq_option_sym; auto.
  - apply eq_option_trans; auto.
Qed.

Instance someProper (A : Type) (eqA : A -> A -> Prop) :
  Proper (eqA ==> eq_option A eqA) Some.
Proof.
  intros a1 a2 H1.
  apply H1.
Qed.

Definition deq_ret := option (prod TLQ A).

Definition eq_deq_ret := eq_option (prod TLQ A) (@eq_prod TLQ A eq_queue eq).

Instance eq_deq_ret_refl : Reflexive eq_deq_ret.
Proof.
  unfold eq_deq_ret.
  apply eq_option_refl.
  apply eq_prod_refl.
  apply eq_queue_refl.
  auto.
Qed.

Instance eq_deq_ret_sym : Symmetric eq_deq_ret.
Proof.
  unfold eq_deq_ret.
  apply eq_option_sym.
  apply eq_prod_sym.
  apply eq_queue_sym.
  auto.
Qed.

Instance eq_deq_ret_trans : Transitive eq_deq_ret.
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

(* 
 * We define the setoid equivalence between OLQ and TLQ here.
 * We don't strictly need to have it defined to do the transformation, 
 * but the existing repair tool currently uses the functions internally 
 * as a key for caching.
 *)

Definition promote (q : OLQ) := (q, @nil A).

Definition forget (q : TLQ) := insOrder q.

Theorem section : forall (q : OLQ), forget (promote q) = q.
Proof.
  intros.
  induction q.
  - reflexivity.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
Qed.

Theorem retraction : forall (q : TLQ), promote (forget q) [=] q.
Proof.
  intros.
  unfold promote.
  unfold forget.
  unfold eq_queue.
  simpl.
  apply app_nil_r.
Qed.

(*
 * Now, we specify our setoid to the automation. Types contains a list of
 * the types with specified equivalence relations, rels contains the equivalence
 * relations, and equiv_proofs contains the proofs that the relations are 
 * instances of Equvialence. They must be provided in the same order; that is,
 * the nth element of types, rels, and equiv_proofs should all correspond to the
 * same type.
 *)

Save setoid OLQ TLQ { promote = promote ; forget = forget ; types = TLQ deq_ret ; rels = eq_queue eq_deq_ret ; equiv_proofs = eq_queue_equiv eq_deq_ret_equiv }.

Configure Lift OLQ TLQ {
    constrs_a = depConstrOLQEmpty depConstrOLQInsert ;
    constrs_b = depConstrTLQEmpty depConstrTLQInsert ;
    elim_a = depRecOLQ ;
    elim_b = depRecTLQ ;
    eta_a = etaOLQ ;
    eta_b = etaTLQ ;
    iota_a = iotaRecOLQEmpty iotaRecOLQEmptyRev iotaRecOLQInsert iotaRecOLQInsertRev ;
    iota_b = iotaRecTLQEmpty iotaRecTLQEmptyRev iotaRecTLQInsert iotaRecTLQInsertRev
  }.

(*
 * We first lift the dependent eliminator, which prevents the tool from
 * unfolding the definition of the repaired eliminator. This helps the 
 * setoid automation successfully discover proofs.
 *)

Lift OLQ TLQ in depRecOLQ as depRecLifted.

(* Now, we begin lifting the functions we defined over OLQ. *)

Lift OLQ TLQ in enqueueOLQ as enqueueTLQ.

(* At present, Pumpkin Pi will not generate proofs that the
 * functions we define are Proper, so we need to do this manually.
 * In the future, we can automatically discover many of these 
 * proofs using tactics for proof search, such as the one below.
 *)

Instance enqueueTLQProper (a : A) : Proper (eq_queue ==> eq_queue) (enqueueTLQ a).
Proof.
  solve_proper.
Qed.

Lift OLQ TLQ in dequeueHelpOLQ as dequeueHelpTLQ.

Instance dequeueHelpTLQProper (a : A) :
  Proper (eq_queue ==> eq_deq_ret ==> eq_deq_ret) (dequeueHelpTLQ a).
Proof.
  intros q1 q2 H0 m1 m2 H1.
  destruct m1; destruct m2; simpl.
  - split.
    + apply depConstrInsertProper.
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

Lift OLQ TLQ in dequeueOLQ as dequeueTLQ.

Instance dequeueTLQProper : Proper (eq_queue ==> eq_deq_ret) dequeueTLQ.
Proof.
  solve_proper.
Qed.

Lift OLQ TLQ in returnOrEnqOLQ as returnOrEnqTLQ.

Instance returnOrEnqTLQProper (a : A) :
  Proper (eq_deq_ret ==> (eq_prod TLQ A eq_queue eq)) (returnOrEnqTLQ a).
Proof.
  intros m1 m2 H.
  destruct m1; destruct m2.
  -  simpl.
     destruct p.
     destruct p0.
     destruct H.
     split.
     + apply enqueueTLQProper.
       apply H.
     + apply H0.
  - contradiction.
  - contradiction.
  - simpl.
    split; reflexivity.
Qed.

(* We can similarly lift dequeueEmptyOLQ, dequeueEnqueueTypeOLQ and dequeueEnqueueOLQ. *)

Lift OLQ TLQ in dequeueEmptyOLQ as dequeueEmptyTLQ.

Lift OLQ TLQ in dequeueEnqueueTypeOLQ as dequeueEnqueueTypeTLQ.

Lift OLQ TLQ in dequeueEnqueueOLQ as dequeueEnqueueTLQ.

(*
 * The repaired dequeue function we have is correct, and comes with many theorems,
 * but it is not especially efficient, because it require computing a canonical
 * element of the equivalence class of its inputs. 
 * Now, we see how we can define a more efficient dequeue function, and prove
 * that it produces the same output as the lifted dequeue function.
 * First, we define our fast dequeue function. Notice that it can directly access 
 * the head of the second list if it is nonempty, and only reverses the first list
 * onto the second list if the second list is empty. This improves the average case
 * runtime of the function from linear to constant.
 *)

Definition fastDequeueTLQ (q : TLQ) : deq_ret :=
  let (l1, l2) := q in
  match l1, l2 with
  | [] , [] => None
  | h1 :: t1 , [] => Some (([] , tl (rev l1)), hd h1 (rev l1))
  | _ , h2 :: t2 => Some ((l1, t2), h2)
  end.

(*
 * Next, we prove several theorems to show that 
 * fastDequeueTLQ and dequeueTLQ are extensionally equal.
 *)

Theorem headTailNonempty (a : A) (l : list A) :
  (hd a (l ++ [a])) :: (tl (l ++ [a])) = l ++ [a].
Proof.
  destruct l; reflexivity.
Qed.

Theorem fastDequeueProperHelp (q : TLQ) :
  eq_deq_ret (fastDequeueTLQ q) (fastDequeueTLQ ([], rev (insOrder q))).
Proof.
  intros.
  destruct q.
  unfold eq_deq_ret.
  unfold eq_option.
  unfold eq_prod.
  destruct l; destruct l0.
  - apply I.
  - simpl.
    rewrite rev_unit.
    rewrite rev_involutive.
    unfold eq_queue.
    split; reflexivity.
  - simpl.
    rewrite app_nil_r.
    rewrite <- headTailNonempty.
    split; reflexivity.
  - simpl.
    rewrite <- headTailNonempty.
    rewrite app_assoc.
    rewrite rev_app_distr.
    simpl.
    split.
    + unfold eq_queue.
      simpl.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      reflexivity.
    + reflexivity.
Qed.  

Instance fastDequeueProper :
  Proper (eq_queue ==> eq_deq_ret) fastDequeueTLQ.
Proof.
  intros q1 q2 H1.
  rewrite fastDequeueProperHelp.
  rewrite (fastDequeueProperHelp q2).
  f_equiv.
  rewrite H1.
  reflexivity.
Qed.

Theorem tlApp (l1 l2 : list A) :
  l1 <> [] -> tl (l1 ++ l2) = tl(l1) ++ l2.
Proof.
  intros.
  destruct l1.
  - contradiction.
  - reflexivity.
Qed.

Theorem hdApp (l : list A) (a1 a2 : A) :
  hd a1 ((l ++ [a2]) ++ [a1]) = hd a2 (l ++ [a2]).
Proof.
  destruct l; reflexivity.
Qed.

(* Destructs on a queue. *)
Ltac queuedestruct queue := 
  let qleft := fresh "x" in
  let qright := fresh "y" in
  destruct queue as (qleft, qright); try destruct qleft; try destruct qright.

Theorem fastDequeueEnqueue (a : A) (q : TLQ) :
  eq_deq_ret
    (fastDequeueTLQ (enqueueTLQ a q))
    (Some (returnOrEnqTLQ a (fastDequeueTLQ q))).
Proof.
  queuedestruct q.
  - reflexivity.
  - split; reflexivity.
  - simpl.
    split.
    + unfold eq_queue.
      simpl.
      rewrite tlApp.
      rewrite rev_app_distr.
      reflexivity.
      rewrite <- headTailNonempty.
      intros H.
      symmetry in H.
      apply nil_cons in H.
      apply H.
    + apply hdApp.
  - split; reflexivity.
Qed.

(*
 * Finally, we see that dequeueTLQ and fastDequeueTLQ are extensionally equal.
 * This theorem allows us to translate theorems about dequeueTLQ
 * into theorems about fastDequeueTLQ, so long as we can unfold definitions
 * to the point where dequeueTLQ is being applied to arguments.
 * If we could prove that dequeueTLQ = fastDequeueTLQ, that restriction would not
 * apply, and we could just rewrite terms by that equality. 
 * However, we cannot prove that the functions themselves are equal, because
 * we do not assume functional extensionality.
 *)

Theorem dequeueEqualsFastDequeue : forall (q : TLQ),
    eq_deq_ret (dequeueTLQ q) (fastDequeueTLQ q).
Proof.
  apply depElimPropTLQ.
  - intros q1 q2 H.
    rewrite H.
    reflexivity.
  - reflexivity.
  - intros.
    rewrite fastDequeueEnqueue.
    rewrite dequeueEnqueueTLQ.
    rewrite H.
    reflexivity.
Qed.
