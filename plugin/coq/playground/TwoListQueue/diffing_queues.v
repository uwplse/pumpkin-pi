Require setoid_crazy_queue.
Require setoid_two_list_queue_sigma_simplified_proof_objects.
Require single_list_queue.
Require Import List Bool.
Import ListNotations.
Import Equivalence.
Require Import Morphisms.
Require Import Specif.
Require Import StructTact.StructTactics.

Module Crazy := setoid_crazy_queue.

Module CrazyTwoListQueue.
  
Import Crazy.TwoListQueue.
  
Lemma raw_enq_not_empty_base : forall (A : Type) (a : A) (l0 : list A) (H : rep_ok ([], l0)),
  raw_is_empty (raw_enq a ([], l0)) = false.
Proof.
  intros. induction l0.
  - reflexivity.
  - bad_rep_ok H.
Qed.

Print raw_enq_not_empty_base.

Theorem raw_enq_not_empty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty (raw_enq a q) = false.
Proof.
  intros. induction q as [l l0].
  induction l.
  - apply (raw_enq_not_empty_base _ _ _ H).
  - reflexivity.
Qed.
End CrazyTwoListQueue.

Print CrazyTwoListQueue.raw_enq_not_empty.

Module Sigma := setoid_two_list_queue_sigma_simplified_proof_objects.

Module TwoListQueue.

Import Sigma.TwoListQueue.
  
Lemma raw_enq_not_empty_base : forall (A : Type) (a : A) (l0 : list A) (H : rep_ok ([], l0)),
  raw_is_empty (raw_enq a ([], l0)) = false.
Proof.
  intros. reflexivity.
Qed.

Print raw_enq_not_empty_base.

Theorem raw_enq_not_empty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty (raw_enq a q) = false.
Proof.
  intros.
  induction q as [l l0].
  induction l.
  - apply (raw_enq_not_empty_base _ _ _ H).
  - reflexivity.
Qed.

End TwoListQueue.

Module Simple := single_list_queue.

Module SimpleQueue.

Import Simple.SimpleQueue.

Lemma enq_not_empty_base : forall (A : Type) (a : A),
  is_empty (enq a []) = false.
Proof.
  intros.
  reflexivity.
Qed.

Theorem enq_not_empty : forall (A : Type) (a : A) (q : queue A),
    is_empty (enq a q) = false.
Proof.
  intros.
  induction q.
  - apply enq_not_empty_base.
  - reflexivity.
Qed.

End SimpleQueue.

Print SimpleQueue.enq_not_empty.

Print TwoListQueue.raw_enq_not_empty.

Print CrazyTwoListQueue.raw_enq_not_empty.

Definition simple_is_empty {A : Type} := @Simple.SimpleQueue.is_empty A.

Definition simple_enq {A : Type} := @Simple.SimpleQueue.enq A.

Definition simple_lemma := @SimpleQueue.enq_not_empty_base.

Definition simple_queue := Simple.SimpleQueue.queue.

Definition enq_not_empty_simple (A : Type) (a : A) (q : simple_queue A) :
  simple_is_empty (simple_enq a q) = false :=
list_ind
  (fun q0 : list A =>
    simple_is_empty (simple_enq a q0) = false)
  (simple_lemma A a)
  (fun (_ : A) (q0 : list A) _ =>
     eq_refl)
  q.

Definition sigma_raw_is_empty {A : Type} := @Sigma.TwoListQueue.raw_is_empty A.

Definition sigma_raw_enq {A : Type} := @Sigma.TwoListQueue.raw_enq A.

Definition sigma_lemma := @TwoListQueue.raw_enq_not_empty_base.

Definition sigma_raw_queue := Sigma.TwoListQueue.raw_queue.

Definition sigma_rep_ok {A : Type} := @Sigma.TwoListQueue.rep_ok A.

Definition raw_enq_not_empty_sigma (A : Type) (a : A) (q : sigma_raw_queue A) (H : sigma_rep_ok q):
       sigma_raw_is_empty
         (sigma_raw_enq a q) = false :=
prod_ind
  (fun q0 : list A * list A =>
   sigma_rep_ok q0 ->
   sigma_raw_is_empty (sigma_raw_enq a q0) = false)
  (fun
    (l l0 : list A)
    (H0 : sigma_rep_ok (l, l0)) =>
      list_ind
        (fun l1 : list A =>
          sigma_rep_ok (l1, l0) ->
          sigma_raw_is_empty (sigma_raw_enq a (l1, l0))
            = false)
        (fun H1 : sigma_rep_ok ([], l0) =>
          sigma_lemma A a l0 H1)
        (fun (a0 : A) (l1 : list A) _ _ =>
          eq_refl)
        l
        H0)
  q
  H.

Definition crazy_raw_is_empty {A : Type} := @Crazy.TwoListQueue.raw_is_empty A.

Definition crazy_raw_enq {A : Type} := @Crazy.TwoListQueue.raw_enq A.

Definition crazy_lemma := @CrazyTwoListQueue.raw_enq_not_empty_base.

Definition crazy_raw_queue := Crazy.TwoListQueue.raw_queue.

Definition crazy_rep_ok {A : Type} := @Crazy.TwoListQueue.rep_ok A.

Definition raw_enq_not_empty_crazy (A : Type) (a : A) (q : crazy_raw_queue A) (H : crazy_rep_ok q):
       crazy_raw_is_empty
         (crazy_raw_enq a q) = false :=
prod_ind
  (fun q0 : list A * list A =>
   crazy_rep_ok q0 ->
   crazy_raw_is_empty (crazy_raw_enq a q0) = false)
  (fun
    (l l0 : list A)
    (H0 : crazy_rep_ok (l, l0)) =>
      list_ind
        (fun l1 : list A =>
          crazy_rep_ok (l1, l0) ->
          crazy_raw_is_empty (crazy_raw_enq a (l1, l0))
            = false)
        (fun H1 : crazy_rep_ok ([], l0) =>
          crazy_lemma A a l0 H1)
        (fun (a0 : A) (l1 : list A) _ _ =>
          eq_refl)
        l
        H0)
  q
  H.

Print TwoListQueue.raw_enq_not_empty_base.

Definition sigma_raw_enq_not_empty_base (A : Type) (a : A) (l0 : list A) (H : sigma_rep_ok ([], l0)) :
  sigma_raw_is_empty (sigma_raw_enq a ([], l0)) =
    false := 
eq_refl.     

Print CrazyTwoListQueue.raw_enq_not_empty_base.

Definition crazy_rep_ok_contradiction := @Crazy.TwoListQueue.rep_ok_contradiction.

Definition crazy_raw_enq_not_empty_base (A : Type) (a : A) (l0 : list A) (H : crazy_rep_ok ([], l0)) :
  crazy_raw_is_empty
    (crazy_raw_enq a ([], l0)) =
       false
  :=
list_ind
  (fun l1 : list A =>
     crazy_rep_ok ([], l1) ->
     crazy_raw_is_empty
       (crazy_raw_enq a ([], l1)) = false)
  (fun _ =>
     eq_refl)
  (fun
     (a0 : A)
     (l1 : list A)
     _
     (H0 : crazy_rep_ok ([], a0 :: l1)) =>
     let H1 : False :=
       crazy_rep_ok_contradiction A a0 l1 H0 in
       False_ind
         (crazy_raw_is_empty
           (crazy_raw_enq a ([], a0 :: l1)) =
            false)
         H1)
  l0
  H.
