Require Import setoid_equivalence.
Require Import single_list_queue.
Require Import setoid_two_list_queue_sigma_simplified_proof_objects.
Require Import Coq.Classes.RelationClasses.
Require Import List.
Import ListNotations.
Module TwoListQueue := setoid_two_list_queue_sigma_simplified_proof_objects.TwoListQueue.
Module SingleListQueue := single_list_queue.SimpleQueue.

Definition slq {A : Type} := SingleListQueue.queue A.

Print SingleListQueue.queue.

Definition tlq {A : Type} := TwoListQueue.queue A.

Print TwoListQueue.queue.

Definition g {A : Type} (q : TwoListQueue.queue A) : (SingleListQueue.queue A) :=
  match (proj1_sig q) with
  | (l1, l2) => l1 ++ List.rev l2
  end.

Definition f {A : Type} (q : SingleListQueue.queue A) : (TwoListQueue.queue A) :=
  exist TwoListQueue.rep_ok (q, []) (fun _ => eq_refl).

(**
Section test.

Context `{setoida : Setoid (SingleListQueue A)}.

End test.
**)

(**
Definition equ (A : Type) : @SetoidEquivalence.setoid_equiv (SingleListQueue.queue A) (@SingleListQueue.slq_setoid A) (TwoListQueue.queue A) (@TwoListQueue.tlq_setoid A).
Proof.
  induction.
  apply (SetoidEquivalence.mkEquiv f g). constructor.
**)

Theorem equ (A : Type) : @SetoidEquivalence.setoid_equiv (SingleListQueue.queue A) (@SingleListQueue.slq_setoid A) (TwoListQueue.queue A) (@TwoListQueue.tlq_setoid A).
Proof.
  apply (@SetoidEquivalence.mkEquiv (SingleListQueue.queue A) (@SingleListQueue.slq_setoid A) (TwoListQueue.queue A) (@TwoListQueue.tlq_setoid A) f g).
  - intros.
    rewrite H.
    reflexivity.
  - intros.
    apply H.
  - intros.
    unfold f.
    unfold g.
    simpl.
    rewrite List.app_nil_r.
    reflexivity.
  - intros.
    unfold f.
    unfold g.
    simpl.
    unfold TwoListQueue.equiv.
    unfold TwoListQueue.raw_equiv.
    simpl.
    rewrite app_nil_r.
    reflexivity.
Defined.

Print equ.
