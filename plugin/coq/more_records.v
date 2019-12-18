Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)
Set Nonrecursive Elimination Schemes. (* <--- Preprocess needs induction principles for records *)

(*
 * This file includes more about records, including
 * tests that the curry record functionality works correctly,
 * rather than the simple walkthrough from minimal_records.v.
 *)

(* TODO remove extra imports and functions that aren't used now *)
(* TODO note somewhere: Can you find patch between left and right? Then use as a unified example w/ PUMPKIN PATCH? *)

(* --- Test a record with 4 fields --- *)

Module Handwritten4.

Record input := MkInput
{
  field1  : bool;
  field2    : nat;
  field3 : bool;
  field4 : nat; 
}.

Record output := MkOutput
{
  field2and4  : nat;
  field1and3 : bool;
}.

Definition op (r : input) :=
  MkOutput
    (field2 r + field4 r)
    (andb (field1 r) (field3 r)).

Theorem and_spec_true_true
  (r : input)
  (F : field1 r = true)
  (S : field3 r = true)
  : field1and3 (op r) = true.
Proof.
  destruct r as [f n s].
  unfold op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

Theorem plus_spec_O_l
  (r : input) 
  (F : field2 r = O)
  : field2and4 (op r) = field4 r.
Proof.
  destruct r as [f n s].
  unfold op.
  simpl in *.
  subst. reflexivity.
Qed.

Theorem plus_spec_O_r
  (r : input) 
  (F : field4 r = O)
  : field2and4 (op r) = field2 r.
Proof.
  destruct r as [f n s].
  unfold op.
  simpl in *.
  subst. auto.
Qed.

End Handwritten4.

Module Generated4.

Definition input := (prod bool (prod nat (prod bool nat))).

Definition output := (prod nat bool).

Definition MkInput (b1 : bool) (n1 : nat) (b2 : bool) (n2 : nat) :=
  pair b1 (pair n1 (pair b2 n2)).

Definition MkOutput (n : nat) (b : bool) :=
  pair n b.

Definition field1 (r : input) : bool :=
  (fst r).

Definition field2 (r : input) : nat :=
  (fst (snd r)).

Definition field3 (r : input) : bool :=
  (fst (snd (snd r))).

Definition field4 (r : input) : nat :=
  (snd (snd (snd r))).

Definition field2and4 (r : output) : nat :=
  (fst r).

Definition field1and3 (r : output) : bool :=
  (snd r).

Definition op (r : input) : output :=
  (pair
    (plus (field2 r) (field4 r))
    (andb (field1 r) (field3 r))).

Theorem and_spec_true_true
  (r : input)
  (F : field1 r = true)
  (S : field3 r = true)
  : field1and3 (op r) = true.
Proof.
  destruct r. repeat destruct p. 
  unfold op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

Theorem plus_spec_O_l
  (r : input) 
  (F : field2 r = O)
  : field2and4 (op r) = field4 r.
Proof.
  destruct r. repeat destruct p.
  unfold op.
  simpl in *.
  rewrite F.
  reflexivity.
Qed.

Theorem plus_spec_O_r
  (r : input) 
  (F : field4 r = O)
  : field2and4 (op r) = field2 r.
Proof.
  destruct r. repeat destruct p.
  unfold op.
  simpl in *.
  rewrite F.
  auto.
Qed.

End Generated4.

Preprocess Module Handwritten4 as Handwritten4' { opaque Nat.add andb eq_ind_r eq_ind plus_n_O eq_sym  andb_true_intro }.
Preprocess Module Generated4 as Generated4' { opaque Nat.add andb eq_ind_r eq_ind plus_n_O eq_sym andb_true_intro }.

Configure Lift Handwritten4'.input Generated4'.input { opaque Nat.add andb eq_ind_r eq_ind plus_n_O eq_sym andb_true_intro Generated4'.output Generated4'.MkOutput }.
Configure Lift Handwritten4'.output Generated4'.output { opaque Nat.add andb eq_ind_r eq_ind plus_n_O eq_sym andb_true_intro Generated4'.input Generated4'.MkInput }.

Module LiftedHandwritten4.

Lift Handwritten4'.input Generated4'.input in Handwritten4'.MkInput as MkInput.
Lift Handwritten4'.output Generated4'.output in Handwritten4'.MkOutput as MkOutput.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.field1 as field1.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.field2 as field2.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.field3 as field3.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.field4 as field4.
Lift Handwritten4'.output Generated4'.output in Handwritten4'.field2and4 as field2and4.
Lift Handwritten4'.output Generated4'.output in Handwritten4'.field1and3 as field1and3.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.op as op_1.
Lift Handwritten4'.output Generated4'.output in op_1 as op.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.and_spec_true_true as and_spec_true_true_1.
Lift Handwritten4'.output Generated4'.output in and_spec_true_true_1 as and_spec_true_true.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.plus_spec_O_l as plus_spec_O_l_1.
Lift Handwritten4'.output Generated4'.output in plus_spec_O_l_1 as plus_spec_O_l.
Lift Handwritten4'.input Generated4'.input in Handwritten4'.plus_spec_O_r as plus_spec_O_l_r.
Lift Handwritten4'.output Generated4'.output in plus_spec_O_l_r as plus_spec_O_r.

Lemma testMkInput:
  MkInput = Generated4.MkInput.
Proof.
  auto.
Qed. 

Lemma testMkOutput:
  MkOutput = Generated4.MkOutput.
Proof.
  auto.
Qed. 

Lemma testField1:
  field1 = Generated4.field1.
Proof.
  auto.
Qed. 

Lemma testField2:
  forall i, field2 i = Generated4.field2 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField3:
  forall i, field3 i = Generated4.field3 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField4:
  forall i, field4 i = Generated4.field4 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField2and4:
  field2and4 = Generated4.field2and4.
Proof.
  auto.
Qed. 

Lemma testField1and3:
  field1and3 = Generated4.field1and3.
Proof.
  auto.
Qed. 

Lemma testOp:
  forall r, op r = Generated4.op r.
Proof.
  intros. induction r. auto.
Qed.

Lemma testAndSpecTrueTrue:
  forall r : Generated4.input,
    Generated4.field1 r = true ->
    Generated4.field3 r = true ->
    Generated4.field1and3 (Generated4.op r) = true.
Proof.
  intros. induction r. apply and_spec_true_true; auto.
Qed.

Lemma testPlusSpecOl:
  forall r : Generated4.input,
    Generated4.field2 r = 0 ->
    Generated4.field2and4 (Generated4.op r) = Generated4.field4 r.
Proof.
  intros. induction r. rewrite <- testOp. apply plus_spec_O_l; auto.
Qed.

Lemma testPlusSpecOr:
  forall r : Generated4.input,
    Generated4.field4 r = 0 ->
    Generated4.field2and4 (Generated4.op r) = Generated4.field2 r.
Proof.
  intros. induction r. rewrite <- testOp. apply plus_spec_O_r; auto.
Qed.

End LiftedHandwritten4.

Module LiftedGenerated4.

Lift Generated4'.input Handwritten4'.input in Generated4'.MkInput as MkInput.
Lift Generated4'.output Handwritten4'.output in Generated4'.MkOutput as MkOutput.
Lift Generated4'.input Handwritten4'.input in Generated4'.field1 as field1.
Lift Generated4'.input Handwritten4'.input in Generated4'.field2 as field2.
Lift Generated4'.input Handwritten4'.input in Generated4'.field3 as field3.
Lift Generated4'.input Handwritten4'.input in Generated4'.field4 as field4.
Lift Generated4'.output Handwritten4'.output in Generated4'.field2and4 as field2and4.
Lift Generated4'.output Handwritten4'.output in Generated4'.field1and3 as field1and3.
Lift Generated4'.output Handwritten4'.output in Generated4'.op as .._1.
Lift Generated4'.input Handwritten4'.input in op_1 as op.
Lift Generated4'.output Handwritten4'.output in Generated4'.and_spec_true_true as .._1.
Lift Generated4'.input Handwritten4'.input in and_spec_true_true_1 as and_spec_true_true.
Lift Generated4'.output Handwritten4'.output in Generated4'.plus_spec_O_l as plus_spec_O_l_1.
Lift Generated4'.input Handwritten4'.input in plus_spec_O_l_1 as plus_spec_O_l.
Lift Generated4'.output Handwritten4'.output  in Generated4'.plus_spec_O_r as plus_spec_O_l_r.
Lift Generated4'.input Handwritten4'.input in plus_spec_O_l_r as plus_spec_O_r.

(* Note that Handwritten4.input and Handwritten4'.input are equivalent, but not equal because
   of how Coq's equality works (will not prove). *)

Lemma testMkInput:
  MkInput = Handwritten4'.MkInput.
Proof.
  auto.
Qed. 

Lemma testMkOutput:
  MkOutput = Handwritten4'.MkOutput.
Proof.
  auto.
Qed. 

Lemma testField1:
  field1 = Handwritten4'.field1.
Proof.
  auto.
Qed. 

Lemma testField2:
  forall i, field2 i = Handwritten4'.field2 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField3:
  forall i, field3 i = Handwritten4'.field3 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField4:
  forall i, field4 i = Handwritten4'.field4 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField2and4:
  field2and4 = Handwritten4'.field2and4.
Proof.
  auto.
Qed. 

Lemma testField1and3:
  field1and3 = Handwritten4'.field1and3.
Proof.
  auto.
Qed. 

Lemma testOp:
  forall r, op r = Handwritten4'.op r.
Proof.
  intros. induction r. auto.
Qed.

Lemma testAndSpecTrueTrue':
  forall r : Handwritten4'.input,
    Handwritten4'.field1 r = true ->
    Handwritten4'.field3 r = true ->
    Handwritten4'.field1and3 (Handwritten4'.op r) = true.
Proof.
  intros. induction r. apply and_spec_true_true; auto.
Qed.

Lemma testAndSpecTrueTrue:
  forall r : Handwritten4.input,
    Handwritten4.field1 r = true ->
    Handwritten4.field3 r = true ->
    Handwritten4.field1and3 (Handwritten4.op r) = true.
Proof.
  intros. induction r. 
  pose proof (testAndSpecTrueTrue' (Handwritten4'.MkInput field5 field6 field7 field8)).
  auto.
Qed.

Lemma testPlusSpecOl':
  forall r : Handwritten4'.input,
    Handwritten4'.field2 r = 0 ->
    Handwritten4'.field2and4 (Handwritten4'.op r) = Handwritten4'.field4 r.
Proof.
  intros. induction r. rewrite <- testOp. apply plus_spec_O_l; auto.
Qed.

Lemma testPlusSpecOl:
  forall r : Handwritten4.input,
    Handwritten4.field2 r = 0 ->
    Handwritten4.field2and4 (Handwritten4.op r) = Handwritten4.field4 r.
Proof.
  intros. induction r.
  pose proof (testPlusSpecOl' (Handwritten4'.MkInput field5 field6 field7 field8)).
  auto.
Qed.

Lemma testPlusSpecOr':
  forall r : Handwritten4'.input,
    Handwritten4'.field4 r = 0 ->
    Handwritten4'.field2and4 (Handwritten4'.op r) = Handwritten4'.field2 r.
Proof.
  intros. induction r. rewrite <- testOp. apply plus_spec_O_r; auto.
Qed.

Lemma testPlusSpecOr:
  forall r : Handwritten4.input,
    Handwritten4.field4 r = 0 ->
    Handwritten4.field2and4 (Handwritten4.op r) = Handwritten4.field2 r.
Proof.
  intros. induction r.
  pose proof (testPlusSpecOr' (Handwritten4'.MkInput field5 field6 field7 field8)).
  auto.
Qed.

End LiftedGenerated4.

(* --- Test a record with parameters --- *)

Module HandwrittenParams.

Record input (T1 T2 T3 T4 : Type) := MkInput
{
  field1 : T1;
  field2 : T2;
  field3 : T3;
  field4 : T4;
}.

Record output (T1 T2 : Type) := MkOutput
{
  field2and4  : T1;
  field1and3 : T2;
}.

Definition op {T1 T2 T3 T4 T5 T6 : Type} (f : T2 -> T4 -> T5) (g : T1 -> T3 -> T6) (r : input T1 T2 T3 T4) :=
  MkOutput _ _
    (f (field2 _ _ _ _ r) (field4 _ _ _ _ r))
    (g (field1 _ _ _ _ r) (field3 _ _ _ _ r)).

Theorem and_spec_true_true :
  forall {T1 T2 T3 : Type} (f : T1 -> T2 -> T3) 
  (r : input bool T1 bool T2)
  (F : field1 _ _ _ _ r = true)
  (S : field3 _ _ _ _ r = true),
  field1and3 _ _ (op f andb r) = true.
Proof.
  intros.
  destruct r as [f' n s].
  unfold op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

Theorem plus_spec_O_l:
  forall {T1 T2 T3 : Type} (g : T1 -> T2 -> T3) 
  (r : input T1 nat T2 nat) 
  (F : field2 _ _ _ _ r = O),
  field2and4 _ _ (op plus g r) = field4 _ _ _ _ r.
Proof.
  intros.
  destruct r as [f n s].
  unfold op.
  simpl in *.
  subst. reflexivity.
Qed.

Theorem plus_spec_O_r:
  forall {T1 T2 T3 : Type} (g : T1 -> T2 -> T3) 
  (r : input T1 nat T2 nat) 
  (F : field4 _ _ _ _ r = O),
  field2and4 _ _ (op plus g r) = field2 _ _ _ _ r.
Proof.
  intros.
  destruct r as [f n s].
  unfold op.
  simpl in *.
  subst. auto.
Qed.

End HandwrittenParams.

Module GeneratedParams.

Definition input (T1 T2 T3 T4 : Type) := (prod T1 (prod T2 (prod T3 T4))).

Definition output (T1 T2 : Type) := (prod T1 T2).

Definition MkInput (T1 T2 T3 T4 : Type) (t1 : T1) (t2 : T2) (t3 : T3) (t4 : T4) :=
  pair t1 (pair t2 (pair t3 t4)).

Definition MkOutput (T1 T2 : Type) (t1 : T1) (t2 : T2) :=
  pair t1 t2.

Definition field1 (T1 T2 T3 T4 : Type) (r : input T1 T2 T3 T4) : T1 :=
  (fst r).

Definition field2 (T1 T2 T3 T4 : Type) (r : input T1 T2 T3 T4) : T2 :=
  (fst (snd r)).

Definition field3 (T1 T2 T3 T4 : Type) (r : input T1 T2 T3 T4) : T3 :=
  (fst (snd (snd r))).

Definition field4 (T1 T2 T3 T4 : Type) (r : input T1 T2 T3 T4) : T4 :=
  (snd (snd (snd r))).

Definition field2and4 (T1 T2 : Type) (r : output T1 T2) : T1 :=
  (fst r).

Definition field1and3 (T1 T2 : Type) (r : output T1 T2) : T2 :=
  (snd r).

Definition op {T1 T2 T3 T4 T5 T6 : Type} (f : T2 -> T4 -> T5) (g : T1 -> T3 -> T6) (r : input T1 T2 T3 T4) : output T5 T6 :=
  (pair
    (f (field2 _ _ _ _ r) (field4 _ _ _ _ r))
    (g (field1 _ _ _ _ r) (field3 _ _ _ _ r))).

Theorem and_spec_true_true:
  forall {T1 T2 T3 : Type} (f : T1 -> T2 -> T3) 
  (r : input bool T1 bool T2)
  (F : field1 _ _ _ _ r = true)
  (S : field3 _ _ _ _ r = true),
  field1and3 _ _ (op f andb r) = true.
Proof.
  intros.
  destruct r. repeat destruct p. 
  unfold op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

Theorem plus_spec_O_l:
  forall {T1 T2 T3 : Type} (g : T1 -> T2 -> T3) 
  (r : input T1 nat T2 nat) 
  (F : field2 _ _ _ _ r = O),
  field2and4 _ _ (op plus g r) = field4 _ _ _ _ r.
Proof.
  intros.
  destruct r. repeat destruct p.
  unfold op.
  simpl in *.
  rewrite F.
  reflexivity.
Qed.

Theorem plus_spec_O_r:
  forall {T1 T2 T3 : Type} (g : T1 -> T2 -> T3) 
  (r : input T1 nat T2 nat) 
  (F : field4 _ _ _ _ r = O),
  field2and4 _ _ (op plus g r) = field2 _ _ _ _ r.
Proof.
  intros.
  destruct r. repeat destruct p.
  unfold op.
  simpl in *.
  rewrite F.
  auto.
Qed.

End GeneratedParams.

Preprocess Module HandwrittenParams as HandwrittenParams' { opaque Nat.add }.
Preprocess Module GeneratedParams as GeneratedParams' { opaque Nat.add }.

Module LiftedHandwrittenParams.

Configure Lift HandwrittenParams'.input GeneratedParams'.input { opaque HandwrittenParams'.input_rect }.
Fail Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.input_rect as input_rect'.
Configure Lift HandwrittenParams'.input  GeneratedParams'.input { ~opaque HandwrittenParams'.input_rect }.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.input_rect as input_rect'.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.output_rect as output_rect'.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.MkInput as MkInput.
Lift HandwrittenParams'.output GeneratedParams'.output in HandwrittenParams'.MkOutput as MkOutput.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.field1 as field1.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.field2 as field2.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.field3 as field3.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.field4 as field4.
Lift HandwrittenParams'.output GeneratedParams'.output in HandwrittenParams'.field2and4 as field2and4.
Lift HandwrittenParams'.output GeneratedParams'.output in HandwrittenParams'.field1and3 as field1and3.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.op as op_1.
Lift HandwrittenParams'.output GeneratedParams'.output in op_1 as op.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.and_spec_true_true as and_spec_true_true_1.
Lift HandwrittenParams'.output GeneratedParams'.output in and_spec_true_true_1 as and_spec_true_true.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.plus_spec_O_l as plus_spec_O_l_1.
Lift HandwrittenParams'.output GeneratedParams'.output in plus_spec_O_l_1 as plus_spec_O_l.
Lift HandwrittenParams'.input GeneratedParams'.input in HandwrittenParams'.plus_spec_O_r as plus_spec_O_l_r.
Lift HandwrittenParams'.output GeneratedParams'.output in plus_spec_O_l_r as plus_spec_O_r.

Lemma testMkInput:
  forall (T1 T2 T3 T4 : Type),
    MkInput = GeneratedParams.MkInput.
Proof.
  auto.
Qed. 

Lemma testMkOutput:
  MkOutput = GeneratedParams.MkOutput.
Proof.
  auto.
Qed. 

Lemma testField1:
  field1 = GeneratedParams.field1.
Proof.
  auto.
Qed. 

Lemma testField2:
  forall T1 T2 T3 T4 i,
    field2 T1 T2 T3 T4 i = GeneratedParams.field2 T1 T2 T3 T4 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField3:
  forall T1 T2 T3 T4 i,
    field3 T1 T2 T3 T4 i = GeneratedParams.field3 T1 T2 T3 T4 i.
Proof.
  intros. induction i. auto.
Qed.

Lemma testField4:
  forall T1 T2 T3 T4 i,
    field4 T1 T2 T3 T4 i = GeneratedParams.field4 T1 T2 T3 T4 i.
Proof.
  intros. induction i. auto.
Qed.

Lemma testField2and4:
  field2and4 = GeneratedParams.field2and4.
Proof.
  auto.
Qed. 

Lemma testField1and3:
  field1and3 = GeneratedParams.field1and3.
Proof.
  auto.
Qed. 

Lemma testOp:
  forall T1 T2 T3 T4 T5 T6 g f r,
    op T1 T2 T3 T4 T5 T6 g f r = GeneratedParams.op g f r.
Proof.
  intros. induction r. auto.
Qed.

Lemma testAndSpecTrueTrue:
  forall (T1 T2 T3 : Type) (f : T1 -> T2 -> T3) (r : GeneratedParams.input bool T1 bool T2),
    GeneratedParams.field1 _ _ _ _ r = true ->
    GeneratedParams.field3 _ _ _ _ r = true ->
    GeneratedParams.field1and3 _ _ (GeneratedParams.op f andb r) = true.
Proof.
  intros. induction r. induction b. induction b.
  apply (and_spec_true_true T1 T2 T3 f); auto.
Qed.

Lemma testPlusSpecOl:
  forall (T1 T2 T3 : Type) (g : T1 -> T2 -> T3) (r : GeneratedParams.input T1 nat T2 nat),
    GeneratedParams.field2 _ _ _ _ r = 0 ->
    GeneratedParams.field2and4 _ _ (GeneratedParams.op Nat.add g r) = GeneratedParams.field4 _ _ _ _ r.
Proof.
  intros. induction r. induction b. induction b.
  rewrite <- testOp. apply (plus_spec_O_l T1 T2 T3 g). auto.
  
Qed.

Lemma testPlusSpecOr:
  forall (T1 T2 T3 : Type) (g : T1 -> T2 -> T3) (r : GeneratedParams.input T1 nat T2 nat),
    GeneratedParams.field4 _ _ _ _ r = 0 ->
    GeneratedParams.field2and4 _ _ (GeneratedParams.op Nat.add g r) = GeneratedParams.field2 _ _ _ _ r.
Proof.
  intros. induction r. induction b. induction b.
  rewrite <- testOp. apply (plus_spec_O_r T1 T2 T3 g); auto.
Qed.

End LiftedHandwrittenParams.

Module LiftedGeneratedParams. 

Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.MkInput as MkInput.
Lift GeneratedParams'.output HandwrittenParams'.output in GeneratedParams'.MkOutput as MkOutput.
Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.field1 as field1.
Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.field2 as field2.
Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.field3 as field3.
Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.field4 as field4.
Lift GeneratedParams'.output HandwrittenParams'.output in GeneratedParams'.field2and4 as field2and4.
Lift GeneratedParams'.output HandwrittenParams'.output in GeneratedParams'.field1and3 as field1and3.
Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.op as op_1.
Lift GeneratedParams'.output HandwrittenParams'.output in op_1 as op
  { opaque 
     Nat.add GeneratedParams'.Coq_Init_Datatypes_andb 
     field1 field2 field3 field4
  }.

(* It is much better to start with the bigger constant, here input. Might even need to sometimes,
   since you are basically playing egraph here. *)
Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.and_spec_true_true as and_spec_true_true_1 {
  opaque Nat.add GeneratedParams'.Coq_Init_Datatypes_andb
  GeneratedParams'.Coq_Init_Datatypes_andb_true_intro
  GeneratedParams'.field1and3 GeneratedParams'.field2and4 }.
Lift GeneratedParams'.output HandwrittenParams'.output in and_spec_true_true_1 as and_spec_true_true {
  opaque GeneratedParams'.Coq_Init_Datatypes_andb_true_intro
  field1 field2 field3 field4 MkInput }.

Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.plus_spec_O_l as plus_spec_O_l_1
  { opaque
     Nat.add GeneratedParams'.Coq_Init_Datatypes_andb
     GeneratedParams'.Coq_Init_Datatypes_andb_true_intro
     GeneratedParams'.field1and3 GeneratedParams'.field2and4 }.
Lift GeneratedParams'.output HandwrittenParams'.output in plus_spec_O_l_1 as plus_spec_O_l 
  { opaque 
     Nat.add GeneratedParams'.Coq_Init_Datatypes_andb
     GeneratedParams'.Coq_Init_Logic_eq_ind_r
     field1 field2 field3 field4 MkInput }.

Lift GeneratedParams'.input HandwrittenParams'.input in GeneratedParams'.plus_spec_O_r as plus_spec_O_l_r
  { opaque
     Nat.add GeneratedParams'.Coq_Init_Datatypes_andb
     GeneratedParams'.Coq_Init_Datatypes_andb_true_intro
     GeneratedParams'.field1and3 GeneratedParams'.field2and4 }.
Lift GeneratedParams'.output HandwrittenParams'.output in plus_spec_O_l_r as plus_spec_O_r 
  { opaque 
     Nat.add GeneratedParams'.Coq_Init_Datatypes_andb 
     GeneratedParams'.Coq_Init_Peano_plus_n_O 
     GeneratedParams'.Coq_Init_Logic_eq_sym 
     GeneratedParams'.Coq_Init_Logic_eq_ind_r
     field1 field2 field3 field4 }.

Lemma testMkInput:
  forall (T1 T2 T3 T4 : Type),
    MkInput = HandwrittenParams'.MkInput.
Proof.
  auto.
Qed. 

Lemma testMkOutput:
  MkOutput = HandwrittenParams'.MkOutput.
Proof.
  auto.
Qed. 

Lemma testField1:
  field1 = HandwrittenParams'.field1.
Proof.
  auto.
Qed. 

Lemma testField2:
  forall T1 T2 T3 T4 i,
    field2 T1 T2 T3 T4 i = HandwrittenParams'.field2 T1 T2 T3 T4 i.
Proof.
  intros. induction i. auto.
Qed. 

Lemma testField3:
  forall T1 T2 T3 T4 i,
    field3 T1 T2 T3 T4 i = HandwrittenParams'.field3 T1 T2 T3 T4 i.
Proof.
  intros. induction i. auto.
Qed.

Lemma testField4:
  forall T1 T2 T3 T4 i,
    field4 T1 T2 T3 T4 i = HandwrittenParams'.field4 T1 T2 T3 T4 i.
Proof.
  intros. induction i. auto.
Qed.

Lemma testField2and4:
  field2and4 = HandwrittenParams'.field2and4.
Proof.
  auto.
Qed. 

Lemma testField1and3:
  field1and3 = HandwrittenParams'.field1and3.
Proof.
  auto.
Qed. 

Lemma testOp:
  forall T1 T2 T3 T4 T5 T6 g f r,
    op T1 T2 T3 T4 T5 T6 g f r = HandwrittenParams'.op _ _ _ _ _ _ g f r.
Proof.
  intros. induction r. auto.
Qed.

Lemma testAndSpecTrueTrue:
  forall (T1 T2 T3 : Type) (f : T1 -> T2 -> T3) (r : HandwrittenParams'.input bool T1 bool T2),
    HandwrittenParams'.field1 _ _ _ _ r = true ->
    HandwrittenParams'.field3 _ _ _ _ r = true ->
    HandwrittenParams'.field1and3 _ _ (HandwrittenParams'.op _ _ _ _ _ _ f andb r) = true.
Proof.
  intros. induction r.
  apply (and_spec_true_true T1 T2 T3 f); auto.
Qed.

Lemma testPlusSpecOl:
  forall (T1 T2 T3 : Type) (g : T1 -> T2 -> T3) (r : HandwrittenParams'.input T1 nat T2 nat),
    HandwrittenParams'.field2 _ _ _ _ r = 0 ->
    HandwrittenParams'.field2and4 _ _ (HandwrittenParams'.op _ _ _ _ _ _ Nat.add g r) = HandwrittenParams'.field4 _ _ _ _ r.
Proof.
  intros. induction r.
  rewrite <- testOp. apply plus_spec_O_l; auto.
Qed.

Lemma testPlusSpecOr:
  forall (T1 T2 T3 : Type) (g : T1 -> T2 -> T3) (r : HandwrittenParams'.input T1 nat T2 nat),
    HandwrittenParams'.field4 _ _ _ _ r = 0 ->
    HandwrittenParams'.field2and4 _ _ (HandwrittenParams'.op _ _ _ _ _ _ Nat.add g r) = HandwrittenParams'.field2 _ _ _ _ r.
Proof.
  intros. induction r.
  rewrite <- testOp. apply plus_spec_O_r; auto.
Qed.

End LiftedGeneratedParams.

(* --- Test fancier parameters --- x*)

Module HandwrittenParamsFancy.

Record input (T : Type) (t : T) (F : T -> Prop) := MkInput
{
  first  : F t;
  second : T;
  third : exists t', t <> t' -> F t';
}.

End HandwrittenParamsFancy.

Module GeneratedParamsFancy.

Definition input (T : Type) (t : T) (F : T -> Prop) :=
  (prod (F t) (prod T (exists t', t <> t' -> F t'))).

End GeneratedParamsFancy.

Find ornament HandwrittenParamsFancy.input GeneratedParamsFancy.input as input_params_fancy_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* --- Things left: --- *)

(* TODO test: failure cases, eta expanded or not expanded variations (e.g. try not eta expanded constr with parameters, like (prod nat) ), taking prod directly, etc *)
(* TODO check test results *)
  