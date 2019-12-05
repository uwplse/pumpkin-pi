Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

(*
 * This file includes more about records, including
 * tests that the curry record functionality works correctly,
 * rather than the simple walkthrough from minimal_records.v.
 *)

(* TODO document all new functionality *)
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

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

Scheme Induction for output Sort Set.
Scheme Induction for output Sort Prop.
Scheme Induction for output Sort Type.

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

Preprocess Module Handwritten4 as Handwritten4' { opaque Nat.add }.
Preprocess Module Generated4 as Generated4' { opaque Nat.add }.

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
Lift Generated4'.output Handwritten4'.output in Generated4'.op as op_1 { opaque Nat.add Generated4'.Coq_Init_Datatypes_andb }.
Lift Generated4'.input Handwritten4'.input in op_1 as op { opaque Nat.add Generated4'.Coq_Init_Datatypes_andb }.
Lift Generated4'.output Handwritten4'.output in Generated4'.and_spec_true_true as and_spec_true_true_1 { opaque Generated4'.Coq_Init_Datatypes_andb_true_intro }.
Lift Generated4'.input Handwritten4'.input in and_spec_true_true_1 as and_spec_true_true { opaque Nat.add Generated4'.Coq_Init_Datatypes_andb Generated4'.Coq_Init_Datatypes_andb_true_intro }.
Lift Generated4'.output Handwritten4'.output in Generated4'.plus_spec_O_l as plus_spec_O_l_1 { opaque Generated4'.Coq_Init_Logic_eq_ind_r }.
Lift Generated4'.input Handwritten4'.input in plus_spec_O_l_1 as plus_spec_O_l { opaque Nat.add Generated4'.Coq_Init_Datatypes_andb Generated4'.Coq_Init_Logic_eq_ind_r }.
Lift Generated4'.output Handwritten4'.output  in Generated4'.plus_spec_O_r as plus_spec_O_l_r { opaque Nat.add Generated4'.Coq_Init_Datatypes_andb Generated4'.Coq_Init_Peano_plus_n_O Generated4'.Coq_Init_Logic_eq_sym Generated4'.Coq_Init_Logic_eq_ind_r }.
Lift Generated4'.input Handwritten4'.input in plus_spec_O_l_r as plus_spec_O_r { opaque Nat.add Generated4'.Coq_Init_Datatypes_andb Generated4'.Coq_Init_Peano_plus_n_O Generated4'.Coq_Init_Logic_eq_sym Generated4'.Coq_Init_Logic_eq_ind_r }.

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

(*
 * TODO WIP from here out
 *)

Module HandwrittenParams.

Record input (T1 T2 T3 : Type) := MkInput
{
  first : T1;
  second : T2;
  third : T3;
}.

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

End HandwrittenParams.

Module GeneratedParams.

Definition input (T1 T2 T3 : Type) := (prod T1 (prod T2 T3)).

End GeneratedParams.

Find ornament HandwrittenParams.input GeneratedParams.input as input_params_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* --- Test a larger record with parameters --- *)

Module HandwrittenParams4.

Record input (T1 T2 T3 T4 : Type) := MkInput
{
  first : T1;
  second : T2;
  third : T3;
  fourth : T4;
}.

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

End HandwrittenParams4.

Module GeneratedParams4.

Definition input (T1 T2 T3 T4 : Type) := (prod T1 (prod T2 (prod T3 T4))).

End GeneratedParams4.

Find ornament HandwrittenParams4.input GeneratedParams4.input as input_params4_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* -- Test swapped params --- *)

Module HandwrittenParams4Swapped.

Record input (T1 T2 T3 T4 : Type) := MkInput
{
  first : T1;
  second : T2;
  third : T4;
  fourth : T3;
}.

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

End HandwrittenParams4Swapped.

Module GeneratedParams4Swapped.

Definition input (T1 T2 T3 T4 : Type) := (prod T1 (prod T2 (prod T4 T3))).

End GeneratedParams4Swapped.

Find ornament HandwrittenParams4Swapped.input GeneratedParams4Swapped.input as input_params4_swapped_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* --- Test fancier parameters --- *)

Module HandwrittenParamsFancy.

Record input (T : Type) (t : T) (F : T -> Prop) := MkInput
{
  first  : F t;
  second : T;
  third : exists t', t <> t' -> F t';
}.

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

End HandwrittenParamsFancy.

Module GeneratedParamsFancy.

Definition input (T : Type) (t : T) (F : T -> Prop) :=
  (prod (F t) (prod T (exists t', t <> t' -> F t'))).

End GeneratedParamsFancy.

Find ornament HandwrittenParamsFancy.input GeneratedParamsFancy.input as input_params_fancy_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* --- Things left: --- *)

(* TODO test: failure cases, eta expanded or not expanded variations, taking prod directly, etc *)
(* TODO check test results *)
