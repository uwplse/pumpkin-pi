Require Import Ornamental.Ornaments.

Definition generated_input := (prod bool (prod nat bool)).

Record handwritten_input := MkInput
{
  firstBool  : bool;
  numberI    : nat;
  secondBool : bool;
}.

Scheme Induction for handwritten_input Sort Set.
Scheme Induction for handwritten_input Sort Prop.
Scheme Induction for handwritten_input Sort Type.

Definition generated_output := (prod nat bool).

Record handwritten_output := MkOutput
{
  numberO  : nat;
  andBools : bool;
}.

Scheme Induction for handwritten_output Sort Set.
Scheme Induction for handwritten_output Sort Prop.
Scheme Induction for handwritten_output Sort Type.

Definition generated_firstBool (r : (prod bool (prod nat bool))) : bool :=
  (fst r).

Definition generated_numberI (r : (prod bool (prod nat bool))) : nat :=
  (fst (snd r)).

Definition generated_secondBool (r : (prod bool (prod nat bool))) : bool :=
  (snd (snd r)).

Definition generated_andBools (r : (prod nat bool)) : bool :=
  (snd r).

Definition generated_op (r : (prod bool (prod nat bool))) : (prod nat bool) :=
  (pair
    (generated_numberI r)
    (andb
      (generated_firstBool  r)
      (generated_secondBool r)
    )
  ).

Definition handwritten_op (r : handwritten_input) : handwritten_output :=
  {|
    numberO  := numberI r;
    andBools := firstBool r && secondBool r;
  |}.

Theorem handwritten_and_spec_true_true
  (r : handwritten_input)
  (F : firstBool  r = true)
  (S : secondBool r = true)
  : andBools (handwritten_op r) = true.
Proof.
  destruct r as [f n s].
  unfold handwritten_op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

Theorem generated_and_spec_true_true
  (r : generated_input)
  (F : generated_firstBool  r = true)
  (S : generated_secondBool r = true)
  : generated_andBools (generated_op r) = true.
Proof.
  destruct r as [f [n s]].
  unfold generated_op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

Definition g2h_input (r : generated_input) : handwritten_input :=
  let '(f, (n, s)) := r in
  {| firstBool := f; numberI := n; secondBool := s |}.

Definition g2h_output (r : generated_output) : handwritten_output :=
  let '(n, b) := r in
  {| numberO := n; andBools := b |}.

Definition h2g_input (r : handwritten_input) : generated_input :=
  (pair (firstBool r) (pair (numberI r) (secondBool r))).

Definition h2g_output (r : handwritten_output) : generated_output :=
  (pair (numberO r) (andBools r)).

Lemma h2g2h_output_spec (h : handwritten_output) : g2h_output (h2g_output h) = h.
Proof.
  destruct h.
  compute.
  reflexivity.
Qed.

(* The most basic test: When this works, should just give us fst *)
Set DEVOID search prove equivalence.
Find ornament handwritten_input generated_input.

Print handwritten_input_curry.
Print handwritten_input_curry_inv.

Find ornament handwritten_output generated_output.
Lift handwritten_input generated_input in firstBool as lifted_firstBool.

Record handwritten_input_4 := MkInput4
{
  field1  : bool;
  field2    : nat;
  field3 : bool;
  field4 : nat; 
}.

Definition generated_input_4 := (prod bool (prod nat (prod bool nat))).

Scheme Induction for handwritten_input_4 Sort Set.
Scheme Induction for handwritten_input_4 Sort Prop.
Scheme Induction for handwritten_input_4 Sort Type.

Find ornament handwritten_input_4 generated_input_4.

Record handwritten_input_5 := MkInput5
{
  field1'  : bool;
  field2'    : nat;
  field3' : bool;
  field4' : nat;
  field5' : bool; 
}.

Definition generated_input_5 := (prod bool (prod nat (prod bool (prod nat bool)))).

Scheme Induction for handwritten_input_5 Sort Set.
Scheme Induction for handwritten_input_5 Sort Prop.
Scheme Induction for handwritten_input_5 Sort Type.

Find ornament handwritten_input_5 generated_input_5.

Definition generated_input_param_test (T1 T2 T3 : Type) := (prod T1 (prod T2 T3)).

Record handwritten_input_param_test (T1 T2 T3 : Type) := MkInputT
{
  firstT : T1;
  secondT : T2;
  thirdT : T3;
}.

Scheme Induction for handwritten_input_param_test Sort Set.
Scheme Induction for handwritten_input_param_test Sort Prop.
Scheme Induction for handwritten_input_param_test Sort Type.

(* The most basic test: When this works, should just give us fst *)
(* TODO set options to prove equiv: Set DEVOID search prove equivalence. Then get working. Then try w/ params. Then clean. Then do lift, same process.*)
Find ornament handwritten_input_param_test generated_input_param_test. (* TODO can omit once lift works *)
(*Fail Lift handwritten_input generated_input in firstBool as lifted_firstBool.*)

(* TODO test: failure cases, dependent parameters, eta expanded or not expanded variations, 2 fields, 4 fields, taking prod directly, etc *)
(* TODO check test results *)
(* TODO integrate into below *)

Definition generated_input_param_test2 (T1 T2 T3 T4 : Type) := (prod T1 (prod T2 (prod T3 T4))).

Record handwritten_input_param_test2 (T1 T2 T3 T4 : Type) := MkInputT2
{
  firstT' : T1;
  secondT' : T2;
  thirdT' : T3;
  fourthT' : T4;
}.

Scheme Induction for handwritten_input_param_test2 Sort Set.
Scheme Induction for handwritten_input_param_test2 Sort Prop.
Scheme Induction for handwritten_input_param_test2 Sort Type.

(* The most basic test: When this works, should just give us fst *)
(* TODO set options to prove equiv: Set DEVOID search prove equivalence. Then get working. Then try w/ params. Then clean. Then do lift, same process.*)
Find ornament handwritten_input_param_test2 generated_input_param_test2. (* TODO can omit once lift works *)
(*Fail Lift handwritten_input generated_input in firstBool as lifted_firstBool.*)

Record handwritten_input_param_test3 (T : Type) (t : T) (F : T -> Prop) := mkInput3
{
  firstT'' : F t;
  secondT'' : T;
  thirdT'' : exists t', t <> t' -> F t';
}.

Definition generated_input_param_test3 (T : Type) (t : T) (F : T -> Prop) :=
  (prod (F t) (prod T (exists t', t <> t' -> F t'))).


Scheme Induction for handwritten_input_param_test3 Sort Set.
Scheme Induction for handwritten_input_param_test3 Sort Prop.
Scheme Induction for handwritten_input_param_test3 Sort Type.

(* The most basic test: When this works, should just give us fst *)
(* TODO set options to prove equiv: Set DEVOID search prove equivalence. Then get working. Then try w/ params. Then clean. Then do lift, same process.*)
Find ornament handwritten_input_param_test3 generated_input_param_test3. (* TODO can omit once lift works *)
(*Fail Lift handwritten_input generated_input in firstBool as lifted_firstBool.*)

Lemma firstBool_spec (g : generated_input) :
  generated_firstBool g = firstBool (g2h_input g).
Proof.
  destruct g as [? [? ?]].
  compute.
  reflexivity.
Qed.

Lemma secondBool_spec (g : generated_input) :
  generated_secondBool g = secondBool (g2h_input g).
Proof.
  destruct g as [? [? ?]].
  compute.
  reflexivity.
Qed.

Lemma andBools_spec (g : generated_output) :
  generated_andBools g = andBools (g2h_output g).
Proof.
  destruct g. reflexivity.
Qed.

Lemma op_spec (g : generated_input) :
  generated_op g = h2g_output (handwritten_op (g2h_input g)).
Proof.
  destruct g as [[|] [? ?]]; reflexivity.
Qed.

Theorem generated_and_spec_true_true_via_handwritten
  (r : generated_input)
  (F : generated_firstBool  r = true)
  (S : generated_secondBool r = true)
  : generated_andBools (generated_op r) = true.
Proof.
  rewrite andBools_spec.
  rewrite op_spec.
  rewrite firstBool_spec  in F.
  rewrite secondBool_spec in S.
  rewrite h2g2h_output_spec.
  now apply handwritten_and_spec_true_true.
Qed.
