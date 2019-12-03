Require Import Ornamental.Ornaments.

Definition generated_input := (prod bool (prod nat bool)).

Module Handwritten.

Record handwritten_input := MkInput
{
  firstBool  : bool;
  numberI    : nat;
  secondBool : bool;
}.

Scheme Induction for handwritten_input Sort Set.
Scheme Induction for handwritten_input Sort Prop.
Scheme Induction for handwritten_input Sort Type.

Record handwritten_output := MkOutput
{
  numberO  : nat;
  andBools : bool;
}.

Scheme Induction for handwritten_output Sort Set.
Scheme Induction for handwritten_output Sort Prop.
Scheme Induction for handwritten_output Sort Type.

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

End Handwritten.

Preprocess Module Handwritten as Handwritten'.

Definition generated_output := (prod nat bool).

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

(* The most basic test: When this works, should just give us pair *)
Set DEVOID search prove equivalence.
Find ornament Handwritten'.handwritten_input generated_input.
Definition mkInput_to_lift b1 n b2 := Handwritten'.MkInput b1 n b2.
Lift Handwritten'.handwritten_input generated_input in mkInput_to_lift as lifted_mkInput.

Print lifted_mkInput.

Lift generated_input Handwritten'.handwritten_input in lifted_mkInput as lifted_lifted_mkInput.

Print lifted_lifted_mkInput.

Lift Handwritten'.handwritten_input generated_input in Handwritten'.firstBool as lifted_firstBool.
(* TODO do elsewhere for test b.c. breaks caching:
Print lifted_firstBool.
Lift generated_input Handwritten'.handwritten_input in lifted_firstBool as lifted_lifted_firstBool.*)

(* TODO lift type too before defining term so we get back better type sig. always when lifting *)

Lift Handwritten'.handwritten_input generated_input in Handwritten'.numberI as lifted_numberI.
Print lifted_numberI.
(* TODO do elsewhere for test b.c. breaks caching:
Lift generated_input Handwritten'.handwritten_input in lifted_numberI as lifted_lifted_numberI.
Print lifted_lifted_numberI.*)

Lift Handwritten'.handwritten_input generated_input in Handwritten'.secondBool as lifted_secondBool.
Print lifted_secondBool.
(* TODO do elsewhere for test b.c. breaks caching:
Lift generated_input Handwritten'.handwritten_input in lifted_secondBool as lifted_lifted_secondBool.
Print lifted_lifted_secondBool.*)

Find ornament Handwritten'.handwritten_output generated_output.

(* TODO why not found otherwise? *)
Definition mkOutput_to_lift n b := Handwritten'.MkOutput n b.
Lift Handwritten'.handwritten_output generated_output in mkOutput_to_lift as lifted_MkOutput'.

Lift Handwritten'.handwritten_output generated_output in Handwritten'.numberO as lifted_numberO.
Lift Handwritten'.handwritten_output generated_output in Handwritten'.andBools as lifted_andBools.

(* TODO test equality *)

Print Handwritten'.handwritten_op.
Print generated_op.

(* TODO!!! Breaks if you have lifted lifted_numberI and so on, b.c. of caching. Bad! Fix caching! *)
Lift Handwritten'.handwritten_input generated_input in Handwritten'.handwritten_op as generated_op'.
Lift Handwritten'.handwritten_output generated_output in generated_op' as generated_op''.

(* TODO!! does opposite order work? why not if it breaks still? *)

Print Handwritten'.handwritten_and_spec_true_true.
Lift Handwritten'.handwritten_input generated_input in Handwritten'.handwritten_and_spec_true_true as handwritten_and_spec_true_true'.


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
(* TODO lift tests for all of the other things here w/ params *)

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
