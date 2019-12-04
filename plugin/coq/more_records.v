(*
 * This file includes more about records, including
 * tests that the curry record functionality works correctly,
 * rather than the simple walkthrough from minimal_records.v.
 *)


(*
 * TODO everything below is for Talia: Later testing and so on.
 *)

(* TODO split below into different files; in above, show workflow that is reasonable *)
(* TODO roundtrip tests for above *)
(* TODO document all new functionality *)
(* TODO remove extra imports and functions that aren't used now *)

(*
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
(* TODO be better about the names you choose for the lifted types above *)

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
*)