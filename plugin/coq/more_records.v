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

(* --- Test a record with 4 fields --- *)

Module Handwritten4.

Record input := MkInput
{
  field1  : bool;
  field2    : nat;
  field3 : bool;
  field4 : nat; 
}.

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

End Handwritten4.

Module Generated4.

Definition input := (prod bool (prod nat (prod bool nat))).

End Generated4.

Find ornament Handwritten4.input Generated4.input as input4_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* --- Test a record with 5 fields --- *)

Module Handwritten5.

Record input := MkInput
{
  field1  : bool;
  field2    : nat;
  field3 : bool;
  field4 : nat;
  field5 : bool; 
}.

Scheme Induction for input Sort Set.
Scheme Induction for input Sort Prop.
Scheme Induction for input Sort Type.

End Handwritten5.

Module Generated5.

Definition input := (prod bool (prod nat (prod bool (prod nat bool)))).

End Generated5.

Find ornament Handwritten5.input Generated5.input as input5_curry.
(* TODO test lifting for above *)
(* TODO test output *)

(* --- Test a record with parameters --- *)

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
(*

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