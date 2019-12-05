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
