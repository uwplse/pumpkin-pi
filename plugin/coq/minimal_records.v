Require Import Ornamental.Ornaments.
Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)

(*
 * This is an example for lifting between nested tuples and records.
 *)

(*
 * In this example, we have some generated code that uses nested tuples:
 *)
Module Generated.

Definition generated_input := (prod bool (prod nat bool)).

Definition generated_output := (prod nat bool).

Definition generated_firstBool (r : (prod bool (prod nat bool))) : bool :=
  (fst r).

Definition generated_numberI (r : (prod bool (prod nat bool))) : nat :=
  (fst (snd r)).

Definition generated_secondBool (r : (prod bool (prod nat bool))) : bool :=
  (snd (snd r)).

Definition generated_numberO (r : (prod nat bool)) : nat :=
  (fst r).

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

End Generated.

(*
 * We want to write proofs over the record versions of these, which
 * are easier to read about. We start by defining the record versions
 * of generated_input and generated_output ourselves:
 *)
Module Handwritten.

Record handwritten_input := MkInput
{
  firstBool  : bool;
  numberI    : nat;
  secondBool : bool;
}.

Record handwritten_output := MkOutput
{
  numberO  : nat;
  andBools : bool;
}.

(*
 * To be able to lift back from these types, we'll need to
 * Preprocess this module, and to be able to do that, we'll need
 * to tell Coq to generate induction principles for these records:
 *)
Scheme Induction for handwritten_input Sort Set.
Scheme Induction for handwritten_input Sort Prop.
Scheme Induction for handwritten_input Sort Type.

Scheme Induction for handwritten_output Sort Set.
Scheme Induction for handwritten_output Sort Prop.
Scheme Induction for handwritten_output Sort Type.

End Handwritten.

(*
 * Now we Preprocess in both directions, since we'll lift in
 * both directions.
 *
 * Note we must tell Preprocess about any constants not in
 * our module, here fst and snd:
 *)
Preprocess Module Generated as Generated' {include fst, snd, andb}.
Preprocess Module Handwritten as Handwritten'.

(*
 * You can lift to handwritten_op all at once if you'd like, but you get prettier
 * (though equal) results if you lift the projections first, here for inputs:
 *)
Lift Generated'.generated_input Handwritten'.handwritten_input in Generated'.generated_firstBool as firstBool.
Lift Generated'.generated_input Handwritten'.handwritten_input in Generated'.generated_numberI as numberI.
Lift Generated'.generated_input Handwritten'.handwritten_input in Generated'.generated_secondBool as secondBool.
(*
 * then for outputs:
 *)
Lift Generated'.generated_output Handwritten'.handwritten_output in Generated'.generated_numberO as numberO.
Lift Generated'.generated_output Handwritten'.handwritten_output in Generated'.generated_andBools as andBools.

(*
 * Now lifting to handwritten_op uses the cached results:
 *)
Lift Generated'.generated_input Handwritten'.handwritten_input in Generated'.generated_op as handwritten_op_1.
Lift Generated'.generated_output Handwritten'.handwritten_output in handwritten_op_1 as handwritten_op {opaque firstBool numberI secondBool}.
(*
 * Note that to get prettier results here, we told to treat certain constants as opaque.
 * Otherwise, it would have opportunistically lifted everything.
 * You can also use this to speed up lifting.
 * Use this feature at your own risk (DEVOID might fail to lift if you use it badly).
 *)

(*
 * OK, now that we're in the handwritten world, we can write our proofs over
 * these nicer types:
 *)
Module HandwrittenProofs.

Theorem handwritten_and_spec_true_true
  (r : Handwritten'.handwritten_input)
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

End HandwrittenProofs.

(*
 * Let's Preprocess this proof for lifting:
 *)
Preprocess Module HandwrittenProofs as HandwrittenProofs' {include andb_true_intro}.

Print HandwrittenProofs'.handwritten_and_spec_true_true.

(*
 * Then lift it back to our nested pair types.
 * I think this is order sensitive if we want something that looks nice, since we
 * lifted generated_op in one order so we only have nice cached intermediate constants if we go
 * in the opposite order. But it will work regardless of which direction you do.
 *)
Lift Handwritten'.handwritten_output Generated'.generated_output in HandwrittenProofs'.handwritten_and_spec_true_true as generated_and_spec_true_true_1 {opaque firstBool numberI secondBool}.
Lift Handwritten'.handwritten_input Generated'.generated_input in generated_and_spec_true_true_1 as generated_and_spec_true_true' {opaque prod_rect}.

(*
 * Now we get our proof over generated types with just one catch: We need to call
 * induction first, since we have something defined over Preprocessed types
 * (induction principles) and we want something defined over the original types
 * (pattern matching and so on).
 *)
Theorem generated_and_spec_true_true
  (r : Generated.generated_input)
  (F : Generated.generated_firstBool  r = true)
  (S : Generated.generated_secondBool r = true)
  : Generated.generated_andBools (Generated.generated_op r) = true.
Proof.
  induction r. (* <-- NOTE: You will need this because you used Preprocess *)
  apply generated_and_spec_true_true'; auto.
Qed.

(* We are done! *)
