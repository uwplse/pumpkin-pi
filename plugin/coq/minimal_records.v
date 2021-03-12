Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)
Set Nonrecursive Elimination Schemes. (* <--- Preprocess needs induction principles for records *)

(*
 * This is an example for lifting between nested tuples and records.
 *)

(*
 * In this example, we have some generated code that uses nested tuples:
 *)
Module Generated.

Definition input := (prod bool (prod nat bool)).

Definition output := (prod nat bool).

Definition firstBool (r : (prod bool (prod nat bool))) : bool :=
  (fst r).

Definition numberI (r : (prod bool (prod nat bool))) : nat :=
  (fst (snd r)).

Definition secondBool (r : (prod bool (prod nat bool))) : bool :=
  (snd (snd r)).

Definition numberO (r : (prod nat bool)) : nat :=
  (fst r).

Definition andBools (r : (prod nat bool)) : bool :=
  (snd r).

Definition op (r : (prod bool (prod nat bool))) : (prod nat bool) :=
  (pair
    (numberI r)
    (andb
      (firstBool  r)
      (secondBool r)
    )
  ).

End Generated.

(*
 * We want to write proofs over the record versions of these, which
 * are easier to read about. We start by defining the record versions
 * of input and output ourselves:
 *)
Module Handwritten.

Record input := MkInput
{
  firstBool  : bool;
  numberI    : nat;
  secondBool : bool;
}.

Record output := MkOutput
{
  numberO  : nat;
  andBools : bool;
}.

End Handwritten.

(*
 * Now we Preprocess in both directions, since we'll lift in
 * both directions.
 *)
Preprocess Module Generated as Generated'.
Preprocess Module Handwritten as Handwritten'.

(*
 * The easiest way to lift these is to just lift the module twice, first for
 * input (bigger type) then for output (smaller type):
 *)
Lift Module Generated'.input Handwritten'.input in Generated' as Temp1.
Lift Module Generated'.output Handwritten'.output in Temp1 as Handwritten''.

(*
 * If you lift in the opposite order, for op, you get something well-typed but with
 * a type you don't even want. So for now when one type definition you lift along
 * is a subterm of another type definition you lift along, you will need to start
 * with the bigger one and then tell DEVOID to treat the lifted projections as opaque.
 * Really interesting WIP on handling this better without so much work for the user.
 *
 * See: https://taliasplse.wordpress.com/2020/02/02/automating-transport-with-univalent-e-graphs/
 *)

(*
 * OK, now that we're in the handwritten world, we can write our proofs over
 * these nicer types:
 *)
Module HandwrittenProofs.

Theorem and_spec_true_true
  (r : Handwritten'.input)
  (F : Handwritten''.firstBool  r = true)
  (S : Handwritten''.secondBool r = true)
  : Handwritten''.andBools (Handwritten''.op r) = true.
Proof.
  destruct r as [f n s].
  unfold Handwritten''.op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.

End HandwrittenProofs.

(*
 * Let's Preprocess this proof for lifting:
 *)
Preprocess Module HandwrittenProofs as HandwrittenProofs'.

(*
 * Then lift it back to our nested pair types.
 * I think this is order sensitive if we want something that looks nice, since we
 * lifted op in one order so we only have nice cached intermediate constants if we go
 * in the opposite order. But it will work regardless of which direction you do.
 *)
Lift Handwritten'.output Generated'.output in HandwrittenProofs'.and_spec_true_true as and_spec_true_true_1.
Repair Handwritten'.input Generated'.input in and_spec_true_true_1 as and_spec_true_true'.

(*
 * Tweaking those tactics, we can get back the original proof even forgetting about
 * Preprocessing.
 *)
Theorem and_spec_true_true
  (r : Generated.input)
  (F : Generated.firstBool  r = true)
  (S : Generated.secondBool r = true)
  : Generated.andBools (Generated.op r) = true.
Proof.
  induction r.
  apply (andb_true_intro (conj F S)).
Qed.

(* We are done! *)

(*
 * This is fully automatic, save for tweaking the tactics.
 * What do we get if we try to do this manually?
 * Let's start with the old proof.
 * The time is 10:29, end time is 10:31. So comparable effort,
 * since we need to tweak the tactics a bit, and the proof is really easy.
 *)
Theorem and_spec_true_true_manual
  (r : Generated.input)
  (F : Generated.firstBool  r = true)
  (S : Generated.secondBool r = true)
  : Generated.andBools (Generated.op r) = true.
Proof.
  destruct r as [n b].
  unfold Generated.op.
  simpl in *.
  apply andb_true_intro.
  intuition.
Qed.
(*
 * All we change is the first line to get rid of the warning.
 *)
