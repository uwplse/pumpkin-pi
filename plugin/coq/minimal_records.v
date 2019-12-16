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
 * You can lift to op all at once if you'd like, but you get prettier
 * (though equal) results if you lift the projections first, here for inputs:
 *)
Lift Generated'.input Handwritten'.input in Generated'.firstBool as firstBool.
Lift Generated'.input Handwritten'.input in Generated'.numberI as numberI.
Lift Generated'.input Handwritten'.input in Generated'.secondBool as secondBool.
(*
 * then for outputs:
 *)
Lift Generated'.output Handwritten'.output in Generated'.numberO as numberO.
Lift Generated'.output Handwritten'.output in Generated'.andBools as andBools.

(*
 * Now lifting to op uses the cached results:
 *)
Lift Generated'.input Handwritten'.input in Generated'.op as op_1 { opaque Generated'.Coq_Init_Datatypes_andb }.
Lift Generated'.output Handwritten'.output in op_1 as op {opaque firstBool numberI secondBool}.
(*
 * Note that to get prettier results here, we told to treat certain constants as opaque.
 * (TODO why is opacity of andb not inferred and used automatically?)
 * Otherwise, it would have opportunistically lifted everything.
 * You can also use this to speed up lifting.
 * Use this feature at your own risk (DEVOID might fail to lift if you use it badly).
 *
 * For example, the above would actually not work (with the opaque notations kept in, but instantiated to Generated')
 * if you lift in the opposite order. If you lift in the opposite order without any
 * notations, you get something well-typed but utterly useless to look at, with
 * a type you don't even want. So for now when one type definition you lift along
 * is a subterm of another type definition you lift along, you will need to start
 * with the bigger one and then tell DEVOID to treat the lifted projections as opaque.
 * Really interesting WIP on handling this better without so much work for the user.
 *)

(*
 * OK, now that we're in the handwritten world, we can write our proofs over
 * these nicer types:
 *)
Module HandwrittenProofs.

Theorem and_spec_true_true
  (r : Handwritten'.input)
  (F : firstBool  r = true)
  (S : secondBool r = true)
  : andBools (op r) = true.
Proof.
  destruct r as [f n s].
  unfold op.
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
Lift Handwritten'.input Generated'.input in and_spec_true_true_1 as and_spec_true_true'.

(*
 * Now we get our proof over generated types with just one catch: We need to call
 * induction first, since we have something defined over Preprocessed types
 * (induction principles) and we want something defined over the original types
 * (pattern matching and so on).
 *)
Theorem and_spec_true_true
  (r : Generated.input)
  (F : Generated.firstBool  r = true)
  (S : Generated.secondBool r = true)
  : Generated.andBools (Generated.op r) = true.
Proof.
  induction r. (* <-- NOTE: You will need this because you used Preprocess *)
  apply and_spec_true_true'; auto.
Qed.

(* We are done! *)
