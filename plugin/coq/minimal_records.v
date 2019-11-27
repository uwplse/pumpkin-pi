Require Import Ornamental.Ornaments.

Definition generated_input := (prod bool (prod nat bool)).

Record handwritten_input := MkInput
{
  firstBool  : bool;
  numberI    : nat;
  secondBool : bool;
}.

Definition generated_output := (prod nat bool).

Record handwritten_output := MkOutput
{
  numberO  : nat;
  andBools : bool;
}.

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
Fail Find ornament handwritten_input generated_input. (* TODO can omit once lift works *)
Fail Lift handwritten_input generated_input in firstBool as lifted_firstBool.

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
