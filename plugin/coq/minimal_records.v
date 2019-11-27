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
Find ornament handwritten_input generated_input. (* TODO can omit once lift works *)
(*Fail Lift handwritten_input generated_input in firstBool as lifted_firstBool.*)

Print handwritten_input_curry.

Lemma section:
  forall h,
    handwritten_input_curry_inv (handwritten_input_curry h) = h.
Proof.
  intros. induction h using handwritten_input_rect. reflexivity.
Qed.

Print section.

(* 
fun h : handwritten_input =>
handwritten_input_rect
  (fun h0 : handwritten_input =>
   @eq handwritten_input (handwritten_input_curry_inv (handwritten_input_curry h0))
     h0)
  (fun (firstBool0 : bool) (numberI0 : nat) (secondBool0 : bool) =>
   @eq_refl handwritten_input (MkInput firstBool0 numberI0 secondBool0)) h
     : forall h : handwritten_input,
       @eq handwritten_input
         (handwritten_input_curry_inv (handwritten_input_curry h)) h

fun h : handwritten_input =>
handwritten_input_rect 
   (fun h0 : handwritten_input => 
    @eq handwritten_input (handwritten_input_curry_inv (handwritten_input_curry h0))
      h0) 
   (fun (firstBool0 : bool) . (λ (numberI0 : nat) . (λ (secondBool0 : bool)  =>
     @eq_refl handwritten_input (MkInput firstBool0 numberI0 secondBool0)) h
*)

Lemma retraction:
  forall g,
    handwritten_input_curry (handwritten_input_curry_inv g) = g.
Proof.
  intros. induction g. induction b. reflexivity.
Qed.

Print retraction.

(*
fun g : prod bool (prod nat bool) =>
@prod_ind bool (prod nat bool)
  (fun g0 : prod bool (prod nat bool) =>
   @eq (prod bool (prod nat bool))
     (handwritten_input_curry (handwritten_input_curry_inv g0)) g0)
  (fun (a : bool) (b : prod nat bool) =>
   @prod_ind nat bool
     (fun b0 : prod nat bool =>
      @eq (prod bool (prod nat bool))
        (handwritten_input_curry
           (handwritten_input_curry_inv (@pair bool (prod nat bool) a b0)))
        (@pair bool (prod nat bool) a b0))
     (fun (a0 : nat) (b0 : bool) =>
      @eq_refl (prod bool (prod nat bool))
        (@pair bool (prod nat bool) a (@pair nat bool a0 b0))) b) g

fun g : prod bool (prod nat bool)) => 
@prod_rect bool (prod nat bool) 
  (fun g0 : prod bool (prod nat bool) => 
   @eq (prod bool (prod nat bool))
     (handwritten_input_curry (handwritten_input_curry_inv g0)) g0) 
  (fun (a : bool) (b : prod nat bool) => 
     @prod_rect nat bool 
       (fun b0 : prod nat bool => 
        @eq (prod bool (prod nat bool)) 
          (handwritten_input_curry
              (handwritten_input_curry_inv (@pair bool (prod nat bool) a b0))) 
          (@pair bool (prod nat bool) a b0)) 
      (fun (a0 : nat) (b0 : bool) => 
       @eq_refl (prod bool (prod nat bool)) 
         (@pair bool (prod nat bool) a (@pair nat bool a0 b0))))) (pair bool (prod nat bool) (_ [Rel 2]) (_ [Rel 1]))))) (_ [Rel 1])))


*)

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
