(*
 * Basic lifting tests for unpack, building on TestLift.v
 *)

Require Import Vector.
Require Import List.
Require Import Foo.Test.
Require Import Foo.TestLift.
Require Import Ornamental.Ornaments.
Require Import Foo.Infrastructure.

Set DEVOID lift type.

Definition packed_list_rect := Test.orn_list_vector_rect.
Definition length {T} l := list_to_vector_index T l.
Definition packed T n := { s : sigT (vector T) & projT1 s = n}.

(* --- Simple constructor tests ---- *)

Program Definition nilp (T : Type):
  { l : list T & length l = 0 }.
Proof.
  exists (nil' T). (* lists *)
  reflexivity. (* lengths *)
Defined.

Lift list vector in nilp as nilpv.
Lift packed vector in nilpv as nilV.

Theorem testNil:
  nilV = Test.nilV.
Proof.
  reflexivity.
Qed.

(* Uncached *)
Definition nilV' (A : Type) := Test.nilV A.

Lift vector packed in nilV' as nilpv'.
Lift vector list in nilpv' as nilp'.

Theorem testNilV:
  forall A, nilp' A = nilp A.
Proof.
  intros. reflexivity.
Qed.

(* Cached *)
Lift vector packed in nilV as nilpv''.
Lift vector list in nilpv'' as nilp''.

Theorem testNilV_cached:
  forall A, nilp'' A = nilp A.
Proof.
  intros. reflexivity.
Qed.

Program Definition consp (T : Type) (n : nat) (t : T):
  { l : list T & length l = n} ->
  { l : list T & length l = S n }.
Proof.
  intros. apply packed_list_rect with (P := fun (_ : { l : list T & length l = n }) => { l : list T & length l = S n}).
  - intros. exists (cons t a). (* lists *)
    simpl. rewrite <- H. reflexivity. (* lengths *)
  - apply X.
Defined.

Lift list vector in consp as conspv.
Lift packed vector in conspv as consV.

Theorem testCons:
  consV = Test.consV.
Proof.
  reflexivity.
Qed.

(*
 * Uncached.
 * This fails because Algebraic is not smart enough to understand that it should
 * lift (eq_refl (S n) : projT1 (existT _ ....) = S n), since not all applications
 * of eq_refl should be lifted that way. So going in this direction is not
 * decidable in general. We may be able to implement some heuristics to understand
 * when eq_refl actually refers to equalities of projections that include rewrites,
 * but this goes against the original contract for when it's OK to call Algebraic.
 * So it is probably better to go along a different equivalence.
 *)

Definition consV' (T : Type) (n : nat) (t : T) (v : vector T n) :=
  Test.consV T n t v.

Lift vector packed in consV' as conspv'.
Fail Lift vector list in conspv' as cons'.

(*
 * Note that for uncached, this doesn't mean all is lost. 
 * We can still lift the left projection without issue:
 *)
Definition conspv_index T n t v := projT1 (conspv' T n t v).
Lift vector list in conspv_index as cons_index'.

(*
 * Just without more heuristics (which I can implement at some point), it can't
 * figure out to lift the equality proof in the second projection:
 *)
Definition conspv_value T n t v := projT2 (conspv' T n t v).
Fail Lift vector list in conspv_value as cons_value'.

(*
 * So if we want packed cons over lists, we can get it, just for now we need
 * to provide the equality proof still:
 *)
Lemma cons_value' T n t pl :
  length (cons_index' T n t pl) = S n.
Proof.
  simpl. unfold length. rewrite (projT2 pl). reflexivity.
Defined.
(*
 * This is exactly what it couldn't lift (eq_refl n) to automatically:
 *)
Print cons_value'.

(*
 * With that we glue it together:
 *)
Definition consp' T n t pl : {l : list T & length l = S n} :=
  existT _ (cons_index' T n t pl) (cons_value' T n t pl).

(* We used a different length proof so these are not refl,
   but still work: *)
Lemma consp_consp':
  forall T n t pl,
    consp T n t pl = consp' T n t pl.
Proof.
  intros. unfold consp, consp'. unfold cons_index', cons_value', packed_list_rect.
  unfold orn_list_vector_rect. simpl. unfold packed_rect. simpl.
  unfold eq_ind_r. f_equal. unfold id. simpl.
  induction pl. rewrite <- p. auto.
Qed.

(*
 * With caching, we don't have to worry about the eq_refl proof, since it remembers
 * what that proof corresponded to:
 *)
Lift vector packed in consV as conspv''.
Lift vector list in conspv'' as cons''.

(* --- Once the above works in both directions, I'll add the rest of the tests --- *)

(*
 * For now, a few more basic tests (note below doesn't work with consV instead of Test.consV):
 *)

Definition packed_cons (T : Type) (n : nat) (v : vector T n) (t : T) :=
  existT _ (S n) (Test.consV T n t v).
Lift vector packed in packed_cons as packed_cons'.

Definition packed_nil (T : Type) := existT _ 0 (Test.nilV T).
Lift vector packed in packed_nil as packed_nil'.

Print packed_nil'.
Print packed_cons'.
