(*
 * Basic lifting tests for unpack, building on TestLift.v
 *)

Add LoadPath "coq".
Require Import Vector.
Require Import List.
Require Import Test.
Require Import TestLift.
Require Import Ornamental.Ornaments.
Require Import Infrastructure.

Set DEVOID lift type.

Definition packed_list_rect := Test.orn_list_vector_rect.
Definition length {T} l := orn_list_vector_index T l.
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

Definition nilV' (A : Type) := Test.nilV A.

Lift vector packed in nilV' as nilpv'.
Lift vector list in nilpv' as nilp'.

Theorem testNilV:
  forall A, nilp' A = nilp A.
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

Definition consV' (T : Type) (n : nat) (t : T) (v : vector T n) := Test.consV T n t v.

Lift vector packed in consV' as conspv'.
Fail Lift vector list in conspv' as consp'. (* <-- not done yet *)

(* when we finish the other direction, this should work by reflexivity: *)
Theorem testConspv':
  forall T n t l,
    conspv' T n t l = conspv T n t l.
Proof.
  intros. Fail reflexivity.
Abort.

(* for now, lifting works, but does not preserve definitional equalities when lifting back: *)
Theorem testConspv_temp':
  forall T n t l,
    conspv' T n t l = conspv T n t l.
Proof.
  intros. unfold conspv', conspv. simpl.
  induction l. induction x.
  simpl in *. subst. reflexivity.
Qed.

(* this gives us trouble when trying to lift back to lists, so we will revisit this soon. *)

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
