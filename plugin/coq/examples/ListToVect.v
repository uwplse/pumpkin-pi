(*
 * Section 5 Preprocess Example
 *)

Require Import Vector.
Require Import List.
Require Import ZArith.

Require Import Ornamental.Ornaments.

Notation "( x ; y )" := (existT _ x y) (no associativity).
Notation "p .1" := (projT1 p) (left associativity, at level 8, format "p .1").
Notation "p .2" := (projT2 p) (left associativity, at level 8, format "p .2").
Notation "p .&" := (p.1; p.2) (left associativity, at level 6, format "p .&").

Notation vector := Vector.t.
Notation vnil := Vector.nil.
Notation vcons := Vector.cons.

(* --- Preprocess --- *)

Preprocess Module List as List' { opaque (* ignore these: *)
  RelationClasses
  Nat
  Coq.Init.Nat
}.

(* --- Search & Lift --- *)

(* We use automatic search here rather than calling Find Ornament ourselves. *)

Definition list_elim A P : P nil -> (forall x xs, P xs -> P (cons x xs)) -> forall xs, P xs :=
  fun H__nil H__cons xs => @list_rect A P H__nil H__cons xs.

Lift list vector in list_elim as vect_elim.

Check (vect_elim :
         forall (A : Type) (P : {n : nat & vector A n} -> Type),
           P (0; vnil A) ->
           (forall (x : A) (xs : {n : nat & vector A n}),
               P xs.& -> P (S xs.1; vcons A x xs.1 xs.2)) ->
           forall (xs : {n : nat & vector A n}),
             P xs.&).

Lift Module list vector in List' as Vector' { opaque (* ignore these, just for speed *)
  RelationClasses.Equivalence_Reflexive
  RelationClasses.reflexivity
  Nat.add
  Nat.sub
  Nat.lt_eq_cases
  Nat.compare_refl
  Nat.lt_irrefl
  Nat.le_refl
  Nat.bi_induction
  Nat.central_induction
}.

(*
 * There are still two proofs (`partition_length` and `elements_in_partition`)
 * that fail to lift above, due to implementation bugs.
 * See: https://github.com/uwplse/ornamental-search/issues/32
 *
 * The effort here is fully automatic, whereas the old tactics don't work for
 * the repaired proofs here, so there are obvious development time savings.
 *)
