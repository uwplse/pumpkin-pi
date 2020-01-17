(*
 * Section 5 Preprocess Example
 *)

Require Import Vector.
Require Import List.

Require Import Ornamental.Ornaments.

Notation vector := Vector.t.

(* --- Preprocess --- *)

Preprocess Module List as List' { opaque (* ignore these: *)
  (* dependent elimination only: *)
  RelationClasses.StrictOrder_Transitive
  RelationClasses.StrictOrder_Irreflexive
  RelationClasses.Equivalence_Symmetric
  RelationClasses.Equivalence_Transitive
  RelationClasses.PER_Symmetric
  RelationClasses.PER_Transitive
  RelationClasses.Equivalence_Reflexive
  (* proofs about these match over the above opaque terms, and would fail: *)
  Nat.add
  Nat.sub
}.

(* --- Search & Lift --- *)

(* We use automatic search here rather than calling Find Ornament ourselves. *)

Lift Module list vector in List' as Vector'.

(*
 * There are still two proofs (`partition_length` and `elements_in_partition`)
 * that fail to lift above, due to implementation bugs.
 * See: https://github.com/uwplse/ornamental-search/issues/32
 *)
