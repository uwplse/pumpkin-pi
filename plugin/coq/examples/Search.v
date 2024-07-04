(*
 * Walkthrough of search for Section 4
 *)

Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

(* syntax to match paper *)
Notation vector := Vector.t.
Notation consV n t v := (Vector.cons _ t n v).
Notation nilV := Vector.nil.

(* --- Running search --- *)

Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.

Find ornament list vector as ltv.

(* --- Indexer ---*)

(*
 * Our generated indexer is ltv_index:
 *)
Print ltv_index.

(*
 * Let's call this the indexer:
 *)
Notation indexer l := (ltv_index _ l).

(*
 * Note that this computes the length:
 *)
Example indexer_is_length:
  forall {T : Type} (l : list T),
    indexer l = length l.
Proof.
  reflexivity.
Qed.

(* --- Promote --- *)

(*
 * Promote is ltv:
 *)
Print ltv.

(*
 * Let's call this promote:
 *)
Notation promote l := (ltv _ l).

(* --- Forget --- *)

(*
 * Forget is ltv_inv:
 *)
Print ltv_inv.

(*
 * Let's call this forget
 *)
Notation forget l := (ltv_inv _ l).

(* --- Correctness --- *)

(*
 * Since we set the "prove coherence" and "prove equivalence" options,
 * DEVOID generated coherence, section, and retraction proofs. Here I
 * simply restate them and show that the generated terms are correct.
 * These automatically generated proofs show that the components DEVOID
 * found form the ornamental promotion isomorphism between lists and vectors.
 *
 * Coherence follows by construction, while section and retraction each
 * follow by induction, where each case is a fold over rewrites by each
 * recursive argument, ending with reflexivity.
 *)

Theorem coherence:
  forall {T : Type} (l : list T),
    indexer l = projT1 (promote l).
Proof.
  exact ltv_coh.
Qed.

Theorem section:
  forall {T : Type} (l : list T),
    forget (promote l) = l.
Proof.
  exact ltv_section.
Qed.

Theorem retraction:
  forall {T : Type} (v : sigT (fun n => vector T n)),
    promote (forget v) = v.
Proof.
  exact ltv_retraction.
Qed.

Theorem adjunction:
  forall {T : Type} (l : list T),
    ltv_retraction_adjoint T (ltv T l) = f_equal (ltv T) (ltv_section T l).
Proof.
  exact ltv_adjunction.
Qed.
