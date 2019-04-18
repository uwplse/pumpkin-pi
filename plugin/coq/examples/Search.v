(*
 * Walkthrough of search for Section 4
 *)

Add LoadPath "coq/examples".
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

(* syntax to match paper *)
Notation vector := Vector.t.
Notation consV n t v := (Vector.cons _ t n v).
Notation nilV := Vector.nil.

(* --- Running search --- *)

Set DEVOID search prove coherence. (* TODO test w/ other types too [tree, dep] *)
Set DEVOID search prove equivalence. (* TODO test w/ other types too [tree, dep]; use in case study code *)

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
 * Coherence follows by construction:
 *)
Theorem coherence:
  forall {T : Type} (l : list T),
    indexer l = projT1 (promote l).
Proof.
  exact ltv_coh.
Qed.

(*
 * With these lemmas, we get section and retraction very formulaically:
 *)
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

