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

Set DEVOID search prove coherence. (* TODO test w/ other types too *)
Set DEVOID search prove equivalence. (* TODO test w/ other types too *)

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
 * To prove section and retraction, we need to show that equalities are
 * preserved in the inductive cases. For list this is simple:
 *)
Lemma eq_cons:
  forall {T : Type} (t : T) (l1 : list T) (l2 : list T),
    l1 = l2 ->
    cons t l1 = cons t l2.
Proof.
  intros. rewrite <- H. auto.
Qed.

Print eq_cons.

(* fun (T : Type) (t : T) (l1 l2 : list T) (H : l1 = l2) =>
     eq_ind (list T) l1 
       (fun (l3 : list T) => cons T t l1 = cons T t l3) 
       (eq_refl (list T) (cons T t l1)) l2 H

*)

(*
 * Luckily, we have a tool that can give us the version over vectors :)
 *)
Lift list vector in @eq_cons as eq_sigT_cons_p.
Definition eq_sigT_cons {T} t n1 v1 n2 v2 := (* partial unpack *)
  eq_sigT_cons_p T t (existT _ n1 v1) (existT _ n2 v2).

(*
 * With these lemmas, we get section and retraction very formulaically:
 *)
Theorem section:
  forall {T : Type} (l : list T),
    forget (promote l) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - apply eq_cons. apply IHl.
Qed.

Print section.

Theorem retraction:
  forall {T : Type} (v : sigT (fun n => vector T n)),
    promote (forget v) = v.
Proof.
  intros. induction v; induction p.
  - reflexivity.
  - apply eq_sigT_cons. apply IHp.
Qed.  


