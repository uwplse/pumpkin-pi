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

(* --- not yet automated --- *)

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

(*
 * Luckily, we have a tool that can give us the version over vectors :)
 *)
Lift list vector in @eq_cons as eq_sigT_cons_p.
Definition eq_sigT_cons {T} t n1 v1 n2 v2 := (* partial unpack *)
  eq_sigT_cons_p T t (existT _ n1 v1) (existT _ n2 v2).

Theorem retraction:
  forall {T : Type} (v : sigT (fun n => vector T n)),
    promote (forget v) = v.
Proof.
  intros. symmetry. induction v; induction p.
  - reflexivity.
  - apply eq_sigT_cons. apply IHp.
Qed.  

Print retraction.

(*

fun (h : T) (n : nat) (p0 : VectorDef.t T n) (IHp : @eq (@sigT nat (fun H : nat => t T H)) (@existT nat (fun n0 : nat => t T n0) n p0)
                    (ltv T (ltv_inv T (@existT nat (fun n0 : nat => t T n0) n p0)))) =>
(Coq.Init.Logic.eq_ind (sigT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1])))) (existT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))) (n [Rel 3]) (t [Rel 2])) (λ (_ : (sigT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))))) . (eq (sigT nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1])))) (existT nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1]))) (S (n [Rel 4])) (cons (A [Rel 7]) (h [Rel 5]) (n [Rel 4]) (t [Rel 3]))) (existT nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1]))) (S (Coq.Init.Specif.projT1 nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1]))) (_ [Rel 1]))) (cons (A [Rel 7]) (h [Rel 5]) (Coq.Init.Specif.projT1 nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1]))) (_ [Rel 1])) (Coq.Init.Specif.projT2 nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1]))) (_ [Rel 1])))))) (eq_refl (sigT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1])))) (existT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))) (S (n [Rel 3])) (cons (A [Rel 6]) (h [Rel 4]) (n [Rel 3]) (t [Rel 2])))) (existT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))) (Coq.Init.Specif.projT1 nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))) (Search.ltv (A [Rel 6]) (Search.ltv_inv (A [Rel 6]) (existT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))) (n [Rel 3]) (t [Rel 2]))))) (Search.ltv (A [Rel 6]) (Search.ltv_inv (A [Rel 6]) (existT nat (λ (_ : nat) . (t (A [Rel 7]) (_ [Rel 1]))) (n [Rel 3]) (t [Rel 2]))))) (_ [Rel 1]))))))

 *)