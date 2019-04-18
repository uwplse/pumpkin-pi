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

Print eq_sigT_cons_p.

(*

fun (T : Type) (t0 : T) (n1 : nat) (v1 : vector T n1) (n2 : nat) (v2 : vector T n2)
  (H : @eq (@sigT nat (fun H : nat => t T H)) 
           (@existT nat (fun H : nat => t T H) n1 v1)
           (@existT nat (fun H : nat => t T H) n2 v2) =>
@eq_ind 
  (@sigT nat (fun H0 : nat => t T H0))
  (@existT nat (fun H0 : nat => t T H0) n1 v1)
  (fun l3 : @sigT nat (fun H0 : nat => t T H0) =>
     @eq 
       (@sigT nat (fun H0 : nat => t T H0))
       (@existT nat 
          (fun H0 : nat => VectorDef.t T H0) 
          (S n1)
          (VectorDef.cons T t0 n1 v1))
       (@existT nat 
          (fun H0 : nat => VectorDef.t T H0) 
          (S (@projT1 nat (fun H0 : nat => t T H0) l3))
          (VectorDef.cons T t0 (@projT1 nat (fun H0 : nat => t T H0) l3) (@projT2 nat (fun H0 : nat => t T H0) l3))))
  (@eq_refl 
     (@sigT nat (fun H0 : nat => t T H0))
     (@existT nat 
        (fun H0 : nat => VectorDef.t T H0)
        (S n)
        (VectorDef.cons T t0 n1 v1)))
  (@existT nat (fun H0 : nat => t T H0) n2 v2) 
  H

fun (T : Type) (t0 : T) (n1 : nat) (v1 : vector T n1) (n2 : nat) (v2 : vector T n2) 
  (H : @eq (@sigT nat (fun H : nat => t T H)) 
           (@existT nat (fun H : nat => t T H) n1 v1)
           (@existT nat (fun H : nat => t T H) n2 v2)) => 
@eq_ind 
  (@sigT nat (fun H0 : nat => t T H0)) 
  (@existT nat (fun H0 : nat => t T H0) n1 v1) 
  (fun (l3 : @sigT nat (fun H0 : nat => t T H0) =>
    @eq  
      (t (A [Rel 8]) 
      (S (n [Rel 6]))) (cons (A [Rel 8]) (h [Rel 7]) (n [Rel 6]) (_ [Rel 5])) (cons (A [Rel 8]) (h [Rel 7]) (n [Rel 6]) (_ [Rel 5])))) (eq_refl (t (A [Rel 7]) (S (n [Rel 5]))) (cons (A [Rel 7]) (h [Rel 6]) (n [Rel 5]) (_ [Rel 4]))) (existT nat (λ (_ : nat) . (t (A [Rel 8]) (_ [Rel 1]))) (_ [Rel 3]) (_ [Rel 2])) (_ [Rel 1])))))))))

 *)

Theorem retraction:
  forall {T : Type} (v : sigT (fun n => vector T n)),
    promote (forget v) = v.
Proof.
  intros. induction v; induction p.
  - reflexivity.
  - apply eq_sigT_cons. apply IHp.
Qed.  

