(*
 * Custom equivalences for ListToVect
 *)

Require Import Vector.
Require Import List.
Require Import ZArith.

Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence.

Notation vector := Vector.t.
Notation vnil := Vector.nil.
Notation vcons := Vector.cons.

(* --- Preprocess --- *)

Preprocess Module List as List' { opaque (* ignore these: *)
  RelationClasses
  Nat
  Coq.Init.Nat
}.

(* --- Length function --- *)

(*
 * We can set our indexer to instead be the list length function if we'd like.
 * First we find the original ornament:
 *)
Find ornament list vector.

(*
 * Then we modify it.
 *
 * For now, the algorithm makes some annoying assumptions about the form that the 
 * equivalence takes. In particular, if we apply (projT2 (list_to_t T l)), it's going
 * to try to recursively lift the argument l to (list_to_t T l), which is annoying.
 * Similarly, it sometimes unfolds things to match over lists and doesn't figure out
 * how to refold it when our equivalence is complex, which is technically correct,
 * except that later on recursive attempts match over lists and call pattern
 * matching rules which are unsupported, rather than using eliminators.
 * We should fix these bugs. They do not have to do with the theory, just the
 * implementation, in particular because of constants and efficiency.
 *
 * In the meantime, we print and substitute so these problems don't show up.
 *)

(* Print list_to_t. *) (* <--- Uncomment to see the old function *)

Definition ltv :=
fun (A : Type) (l : list A) =>
existT (fun H : nat => vector A H) (length l)
  (list_rect (fun l0 : list A => vector A (length l0)) 
     (vnil A)
     (fun (a : A) (l0 : list A)
        (H : (fun (_ : nat) (l1 : list A) => vector A (length l1))
               (length l0) l0) => vcons A a (length l0) H) l).

(*
 * The correctness condition is that these also form an equivalence with the same
 * coherence properties. We don't need to prove this, however. We can just tell
 * CARROT to use our equivalence. (Use at your own risk! If you pick something that isn't an equivalence,
 * lifting will fail with confusing type errors.)
 *)
Save ornament list vector { promote = ltv }.

(*
 * The cute thing is that we can now lift all of these using the length function:
 *)
Lift Module list vector in List' as Vector { opaque (* ignore these, just for speed *)
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
 * One nice thing about this is that we can lift these directly:
 *)
Definition packed_list T n := { l : list T & length l = n }.
Lift list vector in packed_list as packed_vector_proof.

(*
 * This gives us something still equivalent to a vector, and the proof
 * is much easier. This is the next equivalence we should compose with.
 * And when we see a vector, we should use this one directly. It should
 * always follow from the algebraic ornament. 
 *)
Program Definition unpack T n (s : packed_vector_proof T n) : vector T n.
Proof.
  induction s. induction x. rewrite <- p. apply p0.
Defined.

Program Definition pack T n (v : vector T n) : packed_vector_proof T n.
Proof.
  exists (existT _ n v). reflexivity.
Defined.

Lemma pack_section:
  forall T n s, pack T n (unpack T n s) = s.
Proof.
  intros T n s. induction s. induction x. rewrite <- p. simpl. reflexivity.
Defined.

Lemma pack_retraction:
  forall T n v, unpack T n (pack T n v) = v.
Proof.
  intros T n v. reflexivity.
Defined.

(*
 * In theory, we could define a nicer eliminator using packed_list, then.
 * And then do another eliminator transformation.
 * In practice, I haven't really found this to be any easier, but I'll keep trying.
 *)

