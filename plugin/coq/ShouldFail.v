Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Bellow are other kinds of changes I have tried that are not
 * yet supported.
 *)

(* --- Balanced binary trees --- *)

Inductive bal_bintree (A : Type) : nat -> Type :=
| bal_leaf :
    bal_bintree A 0
| bal_node :
    forall (n : nat),
      bal_bintree A n -> A -> bal_bintree A n -> bal_bintree A (n + n).

(*
 * This technically works for indexing,
 * but has an extra condition we don't find yet:
 *
 * Find ornament bintree bal_bintree as bintree_balancer.
 *
 * Print bintree_balancer_index.
 *
 * That is, we can find an indexing function, but note that to use it
 * (and to port bintrees to bal_bintrees anyways) we need a balanced
 * premise. We should be able to also infer the balanced premise automatically,
 * but it's tricky to know when we actually need to do this.
 * It seems like when the same index is referenced by several of the
 * other bintrees. We should revisit this at some point.
 *)

(* --- Nat and fin --- *)

(*
 * Not sure if possible, but might as well try.
 *
 * This doesn't work, though it's technically possible because (n : nat)
 * is our original type. I think we should consider this separately from
 * standard indexing though.
 *
 * See git history prior to 2/14 for some attempts at this that might
 * be useful for later on.
 *
 * Inductive fin : nat -> Type :=
 * | F1 : forall (n : nat), fin (S n)
 * | FS : forall (n : nat), fin n -> fin (S n).
 *
 * Find ornament nat fin as orn_nat_fin.
 *
 * Definition nat_fin_index (n : nat) :=
 *  nat_ind
 *  (fun (n : nat) => nat)
 *  (S O)
 *  (fun (n : nat) (IH : nat) => S IH)
 *  n.
 *)

(* --- Vectors using multiple nats --- *)

(*
 * If we add another nat to this hypothesis, then we have something incompletely
 * determined, because we need an extra nat in each case.
 *)

Inductive vector3 (A : Type) : nat -> Type :=
| nilV3 : vector3 A 0
| consV3 : forall (n m : nat), A -> vector3 A n -> vector3 A (n + m).

(*
 * This will fail (as it should, for now, though with a better error):
 *
 * Find ornament list vector3 as orn_list_vector3.
 *
 * Print orn_list_vector3_index.
 *)

Inductive vector4 (A : Type) : nat -> Type :=
| nilV4 : vector4 A 0
| consV4 : forall (n m : nat), A -> vector4 A (n + m) -> vector4 A n.

(*
 * This will fail (as it should, for now, though with a better error):
 *
 * Find ornament list vector4 as orn_list_vector4.
 *
 * Print orn_list_vector4_index.
 *)

(* --- Index is computed from a hypothesis with a different type --- *)

Require Import ZArith.

Inductive vector_int (A : Type) : Z -> Type :=
| nilV_int : vector_int A (Z.of_nat 0)
| consV_int :
    forall (n : nat),
       A -> vector_int A (Z.of_nat n) -> vector_int A (Z.of_nat (S n)).

Require Import Test.

Theorem vector_int_index:
  forall (A : Type) (n : nat),
     vector A n ->
     Z.
Proof.
  intros. induction X.
  - apply (Z.of_nat 0).
  - apply Z.of_nat. apply (S n).
Qed.

(*
 * This fails:
 * Find ornament list vector_int as orn_list_vectorint.
 *
 * For this to pass, we really need to chain it with PUMPKIN, because what
 * is happening is we first need to find the patch that gets us from list
 * to vector, and then we need to get from that indexing function
 * to Z by searching for a patch. This is really cool.
 *
 * An alternative approach is to get the function that gets us back from
 * Z to nat, so that we can make use of the inductive hypothesis.
 * But that is much less clear to me.
 *)

(* --- Index must be eliminated --- *)

Inductive bintree_weird (A : Type) : nat -> Type :=
| leafW :
    bintree_weird A 0
| nodeW :
    forall (n m : nat),
      bintree_weird A n -> A -> bintree_weird A (n + m) -> bintree_weird A n.

(*
 * This fails:
 * Find ornament bintree bintree_weird as orn_bintree_bintreeweird.
 *
 * Basically, we can't figure out the conclusion from the hypotheses
 * since there's no way to eliminate (n + m) automatically.
 *)
