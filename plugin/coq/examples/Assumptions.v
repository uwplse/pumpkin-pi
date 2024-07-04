(*
 * This file explains the assumptions from Section 3 in more detail,
 * and demonstrates some failing examples.
 *
 * These assumptions are not core to the type theory or to the
 * original definition of algebraic ornaments. Accordingly, this 
 * file can be viewed as a suite of test cases we'd eventually 
 * like to pass.
 *
 * See issue #37 for the status of lifting restrictions that Search makes.
 *)

Require Import Ornamental.Ornaments.
Require Import List ZArith Nat.
Require Import Search.

Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.

(*
 * Our arguments to cons are swapped from Coq's in the paper
 *)
Definition vect_rect {T : Type} p f_nil f_cons (n : nat) (v : vector T n) :=
  Vector.t_rect T p
    f_nil
    (fun (t : T) (n : nat) (v : vector T n) (IH : p n v) =>
      f_cons n t v IH)
    n
    v.

(* --- Same number of constructors --- *)

(*
 * We require that B has the same number of constructors as A. 
 * We cannot, for example, find this ornament:
 *)

Inductive vector3 (T : Type) : nat -> Type :=
| nilV3 : vector3 T 0
| consV30 : T -> vector3 T 1
| consV3S : forall (n : nat), T -> vector3 T (S n) -> vector3 T (S (S n)).

Fail Find ornament list vector3 as ltv3.

(*
 * This is not fundamental to the original definition of ornaments.
 * The definition of "same inductive structure" can in fact capture types
 * with different numbers of constructors. 
 *
 * This example isn't minimal; there are other reasons we can't support it yet.
 * But the reason we don't support different numbers of constructors is that
 * it requires search to understand that both consV30 and consV3S corespond to
 * the cons case of a list. That is, that we can combine them to get consV.
 *
 * This is absolutely possible, it is just not done yet.
 *)

(* --- Same order of constructors --- *)

(*
 * We require that B has constructors in the same order as A.
 * We cannot, for example, find this ornament:
 *)

Inductive vector_flip (T : Type) : nat -> Type :=
| consVflip : forall (n : nat), T -> vector_flip T n -> vector_flip T (S n)
| nilVflip : vector_flip T 0.

Fail Find ornament list vector_flip as ltv_flip.

(*
 * This is not fundamental to the original definition of ornaments.
 * vector and vector_flip are very obviously equivalent.
 *
 * The reason we don't support a different order of constructors is that
 * it requires search to understand that nil maps to nilVflip and
 * cons maps to consVflip. We simplify search a lot by just assuming
 * the 0th constructor maps to the 0th constructor, and so on. But here
 * we need to construct a map between constructors first. This is
 * not straightforward.
 *)

(* --- No recursive references under products --- *)

(*
 * We don't allow for recursive references under products:
 *)

Inductive T1 (T : Type) : Type :=  
| t1 : (T -> T1 T) -> T1 T.

Inductive T2 (T : Type) : nat -> Type :=
| t2 : (T -> T2 T 0) -> T2 T 0.

Fail Find ornament T1 T2 as T1_to_T2.

(*
 * I am not sure what supporting these would mean, or whether these should be 
 * supported. What is the relationship between T1 and T2, exactly? Is this
 * an algebraic ornament? Does the original model the other papers constructed
 * allow for this kind of inductive type? I don't know the answer to these questions.
 * If you do, please chime in on issue #37.
 *)

(* --- One new hypothesis per recursive reference: Non-algebraic versions --- *)

(*
 * The error messages are bad for these; sorry about that.
 *
 * We require that for every recursive reference to A in A, there's exactly
 * one new hypothesis in B. Most ornaments you can define this way aren't
 * algebraic. For example, this one is not algebraic:
 *)

Inductive bintree (A : Type) : Type :=
| leaf :
    bintree A
| node :
    bintree A -> A -> bintree A -> bintree A.

Inductive bal_bintree (A : Type) : nat -> Type :=
| bal_leaf :
    bal_bintree A 0
| bal_node :
    forall (n : nat),
      bal_bintree A n -> A -> bal_bintree A n -> bal_bintree A (n + n).

Fail Find ornament bintree bal_bintree as orn_bintree_balbintree.

(*
 * It has a hidden premise! You can only go from a bintree to a bal_bintree 
 * if the bintree is balanced.
 *
 * If we add an extra hypothesis, then we may have something not algebraic, too:
 *)

Inductive vector2 (A : Type) : nat -> Type :=
| nilV2 : vector2 A 0
| consV2 : forall (n m : nat), A -> vector2 A n -> vector2 A (n + m).

Fail Find ornament list vector2 as list_to_vector2.

(*
 * This is not algebraic because we need to inhabit m.
 *
 * Everyone loves the fin example:
 *)

Inductive fin : nat -> Type :=
| F1 : forall (n : nat), fin (S n)
| FS : forall (n : nat), fin n -> fin (S n).

Fail Find ornament nat fin as orn_nat_fin.

(*
 * But I don't think this is algebraic. It's an ornament, but there are infinitely
 * many fins for every nat.
 *)

(* --- One new hypothesis per recursive reference: Algebraic version --- *)

(*
 * If we are being deliberately silly:
 *)

Inductive vector4 (A : Type) : nat -> Type :=
| nilV4 : vector4 A 0
| consV4 : forall (n : nat), unit -> A -> vector4 A n -> vector4 A (S n).

Fail Find ornament list vector4 as orn_list_vector4.

(*
 * Then we can actually define an algebraic ornament that we can't find because it
 * has an extra hypothesis. This ornament is algebraic because vector4 is obviously
 * equivalent to vector, since we can inhabit unit with tt and only with tt.
 *
 * This is an interesting problem for search! But I think it should also be
 * undecidable, because it necessarily must determine whether the new hypothesis type
 * (here unit) is inhabitable. So, an idea for supporting this part is to get extra
 * user input on what to do about that extra type. Or, search can attempt to solve
 * this obligation in obvious cases.
 *
 * After figuring out that unit is inhabitable, for this to be an equivalence,
 * we need that unit is uniquely inhabitable. For unit this is easy,
 * but I can imagine having some dependent type here instead that makes even
 * this part not easy.
 *
 * This is also really interesting to me, so feel free to chime into #37 with ideas.
 *)

(* --- No index hypothesis of different types --- *)

(*
 * In addition to having the same number of hypotheses, we require that the
 * indices have type IB. This simplifies search. Consider this example:
 *)

Inductive vector_int (A : Type) : Z -> Type :=
| nilV_int : vector_int A (Z.of_nat 0)
| consV_int :
    forall (n : nat),
       A -> vector_int A (Z.of_nat n) -> vector_int A (Z.of_nat (S n)).

Fail Find ornament list vector_int as orn_list_vectorint.

(*
 * This is equivalent to vector, so this is an algebraic ornament.
 * But a search procedure needs to figure out that Z.of_nat is the patch
 * that gets us from nat to Z first. And for some terms, this function
 * might be less obvious.
 *
 * The way to loosen this restriction a bit is to chain DEVOID with PUMPKIN PATCH.
 * Finding the relationship between vector and vector_int is very, very much
 * a PUMPKIN PATCH problem in the original style of PUMPKIN PATCH. I am very
 * excited to do this as part of my thesis work, and I was very excited when
 * I found this problem to begin with. But it's a hard problem.
 *)

(* --- New hypotheses must be exactly the new index of the recursive references --- *)

(* 
 * We actually had some support for some types for which this wans't true in
 * the past. But it led to some difficulties, so it's just in our GitHub history
 * for now. Here is a case that we never figured out:
 *)

Inductive bintree_weird (A : Type) : nat -> Type :=
| leafW :
    bintree_weird A 0
| nodeW :
    forall (n m : nat),
      bintree_weird A n -> A -> bintree_weird A (n + m - n) -> bintree_weird A (n + m).

Fail Find ornament bintree bintree_weird as orn_bintree_bintree_weird.

(*
 * This is exactly the same as our bintreeV type we can support, so it's an 
 * algebraic ornament. But search doesn't know how to get (n + m) from n 
 * and (n + m - n). And when it's looking for the indexer, it doens't have
 * the hypotheses n and m directly; it must make use of the indices n
 * and (n + m - n). This should be undecidable in general.
 *
 * Some cases should be easy, though:
 *)

Inductive bintree_weird2 (A : Type) : nat -> Type :=
| leafW2 :
    bintree_weird2 A 0
| nodeW2 :
    forall (n m : nat),
      bintree_weird2 A n -> A -> bintree_weird2 A ((0 + 0) + m) -> bintree_weird2 A (n + m).

Fail Find ornament bintree bintree_weird2 as orn_bintree_bintree_weird2.

(*
 * In this case, we should just be able to reduce ((0 + 0) + m) to m. So, at the
 * very least, we can easily loosen "exactly" to "definitionally equal to."
 * But we don't do this yet. If it's useful, we will.
 *)

(* --- Input term is well-typed --- *)

(*
 * Well, you can't define an ill-typed term in Coq, but if you could,
 * we wouldn't provide any guarantees about lifting it.
 *)

(* --- Input term is fully η-expanded --- *)

(*
 * We actually lift this restriction. Consider:
 *)
Lift list vector in @cons as consV.

(*
 * It was just easier to assume it for presenting the algorithm.
 * Basically you should either fully expand your term ahead of time when
 * running through the algorithm, or the algorithm should do it as it goes.
 * We implement lazy η-expansion.
 *)

(* --- Input term does not apply promote or forget --- *)

(*
 * We can lift some of these terms without failing, but we don't recursively
 * preserve the equivalence. So there aren't any real guarantees. Consider:
 *)

Definition promote_again (T : Type) (l : list T) :=
  ltv T l.

Lift list vector in promote_again as id_sigT_vect.
Check id_sigT_vect.

(*
 * This might be fine, honestly, but it's harder to reason about.
 *)

(* --- Input term does not reference the new type --- *)

(*
 * Along the same lines, I'm not sure what it means to lift this,
 * even though it works:
 *)

Definition unsure (T : Type) (l : list T) (v : sigT (vector T)) :=
  l.

Lift list vector in unsure as unsure_v.
Check unsure_v.

(*
 * I think this is actually OK, too. I think it still preserves the
 * equivalence this way. But, I didn't think much about these terms,
 * and I didn't want to make any claims in the paper that weren't true,
 * so I just was honest about not thinking about them.
 *)

(* --- Index is not the original type (no refinement) --- *)

(*
 * We don't yet support refinements:
 *)

Inductive nat_nat : nat -> Set :=
| OO : nat_nat 0
| SS : forall (n : nat), nat_nat n -> nat_nat (S n).

(*
 * Search can actually handle this fine:
 *)

Find ornament nat nat_nat as nat_to_nat_nat.

(*
 * The difficult comes from lifting. Some liftings work:
 *)
Lift nat nat_nat in 0 as OO_p.
Lift nat nat_nat in (fun (n : nat) => n) as id_nat_nat.

(*
 * But some do not (because of some kind of compiler bug, I can't demonstrate this infinite loop
 * since it will actually loop infinitely and not trigger the timeout, thanks to some incorrect compiler
 * optimization):
 *)
(*Fail Timeout 5 Lift nat nat_nat in S as SS_p.*)

(*
 * This is because the lifting algorithm is not yet smart enough to stop
 * recursing in some cases. For example, LIFT-CONSTR recurses after calling
 * the intermediate rule. It will this keep recursively lifting S.
 *
 * Supporting this is tricky, but should be possible. It took more than a few days
 * of trying, though, so we deferred it to later. We're primarily interested
 * in changes in types when the old type is no longer available, or deriving
 * new libraries from old libraries. But refinement types are a really
 * interesting use case for a tool like this. So we'd like to handle this one day.
 * See issue #41 for the status of this.
 *)

(* --- Extra restrictions for forgetful direction --- *)

(*
 * The forgetful direction currently doesn't let you forget terms defined
 * directly over vectors (see #42 for status here). You must pack them instead.
 *
 * There's a bug (see #58) that means you can't actually roundtrip right now
 * without reducing in the general case. I'm going to fix it for simple cases
 * right now, but I want #42 for the more general case.
 *)
