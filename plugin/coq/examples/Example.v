(*
 * Section 2 Example
 *)

Add LoadPath "coq/examples".
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

From Coq Require Import ssreflect ssrbool ssrfun.

Import EqNotations.

(* syntax to match paper *)
Notation vector := Vector.t.
Notation consV n t v := (Vector.cons _ t n v).
Notation nilV := Vector.nil.

(*
 * Here is our library that we will lift.
 *)
Module hs_to_coq'.

(* From:
 * https://github.com/antalsz/hs-to-coq/blob/master/base/GHC/List.v
 *)
Definition zip {a} {b} : list a -> list b -> list (a * b)%type :=
  fix zip arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, _bs => nil
           | _as, nil => nil
           | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
  end.

(* From:
 * https://github.com/antalsz/hs-to-coq/blob/master/core-semantics-no-values/semantics.v
 *)
Fixpoint zip_with {A} {B} {C} (f : A -> B -> C) (s : list A) (t : list B) : list C :=
  match s , t with
    | a :: s' , b :: t' => f a b :: zip_with f s' t'
    | _       , _       => nil
  end.

Theorem zip_with_is_zip {A} {B} :
  zip_with (@pair A B) =2 zip.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

End hs_to_coq'.

(* --- Preprocess --- *)

Preprocess Module hs_to_coq' as hs_to_coq.

(* --- Search --- *)

(*
 * You can omit these lines if you'd like, since Lift does not need them,
 * but enabling these options shows that Find ornament behaves correctly:
 *)
Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.

(*
 * You can also omit this line if you want. Lift will run it automatically the first
 * time. The advantage of running it yourself is that you can name the resulting
 * functions yourself.
 *)
Find ornament list vector as ltv.

(*
 * This gives us these functions:
 *)
Print ltv.
Print ltv_inv.

(*
 * As mentioned in the paper, these form an equivalence.
 * This is proven automatically by the prove equivalence option.
 * See Search.v for a detailed walkthrough of the output.
 *)

(* --- Lift --- *)

Lift list vector in hs_to_coq.zip as zipV_p.
Lift list vector in hs_to_coq.zip_with as zip_withV_p.
Lift list vector in hs_to_coq.zip_with_is_zip as zip_with_is_zipV_p.

(* Here are our lifted types: *)
Check zipV_p.
Check zip_withV_p.
Check zip_with_is_zipV_p.

(* --- Unpack --- *)

Unpack zipV_p as zipV.
Unpack zip_withV_p as zip_withV.
Unpack zip_with_is_zipV_p as zip_with_is_zipV.

(* Enable implicit arguments *)
Arguments zipV {_ _} {_} _ {_} _.
Arguments zip_withV {_ _ _} _ {_} _ {_} _.
Arguments zip_with_is_zipV {_ _} {_} _ {_} _.

(* Here are our unpacked types: *)
Check zipV.
Check zip_withV.
Check zip_with_is_zipV.

(* --- Interface --- *)

(* For any two vectors of the same length, we get a vector of the same length *)
Eval compute in (zipV (consV 0 2 (nilV nat)) (consV 0 1 (nilV nat))).

(*
 * However, this type isn't actually what we want. The user-friendly
 * versions of the functions are simple to recover.
 *
 * First, we will prove the indexer is what we want. To do this, we can
 * simply prove this over the indexer of the original list functions,
 * and then use DEVOID to lift and unpack those proofs.
 *
 * So here we are saying that if two lists have the same length,
 * then the result of zip over those lists has the length of the first list,
 * and same for zip_with. The length function here, ltv_index, is automatically
 * generated when we first run Find Ornament.
 *
 * The intuition is that while list T is equivalent to sigT (vector T),
 * for any n, { l : list T | length l = n } is equivalent to vector T n.
 * Thus, to get functions with the index we really want, as opposed to
 * the automatically generated index, we have to show that length l = n
 * for the n that we want. This will lift to a proof that shows the projection
 * is the n that we want. This methodology will work for any indexer;
 * essentially it leaves the ``interesting part'' (showing the length
 * is some desirable result) to the user.
 *)
Lemma zip_index':
  forall {a} {b} (l1 : list a) (l2 : list b),
    ltv_index _ l1 = ltv_index _ l2 ->
    ltv_index _ (hs_to_coq.zip a b l1 l2) = ltv_index _ l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Lemma zip_with_index':
  forall {A} {B} {C} f (l1 : list A) (l2 : list B),
    ltv_index _ l1 = ltv_index _ l2 ->
    ltv_index _ (hs_to_coq.zip_with A B C f l1 l2) = ltv_index _ l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Preprocess zip_index' as zip_index.
Preprocess zip_with_index' as zip_with_index.
Lift list vector in @zip_index as zipV_proj_p.
Lift list vector in @zip_with_index as zip_withV_proj_p.
Unpack zipV_proj_p as zipV_proj.
Unpack zip_withV_proj_p as zip_withV_proj.
Arguments zipV_proj {_} {_} {_} _ {_} _ _.
Arguments zip_withV_proj {_} {_} {_} _ {_} _ {_} _ _.

(* Our user friendly versions then follow by simple rewriting: *)
Definition zipV_uf {a} {b} {n} (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
  rew (zipV_proj v1 v2 eq_refl) in (zipV v1 v2).

Definition zip_withV_uf {A} {B} {C} (f : A -> B -> C) {n} (v1 : vector A n) (v2 : vector B n) : vector C n :=
  rew (zip_withV_proj f v1 v2 eq_refl) in (zip_withV f v1 v2).

(*
 * For proofs, we have to deal with dependent equality.
 * This is more challenging. Essentially, we have to relate
 * our other equalities.
 *
 * In the case of nat, the easiest
 * way to do this is to use the fact that nats form an hset
 * (credit to Jasper Hugunin). Then, we don't actually need any information
 * about how our auxiliary equalities are formed. Otherwise,
 * the way those equalities are formed will matter.
 *)
From Coq Require Import EqdepFacts Eqdep_dec Arith.

Lemma zip_with_is_zipV_uf_aux :
  forall  {A} {B} {n} (v1 : vector A n) (v2 : vector B n),
    zip_withV_proj pair v1 v2 eq_refl =
    eq_trans
      (eq_sigT_fst (eq_dep_eq_sigT_red _ _ _ _ _ _ (zip_with_is_zipV v1 v2)))
      (zipV_proj v1 v2 eq_refl).
Proof.
  auto using (UIP_dec Nat.eq_dec).
Defined.
(*
 * NOTE ON UIP: In general, we should be able to avoid using UIP over the index
 * by proving adjunction explicitly and then using that along with coherence
 * to show that we do not duplicate equalities (credit to Jason Gross).
 * This holds for all algebraic ornaments, not just those for which UIP holds
 * on the index type.
 *
 * See https://github.com/uwplse/ornamental-search/issues/39 for the latest thoughts
 * on this, and please check the latest version of this file in master to see
 * if we have implemented this if you are reading this in a release.
 *)

(*
 * Our theorem then follows:
 *)
Lemma zip_with_is_zipV_uf :
  forall {A} {B} {n} (v1 : vector A n) (v2 : vector B n),
    zip_withV_uf pair v1 v2 = zipV_uf v1 v2.
Proof.
  intros. unfold zip_withV_uf, zipV_uf, zipV.
  pose proof (eq_sigT_snd (eq_dep_eq_sigT_red _ _ _ _ _ _ (zip_with_is_zipV v1 v2))).
  simpl in *. rewrite <- H. rewrite zip_with_is_zipV_uf_aux.
  apply eq_trans_rew_distr.
Defined.

(*
 * Note: For this particular example, interestingly, doing these by hand
 * without DEVOID, it's possible to construct functions such that the proof
 * of zip_with_is_zipV_uf goes through by reflexivity. However, these
 * are not the analogues of the functions included in the hs_to_coq module
 * (note that the proof using reflexivity does not work for them either).
 *)

(* Client code can then call our functions and proofs, for example: *)

Definition BVand' {n : nat} (v1 : vector bool n) (v2 : vector bool n) : vector bool n :=
  zip_withV_uf andb v1 v2.
