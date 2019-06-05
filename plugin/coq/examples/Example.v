(*
 * BEGIN DEVOID DEMO, PART 1
 *)
Add LoadPath "coq/examples". (* <-- sorry for doing this, I know it's bad *)
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

From Coq Require Import ssreflect ssrbool ssrfun.

Import EqNotations.

Check list_rect.
Check Vector.t_rect.

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

(*
 * DEVOID assumes eliminators rather than fixpoints, so we run
 * a preprocessing step to convert fixpoints to eliminators.
 *)
Preprocess Module hs_to_coq' as hs_to_coq.

(* --- Search --- *)

(*
 * This is the functionality I want to highlight today in the demo.
 * I'll explain how this works later.
 *
 * A type equivalence is a pair of functions f and g that are mutual inverses.
 * By default, DEVOID finds only the fold (like length), f, and g, since that's
 * all that our lift command actually needs. However, we can also generate
 * the equivalence proofs by turning on this option:
 *)
Set DEVOID search prove equivalence.

(*
 * This option produces a proof that relates the fold to f and g:
 *)
Set DEVOID search prove coherence.

(*
 * Cool. Now we can search for the equivalence just by passing "list" and "vector"
 * to the Find ornament command. 
 *)
Find ornament list vector as ltv.

(*
 * This gives us the length function:
 *)
Print ltv_index.

(*
 * Note that this computes the length:
 *)
Example indexer_is_length:
  forall {T : Type} (l : list T),
    ltv_index _ l = length l.
Proof.
  reflexivity.
Qed.

(*
 * It also gives us f and g (here ltv and ltv_inv) which take us back and 
 * forth across the equivalence.
 *
 * The function ltv : list T -> sigT (vector T) explicitly applies the indexer:
 *)
Print ltv.

(*
 * The function ltv_inv : sigT (vector T) -> list T just eliminates over
 * the projections:
 *)
Print ltv_inv.

(* 
 * This is enough for DEVOID to lift functions and proofs, but since it's
 * cool and lets us plug into other frameworks like Equivalences for Free!,
 * and since it proves correctness in each instance, let's show you
 * the automatically generated proofs, too. 
 *
 * First, note the types are what we want:
 *)
Theorem coherence:
  forall {T : Type} (l : list T),
    ltv_index _ l = projT1 (ltv _ l).
Proof.
  exact ltv_coh.
Qed.

Theorem section:
  forall {T : Type} (l : list T),
    ltv_inv _ (ltv _ l) = l.
Proof.
  exact ltv_section.
Qed.

Theorem retraction:
  forall {T : Type} (v : sigT (fun n => vector T n)),
    ltv _ (ltv_inv _ v) = v.
Proof.
  exact ltv_retraction.
Qed.

(*
 * Since we're all nerds here, let's look at the proof terms that DEVOID generated.
 *
 * Cherence is really trivial:
 *)

Print ltv_coh.

(*
 * Section and retraction are more interesting, but still very easy to automate:
 *)
Print ltv_section.
Print ltv_retraction.
(*
 * Basically, these just say that equalities are preserved in the inductive case.
 * So the base case is eq_refl, and the inductive case is a fold over eq_ind
 * to substitute each IH with eq_refl as the identity.
 *)

(* --- Lift --- *)

(*
 * This is not what I want to focus on today, but another cute thing here
 * is that once you have f, g, and the indexer, you can run the Lift command
 * to port functions and proofs. And since this is a really nice class of
 * equivalences, you can actually directly lift the eliminator, so you don't
 * have to go back and forth between lists and vectors. 
 *
 * Here we lift our functions and proofs:
 *)
Lift list vector in hs_to_coq.zip as zipV_p.
Lift list vector in hs_to_coq.zip_with as zip_withV_p.
Lift list vector in hs_to_coq.zip_with_is_zip as zip_with_is_zipV_p.

(* Here are our lifted types: *)
Check zipV_p.
Check zip_withV_p.
Check zip_with_is_zipV_p.

(*
 * END DEVOID DEMO, PART 1
 *)

(* --- Unpack --- *)

(*
 * Demo ends here, but from here on out, we have some machinery and a 
 * methodology for obtaining nicer types. I'm not going to run through 
 * this today, but there are still a lot of really interesting questions 
 * left w.r.t. how to automate as much as possible user-friendly types 
 * without depending on properties of the particular index.
 *
 * Or maybe it's not even easy to automate in a reasonable
 * way directly, and I want to extend Search and Lift to support the other
 * form of the equivalence directly; see 
 * http://github.com/uwplse/ornamental-search/issues/42.
 *
 * Anyways, if you play with this on your own, the Unpack command
 * just does the really obvious thing, and still doesn't give you great
 * types:
 *)
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

(*
 * And then this part is the place where we still have a lot of open and
 * interesting questions.
 *
 * As a programmer, we might want to restrict our zip functions to take
 * only vectors of the same length. Note that for any two vectors of the 
 * same length, we get a vector of the same length: 
 *)
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
 * our other equalities. What I think is cute about this is that it captures,
 * in my opinion, the essence of what is actually hard about dependent types:
 * at some point, no matter what you do, you are reasoning about equalities of
 * equalities (though you may be able to make those all refl by construction if
 * you're lucky). 
 *
 * In the case of nat, the easiest
 * way to do this is to use the fact that nats form an hset
 * (credit to Jasper Hugunin). Then, we don't actually need any information
 * about how our auxiliary equalities are formed. Otherwise,
 * the way those equalities are formed will matter (bonus fun problem: 
 * figure out how to do this more generally without UIP, changing only the proj 
 * lemmas if necessary, and submit a PR; see
 * https://github.com/uwplse/ornamental-search/issues/39 for some thoughts).
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

