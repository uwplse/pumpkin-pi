(*
 * Section 2 Example
 *)

Add LoadPath "coq/examples".
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

From Coq Require Import ssreflect ssrbool ssrfun Arith.

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
  forall l1 l2, zip_with (@pair A B) l1 l2 = zip l1 l2.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

End hs_to_coq'.

(* --- Preprocess --- *)

Preprocess Module hs_to_coq' as hs_to_coq { opaque list_ind list_rect eq_ind eq_ind_r eq_sym }.

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

(*
 * You can omit this as well, but it makes the types look nicer:
 *)
Set DEVOID lift type.

(*
 * Since the ITP paper, we now have a "Lift Module" command:
 *)
Lift Module list vector in hs_to_coq as hs_to_coqV_p.

Definition zipV_p := hs_to_coqV_p.zip.
Definition zip_withV_p := hs_to_coqV_p.zip_with.
Definition zip_with_is_zipV_p := hs_to_coqV_p.zip_with_is_zip.

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
 * and same for zip_with.
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
Module hs_to_coq_lengths'.

Lemma zip_length:
  forall a b (l1 : list a) (l2 : list b),
    length l1 = length l2 ->
    length (hs_to_coq.zip a b l1 l2) = length l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Lemma zip_length_n:
  forall a b (n : nat) (l1 : list a) (l2 : list b),
    length l1 = n ->
    length l2 = n ->
    length (hs_to_coq.zip a b l1 l2) = n.
Proof.
  intros. rewrite <- H. apply zip_length. eapply eq_trans; eauto. 
Defined.

Lemma zip_with_length:
  forall A B C f (l1 : list A) (l2 : list B),
    length l1 = length l2 ->
    length (hs_to_coq.zip_with A B C f l1 l2) = length l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Lemma zip_with_length_n:
  forall A B C f (n : nat) (l1 : list A) (l2 : list B),
    length l1 = n ->
    length l2 = n ->
    length (hs_to_coq.zip_with A B C f l1 l2) = n.
Proof.
  intros. rewrite <- H. apply zip_with_length. eapply eq_trans; eauto.
Defined.

End hs_to_coq_lengths'.

Preprocess Module hs_to_coq_lengths' as hs_to_coq_lengths.

(*
 * Once we have the length proofs, we write the proofs
 * about { l : list T & length l = n }. To do this,
 * it's useful to have a nice induction principle:
 *)
Theorem packed_list_rect:
  forall (A : Type) (n : nat) (P : { l : list A & length l = n } -> Type),
    (forall (l : list A) (H : length l = n), P (existT _ l H)) ->
    forall pl, P (existT _ (projT1 pl) (projT2 pl)).
Proof.
  intros A n P pf pl. apply (pf (projT1 pl) (projT2 pl)).
Defined.

(*
 * NOTE: Right now, lifting doesn't work nicely if you don't
 * eta-expand pl in the conclusion. So you should not use
 * sigT_eta, sigT_rect, and so on to get a conclusion of the
 * form (P pl). I'm working on relaxing this assumption
 * and understanding more about it.
 *
 * For now, just copy and paste that induction principle.
 * Then you'll see this will lift without issue:
 *)
Lift list vector in packed_list_rect as packed_vector_rect.

(*
 * Then we can write our proofs:
 *)
Module packed_list.

Definition zip_length := hs_to_coq_lengths.zip_length_n.
Definition zip_with_length := hs_to_coq_lengths.zip_with_length_n.

Program Definition zip:
  forall a b n,
    { l1 : list a & length l1 = n } ->
    { l2 : list b & length l2 = n } ->
    { l3 : list (a * b) & length l3 = n }.
Proof.
  intros a b n pl1. apply packed_list_rect with (P := fun (pl1 : { l1 : list a & length l1 = n }) => { l2 : list b & length l2 = n } -> { l3 : list (a * b) & length l3 = n }).
  - intros l H pl2. 
    (* list function: *)
    exists (hs_to_coq.zip a b l (projT1 pl2)). 
    (* length invariant: *)
    apply zip_length; auto. apply (projT2 pl2).
  - apply pl1. 
Defined.

Program Definition zip_with:
  forall A B C (f : A -> B -> C) n,
    { l1 : list A & length l1 = n } ->
    { l2 : list B & length l2 = n } ->
    { l3 : list C & length l3 = n }.
Proof.
  intros A B C f n pl1. apply packed_list_rect with (P := fun (pl1 : {l1 : list A & length l1 = n}) => {l2 : list B & length l2 = n} -> {l3 : list C & length l3 = n}).
  - intros l H pl2.
    (* list function: *)
    exists (hs_to_coq.zip_with A B C f l (projT1 pl2)).
    (* length invariant: *)
    apply zip_with_length; auto. apply (projT2 pl2).
  - apply pl1.
Defined.

(*
 * The length invariant here relates our _proofs_ of the
 * above length invariants. Ouch! Luckily, for lists,
 * we can just use UIP, since equality over natural numbers
 * is decidable:
 *)
Lemma zip_with_is_zip :
  forall A B n (pl1 : { l1 : list A & length l1 = n }) (pl2 : { l2 : list B & length l2 = n }),
    zip_with A B (A * B) pair n pl1 pl2 = zip A B n pl1 pl2.
Proof.
  intros A B n pl1. 
  apply packed_list_rect with (P := fun (pl1 : {l1 : list A & length l1 = n}) => forall pl2 : {l2 : list B & length l2 = n}, zip_with A B (A * B) pair n pl1 pl2 = zip A B n pl1 pl2). 
  intros l  H pl2.
  (* list proof: *)
  apply EqdepFacts.eq_sigT_sig_eq.
  exists (hs_to_coq.zip_with_is_zip A B l (projT1 pl2)).
  (* length invariant: *)
  apply (Eqdep_dec.UIP_dec Nat.eq_dec).
Defined.
(*
 * NOTE ON UIP: In general, we may be able to avoid using UIP over the index
 * using adjunction and coherence together to show that we do not duplicate equalities (credit to Jason Gross).
 * There is also a coq-club thread about this with an alternative approach.
 * This should hopefully work for any algebraic ornament.
 * For now, if you do not have UIP on your index, you still run into
 * the equalities of equalities problem at some point.
 *
 * I will update this file when we solve this problem.
 *)

End packed_list.

(*
 * Now we can get from that to packed_vector_rect:
 *)
Lift Module list vector in packed_list as packed_vector.

Check packed_vector.zip.
Check packed_vector.zip_with.
Check packed_vector.zip_with_is_zip.

(*
 * Finally, we can get from that to unpacked vectors
 * at the index we want very easily.
 * For now, we do this part manually.
 * There is WIP on automating this, and I will update
 * this file when I do.
 *)
Module uf.

Program Definition vector_pv:
  forall (T : Type) (n : nat) (v : vector T n),
    { s : sigT (vector T) & projT1 s = n }.
Proof.
  intros T n v. exists (existT _ n v). reflexivity.
Defined.

Program Definition pv_vector:
  forall (T : Type) (n : nat) (pv : { s : sigT (vector T) & projT1 s = n }),
    vector T n.
Proof.
  intros T n pv. apply (@eq_rect _ (projT1 (projT1 pv)) _  (projT2 (projT1 pv)) n (projT2 pv)).
Defined.

Program Definition zip:
  forall {A B : Type} {n : nat},
    vector A n ->
    vector B n ->
    vector (A * B) n.
Proof.
  intros A B n v1 v2. apply pv_vector. apply packed_vector.zip.
  - apply (vector_pv A n v1).
  - apply (vector_pv B n v2).
Defined.

Program Definition zip_with:
  forall {A B C : Type} (f : A -> B -> C) {n : nat},
    vector A n ->
    vector B n ->
    vector C n.
Proof.
  intros A B C f n v1 v2. apply pv_vector. apply (packed_vector.zip_with A B).
  - apply f.
  - apply (vector_pv A n v1).
  - apply (vector_pv B n v2).
Defined.

(*
 * The advantage of all of this is that our proof is trivial,
 * whereas over normal vectors it can be painful to separate the
 * data from the index:
 *)
Lemma zip_with_is_zip:
  forall {A B : Type} (n : nat) (v1 : vector A n) (v2 : vector B n),
    zip_with (@pair A B) v1 v2 = zip v1 v2.
Proof.
  intros A B n v1 v2.
  pose proof (packed_vector.zip_with_is_zip A B n (vector_pv A n v1) (vector_pv B n v2)).
  unfold zip_with, zip. f_equal. auto.
Defined.

End uf.
(*
 * NOTE: For this particular example, interestingly, doing these by hand
 * without DEVOID, it's possible to construct functions such that the proof
 * of zip_with_is_zipV_uf goes through by reflexivity. However, these
 * are not the analogues of the functions included in the hs_to_coq module
 * (note that the proof using reflexivity does not work for them either).
 *)

(* Client code can then call our functions and proofs, for example: *)
Definition BVand' {n : nat} (v1 : vector bool n) (v2 : vector bool n) : vector bool n :=
  uf.zip_with andb v1 v2.

