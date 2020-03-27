(*
 * Section 2 Example from the ITP 2019 paper.
 *
 * NOTE: This has changed a lot since the ITP paper! I have updated this file
 * to reflect the latest automation. To see the original ITP version,
 * take a look at the state of this file in the ITP release.
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

(*
 * We define our terms using match statements, so we first need to preprocess.
 * Sometimes we can get away without this when we write terms ourselves, as is
 * true later in this file.
 *)

Preprocess Module hs_to_coq' as hs_to_coq { opaque list_ind list_rect Coq.Init.Logic }.

(* --- Search and Lift --- *)

(*
 * You can omit these lines if you'd like, since Lift does not need them,
 * but enabling these options shows that search behaves correctly:
 *)
Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.

(*
 * You can omit this as well, but it makes the types look nicer:
 *)
Set DEVOID lift type.

(*
 * This option tells DEVOID to generate an induction principle that
 * will be useful later:
 *)
Set DEVOID search smart eliminators.

(*
 * We can then lift our entire module (search runs automatically):
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

(*
 * Now we have proofs about sigT (vector T), but we want proofs about
 * vector T n. So now we can use a methodology to get from lists to
 * these proofs.
 *
 * The intuition for this methodology is that while list T is equivalent to sigT (vector T),
 * for any n, { l : list T & length l = n } lifts to equivalent
 * { s : sigT (vector T) & projT1 s = n}, which is equivalent to vector T n.
 * Thus, we write proofs about { l : list T & length l = n },
 * lift those from list to vector, and then lift those again
 * from { s : sigT (vector T) & projT1 s = n} to vector.
 *
 * However, writing proofs about { l : list T & length l = n } isn't
 * in itself straightforward, so we break this up into parts and use
 * a nice custom eliminator to make this easier.
 *
 * Let's start by proving the length invariants:
 *)
Module hs_to_coq_lengths'.

Lemma zip_length:
  forall a b (l1 : list a) (l2 : list b),
    length l1 = length l2 ->
    length (hs_to_coq.zip a b l1 l2) = length l1.
Proof.
  induction l1, l2; intros; auto. 
  simpl. f_equal. rewrite IHl1; auto.
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
  induction l1, l2; intros; auto.
  simpl. f_equal. rewrite IHl1; auto.
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

Preprocess Module hs_to_coq_lengths' as hs_to_coq_lengths { opaque Datatypes Logic Coq.Init.Nat.pred Coq.Init.Peano.eq_add_S hs_to_coq.zip hs_to_coq.zip_with list_ind list_rect }.

(*
 * Once we have the length proofs, we write the proofs
 * about { l : list T & length l = n }. To do this,
 * it's useful to have a nice induction principle,
 * which DEVOID generated since we set the "smart elims" option
 * (the name of this will always be the name of your promote function
 * followed by _rect):
 *)
Definition packed_list_rect := hs_to_coqV_p.list_to_t_rect.
Check packed_list_rect.
(*
 * TECHNICAL NOTE: DEVOID for now makes some assumptions
 * about the format here. Try not to run "induction" on terms of type
 * { l : list T & length l = n } directly, and instead try to 
 * use this induction principle. I'm working on relaxing this
 * assumption and understanding more about it. It has to do with
 * preserving definitional equalities when we lift.
 *)

(*
 * Then we can write our proofs. Now note how everything here
 * follows a nice and easy formula:
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
  intros l H pl2.
  unfold zip_with, zip, packed_list_rect, hs_to_coqV_p.list_to_t_rect, packed_rect. simpl.
  apply eq_existT_uncurried.
  (* list proof: *)
  exists (hs_to_coq.zip_with_is_zip A B l (projT1 pl2)).
  (* length invariant: *)
  apply (Eqdep_dec.UIP_dec Nat.eq_dec).
Defined.
(*
 * TECHNICAL NOTE: In general, we may be able to avoid using UIP over the index
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
 * Now we can get from that to { s : sigT (vector T) & projT1 s = n} by lifting from
 * lists to vectors.
 *)
Lift Module list vector in hs_to_coq_lengths as hs_to_coq_projT1s.
Lift Module list vector in packed_list as packed_vector.

(*
 * Finally, we can get from { s : sigT (vector T) & projT1 s = n} to unpacked vectors
 * at the index we want very easily.
 *
 * First we define a constant for { s : sigT (vector T) & projT1 s = n}, since DEVOID needs
 * this for caching.
 *)
Definition packed T n := { s : sigT (vector T) & projT1 s = n}.

(*
 * We can get away without preprocessing here, though we must set some terms to opaque to do that:
 *)
Configure Lift packed vector { opaque Eqdep_dec.UIP_dec Nat.eq_dec }.

(* TODO move these tests later *)
Definition my_id (T : Type) (n : nat) (v : vector T n) := v.
Lift vector packed in my_id as id'.
Print id'.
Definition my_cons (T : Type) (n : nat) (v : vector T n) (t : T) := consV n t v.
Print t_unpack.
Lift vector packed in my_cons as my_cons'.
Fail.

Definition my_zip (a b : Type) (n : nat) (pl1 : vector a n) (pl2 : vector b n) :=
rew [vector (a * b)]
    packed_vector.zip_length a b n (existT [eta vector a] n pl1)
      (existT [eta vector b] n pl2) (Datatypes.id (erefl n)) 
      (erefl n) in
projT2
  (hs_to_coqV_p.zip a b (existT [eta vector a] n pl1)
     (existT [eta vector b] n pl2)).
Lift vector packed in my_zip as zip'.

(* end TODO *)

(*
 * Then we lift (lifting hs_to_coqV_p first makes this faster and makes the result prettier):
 *)
Lift Module packed vector in hs_to_coqV_p as hs_to_coqV_u.
Lift Module packed vector in packed_vector as uf.

(* We are done. Here are our final types: *)
Check uf.zip.
Print uf.zip.
Check uf.zip_with.
Check uf.zip_with_is_zip.
(*
 * TECHNICAL NOTE: For this particular example, interestingly, doing these by hand
 * without DEVOID, it's possible to construct functions such that the proof
 * of uf.zip_with_is_zipV goes through by reflexivity. However, these
 * are not the analogues of the functions included in the hs_to_coq module
 * (note that the proof using reflexivity does not work for them either).
 *)

(* --- Interface --- *)

(* Client code can then call our functions and proofs, for example: *)
Definition BVand' {n : nat} (v1 : vector bool n) (v2 : vector bool n) : vector bool n :=
  uf.zip_with bool bool bool andb n v1 v2.

