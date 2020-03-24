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
 * lift those from list to vector, and then do a tiny bit of work
 * to get from { s : sigT (vector T) & projT1 s = n} to vector.
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
Module packed_list'.

Definition zip_length := hs_to_coq_lengths.zip_length_n.
Definition zip_with_length := hs_to_coq_lengths.zip_with_length_n.

Print hs_to_coqV_p.list_to_t_rect.

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
  unfold zip_with, zip, packed_list_rect, hs_to_coqV_p.list_to_t_rect, packed_rect. simpl. f_equal.
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
End packed_list'.

(*
 * Now we can get from that to packed_vector_rect:
 *)
Lift Module list vector in hs_to_coq_lengths as hs_to_coq_projT1s.
Preprocess Module packed_list' as packed_list { opaque Ornamental.Eliminators Datatypes Logic Coq.Init.Nat.pred Coq.Init.Peano.eq_add_S hs_to_coq_lengths.zip_length hs_to_coq_lengths.zip_length_n hs_to_coq_lengths.zip_with_length hs_to_coq_lengths.zip_with_length_n hs_to_coqV_p.list_to_t_index packed_list_rect hs_to_coqV_p.list_to_t_rect projT1 projT2 hs_to_coq.zip_with hs_to_coq_lengths.zip_length hs_to_coq_lengths.zip_length_n hs_to_coq_lengths.zip_with_length hs_to_coq_lengths.zip_with_length_n hs_to_coqV_p.list_to_t_index packed_list_rect hs_to_coqV_p.list_to_t_rect projT1 projT2 hs_to_coq.zip hs_to_coq_lengths.zip_length hs_to_coq_lengths.zip_length_n hs_to_coq_lengths.zip_with_length hs_to_coq_lengths.zip_with_length_n hs_to_coqV_p.list_to_t_index packed_list_rect hs_to_coqV_p.list_to_t_rect projT1 projT2 hs_to_coq.zip hs_to_coq.zip_with hs_to_coq.zip_with_is_zip }. 
Lift Module list vector in packed_list as packed_vector.

Check packed_vector.zip.
Check packed_vector.zip_with.
Print packed_list.zip_with_is_zip.
Print packed_vector.zip_with_is_zip.
Check packed_vector.zip_with_is_zip.

(*
 * Finally, we can get from that to unpacked vectors
 * at the index we want very easily.
 * There is WIP on automating this.
 *)
Module uf.

 
(*
 * We first automatically find another ornament
 * (in order to cache this ornament, DEVOID needs the first argument
 * to be a constant).
 *)
Definition packed T n := { s : sigT (vector T) & projT1 s = n}.
Find ornament packed vector as unpack_vector.

(* playing around with useful induction principles for lifting (TODO then take a break and try implementing dumbest stuff w/o elim lifting): *)
Definition unpack_proof :
  forall (T : Type) (n : nat) (P : {s : {n : nat & vector T n} & projT1 s = n} -> Type),
    (forall pv, P pv) ->
    (forall n0 v H, P (existT _ (existT _ n0 v) H)).
Proof.
  intros. apply X.
Defined.

Definition unpack_proof_refl :
  forall (T : Type) (n : nat) (P : {s : {n : nat & vector T n} & projT1 s = n} -> Type),
    (forall pv, P pv) ->
    (forall v, P (unpack_vector_inv T n v)).
Proof.
  intros. apply X.
Defined.

Print packed_vector.zip.

Definition experimental_zip_1 (a b : Type) (n : nat) (v : vector a n) : 
  {l2 : {H : nat & vector b H} & projT1 l2 = n} ->
  {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n}
:=
  unpack_proof_refl a n _ (packed_vector.zip a b n) v.

Definition experimental_zip_2 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : 
  {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n}
:=
  unpack_proof_refl b n _ (unpack_proof_refl a n _ (packed_vector.zip a b n) v1) v2.

Definition experimental_zip_3 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) :
  vector (a * b) n
:=
  unpack_vector
    (a * b)
    n
    (unpack_proof_refl b n _ (unpack_proof_refl a n _ (packed_vector.zip a b n) v1) v2).

(* This gives us: *)

Definition experimental_zip_3_delta (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) :=
  rew
    hs_to_coq_projT1s.zip_length a b (existT _ n v1) (existT _ n v2) (erefl n)
  in
    projT2
      (hs_to_coqV_p.zip a b (existT _ n v1) (existT _ n v2)).

Print packed_vector.zip.
Print packed_rect.
Print packed_vector.zip_with_is_zip.
Print hs_to_coqV_p.zip.

(* Does this form look any nicer? Does it give us an induction principle (unpack_proof_refl?) *)
(* b.c. I can't think of a way to get rid of unpack_vector without introspecting into vector_rect *)
(* ^ TODO can we? at all? ever? if so, how? if not, why not? *)

Check sigT.
(* TODO explain, automate, etc *)
Check zipV_p.
Check zip_withV_p.
Check zip_with_is_zipV_p.

Print hs_to_coqV_p.zip.

Print packed_rect.
Lemma unpacked_rect_rew_1:
  forall (T : Type) (n : nat) (v : vector T n)
         (P : {s : {n0 : nat & vector T n0} & projT1 s = n} -> Type)
         (pf : forall (s : {n0 : nat & vector T n0}) (H : projT1 s = n), P (existT _ s H)),
    packed_rect
      { n0 : nat & vector T n0}
      (fun s => projT1 s)
      Datatypes.id
      (fun (_ : nat) (s : { n : nat & vector T n }) => Datatypes.id)
      n
      P
      pf
      (unpack_vector_inv T n v)
   =
     pf (existT _ n v) eq_refl.
Proof.
  reflexivity.
Defined.

Print unpack_generic_inv.

(* lift v1 *)
Definition unpacked_zip_handwritten_1 (a b : Type) (n : nat) (v1 : vector a n) (v2 : {l2 : {H : nat & vector b H} & projT1 l2 = n}) : {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n} :=
  packed_rect {H : nat & vector a H}
    (fun s => projT1 s)
    Datatypes.id
    (fun (H : nat) (H0 : {H0 : nat & vector a H0}) => Datatypes.id)
    n
    (fun _ : {l1 : {H : nat & vector a H} & projT1 l1 = n} =>
        {l2 : {H : nat & vector b H} & projT1 l2 = n} ->
        {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n})
     (fun (l : {H : nat & vector a H}) (H : projT1 l = n)
          (pl2 : {l2 : {H0 : nat & vector b H0} & projT1 l2 = n}) =>
        existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
          (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 l) (projT2 l))
                   (existT _ (projT1 (projT1 pl2))
                      (projT2 (projT1 pl2)))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 l) (projT2 l))
                   (existT _ (projT1 (projT1 pl2))
                      (projT2 (projT1 pl2))))))
          (packed_vector.zip_length a b n
             (existT _ (projT1 l) (projT2 l))
             (existT _ (projT1 (projT1 pl2)) (projT2 (projT1 pl2)))
             H (projT2 pl2))) 
   (unpack_vector_inv a n v1) (* <-- forget *)
   v2.

(* reduce *)
Definition unpacked_zip_handwritten_2 (a b : Type) (n : nat) (v1 : vector a n) (v2 : {l2 : {H : nat & vector b H} & projT1 l2 = n}) : {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n} :=
  (fun (l : {H : nat & vector a H}) (H : projT1 l = n)
          (pl2 : {l2 : {H0 : nat & vector b H0} & projT1 l2 = n}) =>
        existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
          (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 l) (projT2 l))
                   (existT _ (projT1 (projT1 pl2))
                      (projT2 (projT1 pl2)))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 l) (projT2 l))
                   (existT _ (projT1 (projT1 pl2))
                      (projT2 (projT1 pl2))))))
          (packed_vector.zip_length a b n
             (existT _ (projT1 l) (projT2 l))
             (existT _ (projT1 (projT1 pl2)) (projT2 (projT1 pl2)))
             H (projT2 pl2))) (existT _ n v1) eq_refl v2. 

Lemma unpacked_zip_handwritten_2_OK:
  unpacked_zip_handwritten_1 = unpacked_zip_handwritten_2.
Proof.
  reflexivity. (* unpacked_rect_rew_1 is refl *)
Defined.

(* beta etc: *)
Definition unpacked_zip_handwritten_3 (a b : Type) (n : nat) (v1 : vector a n) (v2 : {l2 : {H : nat & vector b H} & projT1 l2 = n}) : {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n} :=
  (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
          (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ (projT1 (projT1 v2))
                      (projT2 (projT1 v2)))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ (projT1 (projT1 v2))
                      (projT2 (projT1 v2))))))
          (packed_vector.zip_length a b n
             (existT _ n v1)
             (existT _ (projT1 (projT1 v2)) (projT2 (projT1 v2)))
             eq_refl (projT2 v2))).

Lemma unpacked_zip_handwritten_3_OK:
  unpacked_zip_handwritten_2 = unpacked_zip_handwritten_3.
Proof.
  reflexivity. (* obviously *)
Defined.

(* lift v2 *)
Definition unpacked_zip_handwritten_4 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) :=
  (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
          (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2))))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2)))))))
          (packed_vector.zip_length a b n
             (existT _ n v1)
             (existT _ (projT1 (projT1 (unpack_vector_inv b n v2))) (projT2 (projT1 (unpack_vector_inv b n v2))))
             eq_refl (projT2 (unpack_vector_inv b n v2)))).

Lemma unpacked_zip_handwritten_4_OK:
  forall a b n v1 v2,
    unpacked_zip_handwritten_3 a b n v1 (unpack_vector_inv b n v2) =
    unpacked_zip_handwritten_4 a b n v1 v2.
Proof.
  reflexivity. (* obviously *)
Defined.

(* eta *)
Definition unpacked_zip_handwritten_5 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) :=
  (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
          (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ n v2)))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ n v2))))
          (packed_vector.zip_length a b n
             (existT _ n v1)
             (existT _ n v2)
             eq_refl eq_refl)).

Lemma unpacked_zip_handwritten_5_OK:
  forall a b n v1 v2,
    unpacked_zip_handwritten_4 a b n v1 v2 =
    unpacked_zip_handwritten_5 a b n v1 v2.
Proof.
  reflexivity. (* obviously *)
Defined.

(* unpack *)
Definition unpacked_zip_handwritten_6 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
  (unpack_vector (a * b) n
  (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
          (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ n v2)))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ n v1)
                   (existT _ n v2))))
          (packed_vector.zip_length a b n
             (existT _ n v1)
             (existT _ n v2)
             eq_refl eq_refl))).

Lemma unpacked_zip_handwritten_6_OK:
  forall a b n v1 v2,
    unpack_vector (a * b) n (unpacked_zip_handwritten_5 a b n v1 v2) =
    unpacked_zip_handwritten_6 a b n v1 v2.
Proof.
  reflexivity. (* obviously *)
Defined.

Print unpack_generic.

(* reduce *)
Definition unpacked_zip_handwritten_7 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
  rew 
    (packed_vector.zip_length a b n
      (existT _ n v1)
      (existT _ n v2)
      eq_refl eq_refl)
  in
    (projT2
      (hs_to_coqV_p.zip a b
        (existT _ n v1)
        (existT _ n v2))).

Lemma unpacked_zip_handwritten_7_OK:
  forall a b n v1 v2,
    unpacked_zip_handwritten_6 a b n v1 v2 =
    unpacked_zip_handwritten_7 a b n v1 v2.
Proof.
  reflexivity. (* obviously *)
Defined.

Print packed_vector.zip_length.
Print hs_to_coq_projT1s.zip_length_n.

(* reduce *)
Definition unpacked_zip_handwritten_8 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
  rew 
    (hs_to_coq_projT1s.zip_length a b (existT _ n v1) (existT _ n v2) eq_refl)
  in
    (projT2 (hs_to_coqV_p.zip a b (existT _ n v1) (existT _ n v2))).

Lemma unpacked_zip_handwritten_8_OK:
  forall a b n v1 v2,
    unpacked_zip_handwritten_7 a b n v1 v2 =
    unpacked_zip_handwritten_8 a b n v1 v2.
Proof.
  reflexivity. (* obviously *)
Defined.

(* no idea how to get to something like this. is it doable automatically? why/why not? TODO: *)
Program Definition unpacked_zip_ideal (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
VectorDef.t_rect a
  (fun (n : nat) (_ : vector a n) =>
   vector b n -> vector (a * b) n) (* Our P above at i_b, at the second projection *)
  (fun _ : vector b 0 => (nilV (a * b)))
  (fun (h : a) (n : nat) (_ : vector a n)
     (H : vector b n -> vector (a * b) n)
     (arg_1__0 : vector b (S n)) =>
     (VectorDef.t_rect b (* second projection of zip with zip_length substituted in *)
           (fun (n0 : nat) (_ : vector b n0) => vector (a * b) _)
           (nilV (a * b))
           (fun (h0 : b) (n0 : nat) (t1 : vector b n0)
              (IH : vector (a * b) n0) =>
              (consV n0 (h, h0) IH))
           (S n) arg_1__0)) 
  n
  v1
  v2.

(* TODO is there an induction principle that describes that? check it out *)

(* TODO move a lot of below to separate test file so we can really work through easy tests: *)
Check unpack_vector.
Print unpack_vector.
Print unpack_vector_inv.
Print unpack_generic.
Print packed_vector.zip.
Print hs_to_coq_projT1s.zip_length_n.
(* TODO get working: *)
Definition minimal_test (T : Type) (n : nat) := { s : { n : nat & vector T n } & projT1 s = n }.
Lift packed vector in minimal_test as minimal_test_lifted. (* TODO move to tests somewhere *)
Print minimal_test_lifted.
Definition proj1_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT1 pv.
Print proj1_test.
Lift packed vector in proj1_test as proj1_test_lifted.
Definition proj1_test_expected (T : Type) (n : nat) (v : vector T n) := existT _ n v.
Print proj1_test_expected.
Print proj1_test_lifted.
Definition minimal_test_2 (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := pv.
Lift packed vector in minimal_test_2 as minimal_test_2_lifted { opaque eq_rect }. (* TODO need to stop this from reducing generally... refold or something *)
Print minimal_test_2_lifted.
Definition proj2_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT2 pv.
Lift packed vector in proj2_test as proj2_test_lifted.

Print proj2_test_lifted.

Definition lifted (T : Type) (n : nat)  (pv : vector T n) :=
  existT (fun (s : sigT (vector T)) => projT1 s = n) (existT (fun n => vector T n) n pv) (eq_refl n).
Check lifted.
Definition ex_test_constr (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) : {s : {x : nat & vector T x} & projT1 s = n} :=
  (fun n v H => existT _ (existT _ n v) H) (projT1 (projT1 pv)) (projT2 (projT1 pv)) (projT2 pv).

Print ex_test_constr.
Lift packed vector in ex_test_constr as ex_test_constr_lifted.
Print ex_test_constr_lifted.
Lemma ex_test_constr_lift_correct :
  forall T n v, ex_test_constr_lifted T n v = v.
Proof.
  reflexivity.
Qed.

(* TODO we will need to eta expand below to above before running: *)
Definition ex_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := existT _ (projT1 pv) (projT2 pv).
Definition ex_test_expected (T : Type) (n : nat) (v : vector T n) := v.

Lift packed vector in ex_test as ex_test_lifted.
Print ex_test_lifted. (* TODO yay!!! ok now move on to other tests *)

Definition proj1_eta_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT1 (existT _ (projT1 pv) (projT2 pv)).
Lift packed vector in proj1_eta_test as proj1_eta_test_lifted.
Print proj1_eta_test_lifted.

(* TODO still stuck here: *)
Print packed_vector.zip.

(* TODO lift module *)
Lift packed vector in packed_vector.zip_length as zip_length { opaque eq_rect hs_to_coq_projT1s.zip_length_n hs_to_coqV_p.zip hs_to_coq_projT1s.zip_length eq_trans eq_sym eq_ind }.
Lift packed vector in packed_vector.zip_with_length as zip_with_length  { opaque eq_rect hs_to_coq_projT1s.zip_with_length_n hs_to_coqV_p.zip_with hs_to_coq_projT1s.zip_with_length eq_trans eq_sym eq_ind }.
Lift packed vector in packed_vector.zip as zip { opaque eq_rect hs_to_coq_projT1s.zip_length_n hs_to_coqV_p.zip hs_to_coq_projT1s.zip_length eq_trans eq_sym eq_ind }.
Lift packed vector in packed_vector.zip_with as zip_with  { opaque eq_rect hs_to_coq_projT1s.zip_with_length_n hs_to_coqV_p.zip_with hs_to_coq_projT1s.zip_with_length eq_trans eq_sym eq_ind }.

Print packed_vector.zip_with_is_zip.
Print eq_existT_uncurried.

Lift packed vector in packed_vector.zip_with_is_zip as zip_with_is_zip
 { opaque f_equal hs_to_coqV_p.zip_with_is_zip Coq.Init.Logic.eq_ind
   Coq.Init.Logic.eq_trans Coq.Init.Logic.eq_sym
   hs_to_coqV_p.zip hs_to_coqV_p.zip_with hs_to_coq_projT1s.zip_length
   hs_to_coq_projT1s.zip_length_n eq_rect eq_rect_r eq_rec eq_rec_r eq_ind 
   eq_ind_r hs_to_coq_projT1s.zip_with_length_n hs_to_coq_projT1s.zip_with_length
   packed_vector.Coq_Logic_Eqdep_dec_UIP_dec packed_vector.Coq_Arith_PeanoNat_Nat_eq_dec
   existT EqdepFacts.internal_eq_rew_r_dep sig_ind eq_existT_uncurried }.
(* TODO clean opaques *)

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
  pose proof (packed_vector.zip_with_is_zip A B n (unpack_vector_inv A n v1) (unpack_vector_inv B n v2)).
  unfold zip_with, zip. f_equal. auto.
Defined.

End uf.
(*
 * TECHNICAL NOTE: For this particular example, interestingly, doing these by hand
 * without DEVOID, it's possible to construct functions such that the proof
 * of zip_with_is_zipV_uf goes through by reflexivity. However, these
 * are not the analogues of the functions included in the hs_to_coq module
 * (note that the proof using reflexivity does not work for them either).
 *)

(* --- Interface --- *)

(* Client code can then call our functions and proofs, for example: *)
Definition BVand' {n : nat} (v1 : vector bool n) (v2 : vector bool n) : vector bool n :=
  uf.zip_with andb v1 v2.

