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

Preprocess Module hs_to_coq' as hs_to_coq { opaque list_ind list_rect eq_ind eq_ind_r eq_sym }.

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
  intros l  H pl2.
  (* list proof: *)
  apply EqdepFacts.eq_sigT_sig_eq.
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
 * Now we can get from that to packed_vector_rect:
 *)
Lift Module list vector in packed_list as packed_vector.

Check packed_vector.zip.
Check packed_vector.zip_with.
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

Print packed_vector.zip.

(*
 packed_vector.zip = 
fun (a b : Type) (n : nat) =>
[eta packed_rect {H : nat & vector a H} [eta projT1 (P:=_)]
       Datatypes.id
       (fun (H : nat) (H0 : {H0 : nat & vector a H0}) => Datatypes.id) n
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
             H (projT2 pl2)))]
     : forall (a b : Type) (n : nat),
       {l1 : {H : nat & vector a H} & projT1 l1 = n} ->
       {l2 : {H : nat & vector b H} & projT1 l2 = n} ->
       {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n}
*)

(* forget arg: *)
Definition unpacked_zip_handwritten_1 (a b : Type) (n : nat) (v1 : vector a n) (v2 : {l2 : {H : nat & vector b H} & projT1 l2 = n}) : {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n} :=
  packed_rect
    {H : nat & vector a H}
    (fun s => projT1 s)
    Datatypes.id
    (fun (H : nat) (H0 : {H0 : nat & vector a H0}) => Datatypes.id) n
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

Print packed_rect.

(* reduce function *)
Definition unpacked_zip_handwritten_2 (a b : Type) (n : nat) (v1 : vector a n) (v2 : {l2 : {H : nat & vector b H} & projT1 l2 = n}) : {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n} :=
       ((fun (l : {H : nat & vector a H}) (H : projT1 l = n)
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
             H (projT2 pl2))) (projT1 (unpack_vector_inv a n v1)) (projT2 (unpack_vector_inv a n v1)))
   v2.

(* lift v2 *)
Definition unpacked_zip_handwritten_3 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : {l3 : {H : nat & vector (a * b) H} & projT1 l3 = n} :=
   existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
       (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2))))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2)))))))
       (packed_vector.zip_length a b n
          (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
          (existT _ (projT1 (projT1 (unpack_vector_inv b n v2))) (projT2 (projT1 (unpack_vector_inv b n v2))))
          (projT2 (unpack_vector_inv a n v1)) (projT2 (unpack_vector_inv b n v2))).

(* lift result *)
Definition unpacked_zip_handwritten_4 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
   unpack_vector (a * b) n
   (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
       (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2))))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2)))))))
       (packed_vector.zip_length a b n
          (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
          (existT _ (projT1 (projT1 (unpack_vector_inv b n v2))) (projT2 (projT1 (unpack_vector_inv b n v2))))
          (projT2 (unpack_vector_inv a n v1)) (projT2 (unpack_vector_inv b n v2)))). 

(* reduce *)
Print unpack_generic.    
Definition unpacked_zip_handwritten_5 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
   rew 
   (projT2 
   (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
       (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2))))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2)))))))
       (packed_vector.zip_length a b n
          (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
          (existT _ (projT1 (projT1 (unpack_vector_inv b n v2))) (projT2 (projT1 (unpack_vector_inv b n v2))))
          (projT2 (unpack_vector_inv a n v1)) (projT2 (unpack_vector_inv b n v2)))))
    in 
    (projT2 (projT1 (existT (fun l3 : {H0 : nat & vector (a * b) H0} => projT1 l3 = n)
       (existT _
             (projT1
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2))))))
             (projT2
                (hs_to_coqV_p.zip a b
                   (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
                   (existT _ (projT1 (projT1 (unpack_vector_inv b n v2)))
                      (projT2 (projT1 (unpack_vector_inv b n v2)))))))
       (packed_vector.zip_length a b n
          (existT _ (projT1 (projT1 (unpack_vector_inv a n v1))) (projT2 (projT1 (unpack_vector_inv a n v1))))
          (existT _ (projT1 (projT1 (unpack_vector_inv b n v2))) (projT2 (projT1 (unpack_vector_inv b n v2))))
          (projT2 (unpack_vector_inv a n v1)) (projT2 (unpack_vector_inv b n v2)))))). 

Print unpack_generic_inv.

(* reduce projections to see if a pattern emerges *)
Definition unpacked_zip_handwritten_6 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
   rew 
    (packed_vector.zip_length a b n
       (existT _ n v1)
       (existT _ n v2)
       (erefl n)
       (erefl n))
    in 
    (projT2
       (hs_to_coqV_p.zip a b
         (existT _ n v1)
         (existT _ n v2))).

(* Continue down this line. Want to see if can simplify nicely. *)
Print packed_vector.zip_length.
Definition unpacked_zip_handwritten_7 (a b : Type) (n : nat) (v1 : vector a n) (v2 : vector b n) : vector (a * b) n :=
   rew 
    (let l1 := (existT _ n v1) in let l2 := (existT _ n v2)
     in let H := erefl n in let H0 := erefl n in
hs_to_coq_lengths.Coq_Init_Logic_eq_ind nat (projT1 l1)
  [eta eq
         (projT1
            (VectorDef.t_rect a
               (fun (n1 : nat) (_ : vector a n1) =>
                {H1 : nat & vector b H1} -> {H1 : nat & vector (a * b) H1})
               (fun _ : {H1 : nat & vector b H1} =>
                existT _ 0 (nilV (a * b)))
               (fun (h : a) (n1 : nat) (_ : vector a n1)
                  (H1 : {H1 : nat & vector b H1} ->
                        {H1 : nat & vector (a * b) H1})
                  (arg_1__ : {H2 : nat & vector b H2}) =>
                existT _
                  (projT1
                     (VectorDef.t_rect b
                        (fun (n2 : nat) (_ : vector b n2) =>
                         {H2 : nat & vector (a * b) H2})
                        (existT _ 0 (nilV (a * b)))
                        (fun (h0 : b) (n2 : nat) (t1 : vector b n2)
                           (_ : {H2 : nat & vector (a * b) H2}) =>
                         existT _
                           (S (projT1 (H1 (existT _ n2 t1))))
                           (consV
                              (projT1 (H1 (existT _ n2 t1)))
                              (h, h0)
                              (projT2 (H1 (existT _ n2 t1)))))
                        (projT1 arg_1__)
                        (projT2 arg_1__)))
                  (projT2
                     (VectorDef.t_rect b
                        (fun (n2 : nat) (_ : vector b n2) =>
                         {H2 : nat & vector (a * b) H2})
                        (existT _ 0 (nilV (a * b)))
                        (fun (h0 : b) (n2 : nat) (t1 : vector b n2)
                           (_ : {H2 : nat & vector (a * b) H2}) =>
                         existT _
                           (S (projT1 (H1 (existT _ n2 t1))))
                           (consV
                              (projT1 (H1 (existT _ n2 t1)))
                              (h, h0)
                              (projT2 (H1 (existT _ n2 t1)))))
                        (projT1 arg_1__)
                        (projT2 arg_1__))))
               (projT1 l1)
               (projT2 l1)
               (existT _ (projT1 l2) (projT2 l2))))]
  (VectorDef.t_rect a
     (fun (n0 : nat) (t0 : vector a n0) =>
      forall l3 : {H1 : nat & vector b H1},
      n0 = projT1 l3 ->
      projT1
        (VectorDef.t_rect a
           (fun (n1 : nat) (_ : vector a n1) =>
            {H1 : nat & vector b H1} -> {H1 : nat & vector (a * b) H1})
           (fun _ : {H1 : nat & vector b H1} =>
            existT _ 0 (nilV (a * b)))
           (fun (h : a) (n1 : nat) (_ : vector a n1)
              (H1 : {H1 : nat & vector b H1} -> {H1 : nat & vector (a * b) H1})
              (arg_1__ : {H2 : nat & vector b H2}) =>
            existT _
              (projT1
                 (VectorDef.t_rect b
                    (fun (n2 : nat) (_ : vector b n2) =>
                     {H2 : nat & vector (a * b) H2})
                    (existT _ 0 (nilV (a * b)))
                    (fun (h0 : b) (n2 : nat) (t2 : vector b n2)
                       (_ : {H2 : nat & vector (a * b) H2}) =>
                     existT _
                       (S (projT1 (H1 (existT _ n2 t2))))
                       (consV
                         (projT1 (H1 (existT _ n2 t2)))
                         (h, h0)
                         (projT2 (H1 (existT _ n2 t2)))))
                    (projT1 arg_1__)
                    (projT2 arg_1__)))
              (projT2
                 (VectorDef.t_rect b
                    (fun (n2 : nat) (_ : vector b n2) =>
                     {H2 : nat & vector (a * b) H2})
                    (existT _ 0 (nilV (a * b)))
                    (fun (h0 : b) (n2 : nat) (t2 : vector b n2)
                       (_ : {H2 : nat & vector (a * b) H2}) =>
                     existT _
                       (S (projT1 (H1 (existT _ n2 t2))))
                       (consV
                         (projT1 (H1 (existT _ n2 t2)))
                         (h, h0)
                         (projT2 (H1 (existT _ n2 t2)))))
                    (projT1 arg_1__)
                    (projT2 arg_1__))))
           n0
           t0
           (existT _ (projT1 l3) (projT2 l3))) = n0)
     (fun l3 : {H1 : nat & vector b H1} =>
      [eta VectorDef.t_rect b
             (fun (n0 : nat) (t0 : vector b n0) =>
              0 = n0 ->
              projT1
                (VectorDef.t_rect a
                   (fun (n1 : nat) (_ : vector a n1) =>
                    {H2 : nat & vector b H2} -> {H2 : nat & vector (a * b) H2})
                   (fun _ : {H2 : nat & vector b H2} =>
                    existT _ 0 (nilV (a * b)))
                   (fun (h : a) (n1 : nat) (_ : vector a n1)
                      (H2 : {H2 : nat & vector b H2} ->
                            {H2 : nat & vector (a * b) H2})
                      (arg_1__ : {H3 : nat & vector b H3}) =>
                    existT _
                      (projT1
                         (VectorDef.t_rect b
                            (fun (n2 : nat) (_ : vector b n2) =>
                             {H3 : nat & vector (a * b) H3})
                            (existT _ 0 (nilV (a * b)))
                            (fun (h0 : b) (n2 : nat) 
                               (t2 : vector b n2)
                               (_ : {H3 : nat & vector (a * b) H3}) =>
                             existT _
                               (S (projT1 (H2 (existT _ n2 t2))))
                               (consV
                                  (projT1 (H2 (existT _ n2 t2)))
                                  (h, h0)
                                  (projT2 (H2 (existT _ n2 t2)))))
                            (projT1 arg_1__)
                            (projT2 arg_1__)))
                      (projT2
                         (VectorDef.t_rect b
                            (fun (n2 : nat) (_ : vector b n2) =>
                             {H3 : nat & vector (a * b) H3})
                            (existT _ 0 (nilV (a * b)))
                            (fun (h0 : b) (n2 : nat) 
                               (t2 : vector b n2)
                               (_ : {H3 : nat & vector (a * b) H3}) =>
                             existT _
                               (S (projT1 (H2 (existT _ n2 t2))))
                               (consV
                                  (projT1 (H2 (existT _ n2 t2)))
                                  (h, h0)
                                  (projT2 (H2 (existT _ n2 t2)))))
                            (projT1 arg_1__)
                            (projT2 arg_1__))))
                   0
                   (nilV a)
                   (existT _ n0 t0)) = 0) id
             (fun (_ : b) (n0 : nat) (t0 : vector b n0)
                (_ : 0 = n0 ->
                     projT1
                       (VectorDef.t_rect a
                          (fun (n1 : nat) (_ : vector a n1) =>
                           {H2 : nat & vector b H2} ->
                           {H2 : nat & vector (a * b) H2})
                          (fun _ : {H2 : nat & vector b H2} =>
                           existT _ 0 (nilV (a * b)))
                          (fun (h0 : a) (n1 : nat) (_ : vector a n1)
                             (H2 : {H2 : nat & vector b H2} ->
                                   {H2 : nat & vector (a * b) H2})
                             (arg_1__ : {H3 : nat & vector b H3}) =>
                           existT _
                             (projT1
                                (VectorDef.t_rect b
                                   (fun (n2 : nat) (_ : vector b n2) =>
                                    {H3 : nat & vector (a * b) H3})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h1 : b) (n2 : nat) 
                                      (t2 : vector b n2)
                                      (_ : {H3 : nat & vector (a * b) H3}) =>
                                    existT _
                                      (S (projT1 (H2 (existT _ n2 t2))))
                                      (consV
                                         (projT1 (H2 (existT _ n2 t2)))
                                         (h0, h1)
                                         (projT2 (H2 (existT _ n2 t2)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__)))
                             (projT2 (VectorDef.t_rect b
                                   (fun (n2 : nat) (_ : vector b n2) =>
                                    {H3 : nat & vector (a * b) H3})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h1 : b) (n2 : nat) 
                                      (t2 : vector b n2)
                                      (_ : {H3 : nat & vector (a * b) H3}) =>
                                    existT _
                                      (S (projT1 (H2 (existT _ n2 t2))))
                                      (consV
                                         (projT1 (H2 (existT _ n2 t2)))
                                         (h0, h1)
                                         (projT2 (H2 (existT _ n2 t2)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__))))
                          0
                          (nilV a)
                          (existT _ n0 t0)) = 0) 
                (_ : 0 = S n0) => erefl 0) (projT1 l3) 
             (projT2 l3)])
     (fun (h : a) (n0 : nat) (t0 : vector a n0)
        (H1 : forall l3 : {H1 : nat & vector b H1},
              n0 = projT1 l3 ->
              projT1
                (VectorDef.t_rect a
                   (fun (n1 : nat) (_ : vector a n1) =>
                    {H1 : nat & vector b H1} -> {H1 : nat & vector (a * b) H1})
                   (fun _ : {H1 : nat & vector b H1} =>
                    existT _ 0 (nilV (a * b)))
                   (fun (h0 : a) (n1 : nat) (_ : vector a n1)
                      (H1 : {H1 : nat & vector b H1} ->
                            {H1 : nat & vector (a * b) H1})
                      (arg_1__ : {H2 : nat & vector b H2}) =>
                    existT _
                      (projT1
                         (VectorDef.t_rect b
                            (fun (n2 : nat) (_ : vector b n2) =>
                             {H2 : nat & vector (a * b) H2})
                            (existT _ 0 (nilV (a * b)))
                            (fun (h1 : b) (n2 : nat) 
                               (t2 : vector b n2)
                               (_ : {H2 : nat & vector (a * b) H2}) =>
                             existT _
                               (S (projT1 (H1 (existT _ n2 t2))))
                               (consV
                                  (projT1 (H1 (existT _ n2 t2)))
                                  (h0, h1)
                                  (projT2 (H1 (existT _ n2 t2)))))
                            (projT1 arg_1__)
                            (projT2 arg_1__)))
                      (projT2
                         (VectorDef.t_rect b
                            (fun (n2 : nat) (_ : vector b n2) =>
                             {H2 : nat & vector (a * b) H2})
                            (existT _ 0 (nilV (a * b)))
                            (fun (h1 : b) (n2 : nat) 
                               (t2 : vector b n2)
                               (_ : {H2 : nat & vector (a * b) H2}) =>
                             existT _
                               (S (projT1 (H1 (existT _ n2 t2))))
                               (consV
                                  (projT1 (H1 (existT _ n2 t2)))
                                  (h0, h1)
                                  (projT2 (H1 (existT _ n2 t2)))))
                            (projT1 arg_1__)
                            (projT2 arg_1__))))
                   n0
                   t0
                   (existT _ (projT1 l3) (projT2 l3))) = n0)
        (l3 : {H2 : nat & vector b H2}) =>
      [eta VectorDef.t_rect b
             (fun (n1 : nat) (t1 : vector b n1) =>
              S n0 = n1 ->
              projT1
                (VectorDef.t_rect a
                   (fun (n2 : nat) (_ : vector a n2) =>
                    {H3 : nat & vector b H3} -> {H3 : nat & vector (a * b) H3})
                   (fun _ : {H3 : nat & vector b H3} =>
                    existT _ 0 (nilV (a * b)))
                   (fun (h0 : a) (n2 : nat) (_ : vector a n2)
                      (H3 : {H3 : nat & vector b H3} ->
                            {H3 : nat & vector (a * b) H3})
                      (arg_1__ : {H4 : nat & vector b H4}) =>
                    existT _
                      (projT1
                         (VectorDef.t_rect b
                            (fun (n3 : nat) (_ : vector b n3) =>
                             {H4 : nat & vector (a * b) H4})
                            (existT _ 0 (nilV (a * b)))
                            (fun (h1 : b) (n3 : nat) 
                               (t3 : vector b n3)
                               (_ : {H4 : nat & vector (a * b) H4}) =>
                             existT _
                               (S (projT1 (H3 (existT _ n3 t3))))
                               (consV
                                  (projT1 (H3 (existT _ n3 t3)))
                                  (h0, h1)
                                  (projT2 (H3 (existT _ n3 t3)))))
                            (projT1 arg_1__)
                            (projT2 arg_1__)))
                      (projT2
                         (VectorDef.t_rect b
                            (fun (n3 : nat) (_ : vector b n3) =>
                             {H4 : nat & vector (a * b) H4})
                            (existT _ 0 (nilV (a * b)))
                            (fun (h1 : b) (n3 : nat) 
                               (t3 : vector b n3)
                               (_ : {H4 : nat & vector (a * b) H4}) =>
                             existT _
                               (S (projT1 (H3 (existT _ n3 t3))))
                               (consV
                                  (projT1 (H3 (existT _ n3 t3)))
                                  (h0, h1)
                                  (projT2 (H3 (existT _ n3 t3)))))
                            (projT1 arg_1__)
                            (projT2 arg_1__))))
                   (S n0)
                   (consV n0 h t0)
                   (existT _ n1 t1)) = S n0)
             [eta hs_to_coq_lengths.Coq_Init_Logic_eq_sym nat
                    (S n0)
                    (projT1
                       (VectorDef.t_rect a
                          (fun (n1 : nat) (_ : vector a n1) =>
                           {H4 : nat & vector b H4} ->
                           {H4 : nat & vector (a * b) H4})
                          (fun _ : {H4 : nat & vector b H4} =>
                           existT _ 0 (nilV (a * b)))
                          (fun (h0 : a) (n1 : nat) (_ : vector a n1)
                             (H4 : {H4 : nat & vector b H4} ->
                                   {H4 : nat & vector (a * b) H4})
                             (arg_1__ : {H5 : nat & vector b H5}) =>
                           existT _
                             (projT1
                                (VectorDef.t_rect b
                                   (fun (n2 : nat) (_ : vector b n2) =>
                                    {H5 : nat & vector (a * b) H5})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h1 : b) (n2 : nat) 
                                      (t2 : vector b n2)
                                      (_ : {H5 : nat & vector (a * b) H5}) =>
                                    existT _
                                      (S (projT1 (H4 (existT _ n2 t2))))
                                      (consV
                                         (projT1 (H4 (existT _ n2 t2)))
                                         (h0, h1)
                                         (projT2 (H4 (existT _ n2 t2)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__)))
                             (projT2
                                (VectorDef.t_rect b
                                   (fun (n2 : nat) (_ : vector b n2) =>
                                    {H5 : nat & vector (a * b) H5})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h1 : b) (n2 : nat) 
                                      (t2 : vector b n2)
                                      (_ : {H5 : nat & vector (a * b) H5}) =>
                                    existT _
                                      (S (projT1 (H4 (existT _ n2 t2))))
                                      (consV
                                         (projT1 (H4 (existT _ n2 t2)))
                                         (h0, h1)
                                         (projT2 (H4 (existT _ n2 t2)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__))))
                          (S n0)
                          (consV n0 h t0)
                          (existT _ 0 (nilV b))))]
             (fun (h0 : b) (n1 : nat) (t1 : vector b n1)
                (_ : S n0 = n1 ->
                     projT1
                       (VectorDef.t_rect a
                          (fun (n2 : nat) (_ : vector a n2) =>
                           {H3 : nat & vector b H3} ->
                           {H3 : nat & vector (a * b) H3})
                          (fun _ : {H3 : nat & vector b H3} =>
                           existT _ 0 (nilV (a * b)))
                          (fun (h1 : a) (n2 : nat) (_ : vector a n2)
                             (H3 : {H3 : nat & vector b H3} ->
                                   {H3 : nat & vector (a * b) H3})
                             (arg_1__ : {H4 : nat & vector b H4}) =>
                           existT _
                             (projT1
                                (VectorDef.t_rect b
                                   (fun (n3 : nat) (_ : vector b n3) =>
                                    {H4 : nat & vector (a * b) H4})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h2 : b) (n3 : nat) 
                                      (t3 : vector b n3)
                                      (_ : {H4 : nat & vector (a * b) H4}) =>
                                    existT _
                                      (S (projT1 (H3 (existT _ n3 t3))))
                                      (consV
                                         (projT1 (H3 (existT _ n3 t3)))
                                         (h1, h2)
                                         (projT2 (H3 (existT _ n3 t3)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__)))
                             (projT2
                                (VectorDef.t_rect b
                                   (fun (n3 : nat) (_ : vector b n3) =>
                                    {H4 : nat & vector (a * b) H4})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h2 : b) (n3 : nat) 
                                      (t3 : vector b n3)
                                      (_ : {H4 : nat & vector (a * b) H4}) =>
                                    existT _
                                      (S (projT1 (H3 (existT _ n3 t3))))
                                      (consV
                                         (projT1 (H3 (existT _ n3 t3)))
                                         (h1, h2)
                                         (projT2 (H3 (existT _ n3 t3)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__))))
                          (S n0)
                          (consV n0 h t0)
                          (existT _ n1 t1)) = S n0) =>
              (eq_ind (S n0)
                 (fun y : nat =>
                  y = S n1 ->
                  projT1
                    (VectorDef.t_rect a
                       (fun (n2 : nat) (_ : vector a n2) =>
                        {H4 : nat & vector b H4} ->
                        {H4 : nat & vector (a * b) H4})
                       (fun _ : {H4 : nat & vector b H4} =>
                        existT _ 0 (nilV (a * b)))
                       (fun (h1 : a) (n2 : nat) (_ : vector a n2)
                          (H4 : {H4 : nat & vector b H4} ->
                                {H4 : nat & vector (a * b) H4})
                          (arg_1__ : {H5 : nat & vector b H5}) =>
                        existT _
                          (projT1
                             (VectorDef.t_rect b
                                (fun (n3 : nat) (_ : vector b n3) =>
                                 {H5 : nat & vector (a * b) H5})
                                (existT _ 0 (nilV (a * b)))
                                (fun (h2 : b) (n3 : nat) 
                                   (t3 : vector b n3)
                                   (_ : {H5 : nat & vector (a * b) H5}) =>
                                 existT _
                                   (S (projT1 (H4 (existT _ n3 t3))))
                                   (consV
                                      (projT1 (H4 (existT _ n3 t3)))
                                      (h1, h2)
                                      (projT2 (H4 (existT _ n3 t3)))))
                                (projT1 arg_1__)
                                (projT2 arg_1__)))
                          (projT2
                             (VectorDef.t_rect b
                                (fun (n3 : nat) (_ : vector b n3) =>
                                 {H5 : nat & vector (a * b) H5})
                                (existT _ 0 (nilV (a * b)))
                                (fun (h2 : b) (n3 : nat) 
                                   (t3 : vector b n3)
                                   (_ : {H5 : nat & vector (a * b) H5}) =>
                                 existT _
                                   (S (projT1 (H4 (existT _ n3 t3))))
                                   (consV
                                      (projT1 (H4 (existT _ n3 t3)))
                                      (h1, h2)
                                      (projT2 (H4 (existT _ n3 t3)))))
                                (projT1 arg_1__)
                                (projT2 arg_1__))))
                       (S n0)
                       (consV n0 h t0)
                       (existT _ (S n1) (consV n1 h0 t1))) =
                  S n0)
                 (fun H4 : S n0 = S n1 =>
                  hs_to_coq_lengths.Coq_Init_Logic_eq_ind nat
                    n0
                    (fun _ : nat =>
                     projT1
                       (VectorDef.t_rect a
                          (fun (n3 : nat) (_ : vector a n3) =>
                           {H5 : nat & vector b H5} ->
                           {H5 : nat & vector (a * b) H5})
                          (fun _ : {H5 : nat & vector b H5} =>
                           existT _ 0 (nilV (a * b)))
                          (fun (h1 : a) (n3 : nat) (_ : vector a n3)
                             (H5 : {H5 : nat & vector b H5} ->
                                   {H5 : nat & vector (a * b) H5})
                             (arg_1__ : {H6 : nat & vector b H6}) =>
                           existT _
                             (projT1
                                (VectorDef.t_rect b
                                   (fun (n4 : nat) (_ : vector b n4) =>
                                    {H6 : nat & vector (a * b) H6})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h2 : b) (n4 : nat) 
                                      (t3 : vector b n4)
                                      (_ : {H6 : nat & vector (a * b) H6}) =>
                                    existT _
                                      (S (projT1 (H5 (existT _ n4 t3))))
                                      (consV
                                         (projT1 (H5 (existT _ n4 t3)))
                                         (h1, h2)
                                         (projT2 (H5 (existT _ n4 t3)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__)))
                             (projT2
                                (VectorDef.t_rect b
                                   (fun (n4 : nat) (_ : vector b n4) =>
                                    {H6 : nat & vector (a * b) H6})
                                   (existT _ 0 (nilV (a * b)))
                                   (fun (h2 : b) (n4 : nat) 
                                      (t3 : vector b n4)
                                      (_ : {H6 : nat & vector (a * b) H6}) =>
                                    existT _
                                      (S (projT1 (H5 (existT _ n4 t3))))
                                      (consV
                                         (projT1 (H5 (existT _ n4 t3)))
                                         (h1, h2)
                                         (projT2 (H5 (existT _ n4 t3)))))
                                   (projT1 arg_1__)
                                   (projT2 arg_1__))))
                          (S n0)
                          (consV n0 h t0)
                          (existT _ (S n1) (consV n1 h0 t1))) =
                     S n0)
                    (hs_to_coq_lengths.Coq_Init_Logic_eq_trans nat
                       (S
                          (projT1
                             (VectorDef.t_rect a
                                (fun (n2 : nat) (_ : vector a n2) =>
                                 {H5 : nat & vector b H5} ->
                                 {H5 : nat & vector (a * b) H5})
                                (fun _ : {H5 : nat & vector b H5} =>
                                 existT _ 0 (nilV (a * b)))
                                (fun (h1 : a) (n2 : nat) 
                                   (_ : vector a n2)
                                   (H5 : {H5 : nat & vector b H5} ->
                                         {H5 : nat & vector (a * b) H5})
                                   (arg_1__ : {H6 : nat & vector b H6}) =>
                                 existT _
                                   (projT1
                                      (VectorDef.t_rect b
                                         (fun (n3 : nat) (_ : vector b n3) =>
                                          {H6 : nat & vector (a * b) H6})
                                         (existT _ 0 (nilV (a * b)))
                                         (fun (h2 : b) 
                                            (n3 : nat) 
                                            (t3 : vector b n3)
                                            (_ : {H6 : nat & vector (a * b) H6})
                                          =>
                                          existT _
                                            (S (projT1 (H5 (existT _ n3 t3))))
                                            (consV
                                               (projT1 (H5 (existT _ n3 t3)))
                                               (h1, h2)
                                               (projT2 (H5 (existT _ n3 t3)))))
                                         (projT1 arg_1__)
                                         (projT2 arg_1__)))
                                   (projT2
                                      (VectorDef.t_rect b
                                         (fun (n3 : nat) (_ : vector b n3) =>
                                          {H6 : nat & vector (a * b) H6})
                                         (existT _ 0 (nilV (a * b)))
                                         (fun (h2 : b) 
                                            (n3 : nat) 
                                            (t3 : vector b n3)
                                            (_ : {H6 : nat & vector (a * b) H6})
                                          =>
                                          existT _
                                            (S (projT1 (H5 (existT _ n3 t3))))
                                            (consV
                                               (projT1 (H5 (existT _ n3 t3)))
                                               (h1, h2)
                                               (projT2 (H5 (existT _ n3 t3)))))
                                         (projT1 arg_1__)
                                         (projT2 arg_1__))))
                                n0
                                t0
                                (existT _ n1 t1))))
                       (S
                          (projT1
                             (VectorDef.t_rect a
                                (fun (n2 : nat) (_ : vector a n2) =>
                                 {H5 : nat & vector b H5} ->
                                 {H5 : nat & vector (a * b) H5})
                                (fun _ : {H5 : nat & vector b H5} =>
                                 existT _ 0 (nilV (a * b)))
                                (fun (h1 : a) (n2 : nat) 
                                   (_ : vector a n2)
                                   (H5 : {H5 : nat & vector b H5} ->
                                         {H5 : nat & vector (a * b) H5})
                                   (arg_1__ : {H6 : nat & vector b H6}) =>
                                 existT _
                                   (projT1
                                      (VectorDef.t_rect b
                                         (fun (n3 : nat) (_ : vector b n3) =>
                                          {H6 : nat & vector (a * b) H6})
                                         (existT _ 0 (nilV (a * b)))
                                         (fun (h2 : b) 
                                            (n3 : nat) 
                                            (t3 : vector b n3)
                                            (_ : {H6 : nat & vector (a * b) H6})
                                          =>
                                          existT _
                                            (S (projT1 (H5 (existT _ n3 t3))))
                                            (consV
                                               (projT1 (H5 (existT _ n3 t3)))
                                               (h1, h2)
                                               (projT2 (H5 (existT _ n3 t3)))))
                                         (projT1 arg_1__)
                                         (projT2 arg_1__)))
                                   (projT2
                                      (VectorDef.t_rect b
                                         (fun (n3 : nat) (_ : vector b n3) =>
                                          {H6 : nat & vector (a * b) H6})
                                         (existT _ 0 (nilV (a * b)))
                                         (fun (h2 : b) 
                                            (n3 : nat) 
                                            (t3 : vector b n3)
                                            (_ : {H6 : nat & vector (a * b) H6})
                                          =>
                                          existT _
                                            (S (projT1 (H5 (existT _ n3 t3))))
                                            (consV
                                               (projT1 (H5 (existT _ n3 t3)))
                                               (h1, h2)
                                               (projT2 (H5 (existT _ n3 t3)))))
                                         (projT1 arg_1__)
                                         (projT2 arg_1__))))
                                n0
                                t0
                                (existT _ n1 t1))))
                       (S n0)
                       (hs_to_coq_lengths.Coq_Init_Logic_f_equal 
                          (nat -> nat) nat
                          (@^~ (projT1
                                  (VectorDef.t_rect a
                                     (fun (n2 : nat) (_ : vector a n2) =>
                                      {H5 : nat & vector b H5} ->
                                      {H5 : nat & vector (a * b) H5})
                                     (fun _ : {H5 : nat & vector b H5} =>
                                      existT _ 0 (nilV (a * b)))
                                     (fun (h1 : a) (n2 : nat) 
                                        (_ : vector a n2)
                                        (H5 : {H5 : nat & vector b H5} ->
                                              {H5 : nat & vector (a * b) H5})
                                        (arg_1__ : {H6 : nat & vector b H6}) =>
                                      existT _
                                        (projT1
                                           (VectorDef.t_rect b
                                              (fun (n3 : nat) (_ : vector b n3)
                                               => {H6 : nat & vector (a * b) H6})
                                              (existT _ 0  (nilV (a * b)))
                                              (fun (h2 : b) 
                                                 (n3 : nat) 
                                                 (t3 : vector b n3)
                                                 (_ : 
                                                  {H6 : nat & 
                                                  vector (a * b) H6}) =>
                                               existT _
                                                 (S (projT1 (H5 (existT _ n3 t3))))
                                                 (consV
                                                    (projT1 (H5 (existT _ n3 t3)))
                                                    (h1, h2)
                                                    (projT2 (H5 (existT _ n3 t3)))))
                                              (projT1 arg_1__)
                                              (projT2 arg_1__)))
                                        (projT2
                                           (VectorDef.t_rect b
                                              (fun (n3 : nat) (_ : vector b n3)
                                               => {H6 : nat & vector (a * b) H6})
                                              (existT _ 0  (nilV (a * b)))
                                              (fun (h2 : b) 
                                                 (n3 : nat) 
                                                 (t3 : vector b n3)
                                                 (_ : 
                                                  {H6 : nat & 
                                                  vector (a * b) H6}) =>
                                               existT _
                                                 (S (projT1 (H5 (existT _ n3 t3))))
                                                 (consV
                                                    (projT1 (H5 (existT _ n3 t3)))
                                                    (h1, h2)
                                                    (projT2 (H5 (existT _ n3 t3)))))
                                              (projT1 arg_1__)
                                              (projT2 arg_1__))))
                                     n0
                                     t0
                                     (existT _ n1 t1)))) S S
                          (erefl S))
                       (hs_to_coq_lengths.Coq_Init_Logic_f_equal nat nat S
                          (projT1
                             (VectorDef.t_rect a
                                (fun (n2 : nat) (_ : vector a n2) =>
                                 {H5 : nat & vector b H5} ->
                                 {H5 : nat & vector (a * b) H5})
                                (fun _ : {H5 : nat & vector b H5} =>
                                 existT _ 0 (nilV (a * b)))
                                (fun (h1 : a) (n2 : nat) 
                                   (_ : vector a n2)
                                   (H5 : {H5 : nat & vector b H5} ->
                                         {H5 : nat & vector (a * b) H5})
                                   (arg_1__ : {H6 : nat & vector b H6}) =>
                                 existT _
                                   (projT1
                                      (VectorDef.t_rect b
                                         (fun (n3 : nat) (_ : vector b n3) =>
                                          {H6 : nat & vector (a * b) H6})
                                         (existT _ 0 (nilV (a * b)))
                                         (fun (h2 : b) 
                                                 (n3 : nat) 
                                                 (t3 : vector b n3)
                                                 (_ : 
                                                  {H6 : nat & 
                                                  vector (a * b) H6}) =>
                                               existT _
                                                 (S (projT1 (H5 (existT _ n3 t3))))
                                                 (consV
                                                    (projT1 (H5 (existT _ n3 t3)))
                                                    (h1, h2)
                                                    (projT2 (H5 (existT _ n3 t3)))))
                                         (projT1 arg_1__)
                                         (projT2 arg_1__)))
                                   (projT2
                                      (VectorDef.t_rect b
                                         (fun (n3 : nat) (_ : vector b n3) =>
                                          {H6 : nat & vector (a * b) H6})
                                         (existT _ 0 (nilV (a * b)))
                                         (fun (h2 : b) 
                                                 (n3 : nat) 
                                                 (t3 : vector b n3)
                                                 (_ : 
                                                  {H6 : nat & 
                                                  vector (a * b) H6}) =>
                                               existT _
                                                 (S (projT1 (H5 (existT _ n3 t3))))
                                                 (consV
                                                    (projT1 (H5 (existT _ n3 t3)))
                                                    (h1, h2)
                                                    (projT2 (H5 (existT _ n3 t3)))))
                                         (projT1 arg_1__)
                                         (projT2 arg_1__))))
                                n0
                                t0
                                (existT _ n1 t1)))
                          n0
                          (H1 (existT _ n1 t1)
                             (hs_to_coq_lengths.Coq_Init_Logic_f_equal nat nat
                                [eta nat_rec (fun _ : nat => nat)
                                       (VectorDef.t_rect a
                                          (fun (n2 : nat) (_ : vector a n2) =>
                                           nat) 0
                                          (fun (_ : a) 
                                             (n2 : nat) 
                                             (_ : vector a n2) => [eta S])
                                          n0
                                          t0)
                                       (fun n2 _ : nat => n2)]
                                (S n0) 
                                (S n1) H4)))) n1
                    (hs_to_coq_lengths.Coq_Init_Logic_f_equal nat nat
                       [eta nat_rec (fun _ : nat => nat)
                              (VectorDef.t_rect a
                                 (fun (n2 : nat) (_ : vector a n2) => nat) 0
                                 (fun (_ : a) (n2 : nat) (_ : vector a n2) =>
                                  [eta S]) n0
                                 t0)
                              (fun n2 _ : nat => n2)]
                       (S n0) 
                       (S n1) H4)) (S n1))^~ (erefl (S n1))) 
             (projT1 l3) (projT2 l3)])
     (projT1 l1)
     (projT2 l1)
     (existT _ (projT1 l2) (projT2 l2))
     (hs_to_coq_lengths.Coq_Init_Logic_eq_trans nat (projT1 l1) n 
        (projT1 l2) H
        (hs_to_coq_lengths.Coq_Init_Logic_eq_sym nat (projT1 l2) n H0))) n H)
   in
(projT2
       (hs_to_coqV_p.zip a b
         (existT _ n v1)
         (existT _ n v2))).

(* TODO why is simplifying projections of existentials not working anymore? terms are ugly *)

(*
 * Lifting along this equivalence will soon be automated, but for now apply
 * the above functions by hand:
 *)
Program Definition zip:
  forall {A B : Type} {n : nat},
    vector A n ->
    vector B n ->
    vector (A * B) n.
Proof.
  intros A B n v1 v2. apply unpack_vector. apply packed_vector.zip.
  - apply (unpack_vector_inv A n v1).
  - apply (unpack_vector_inv B n v2).
Defined.

Program Definition zip_with:
  forall {A B C : Type} (f : A -> B -> C) {n : nat},
    vector A n ->
    vector B n ->
    vector C n.
Proof.
  intros A B C f n v1 v2. apply unpack_vector. apply (packed_vector.zip_with A B).
  - apply f.
  - apply (unpack_vector_inv A n v1).
  - apply (unpack_vector_inv B n v2).
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

