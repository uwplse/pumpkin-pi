Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(* --- Simple functions on lists --- *)

(*
 * hd and hd_vect
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_auto as hd_vect_red.

Theorem test_hd_vect:
  forall (A : Type) (default : A) (pv : packed_vector A),
    hd_vect_packed A default pv = hd_vect_red A default pv.
Proof.
  intros. reflexivity.
Qed.

(* TODO test relation to old version, eventually branch & simplify etc *)
(* TODO generate coherence proof if asked for *)

Reduce ornament orn_list_vector_inv orn_list_vector in hd_auto as hd_red.

Theorem test_hd:
  forall (A : Type) (default : A) (l : list A),
    hd A default l = hd_red A default l.
Proof.
  intros. reflexivity.
Qed.

(*
 * hd_error and hd_vect_error
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_vect_error_auto as hd_vect_error_red.

Theorem test_hd_vect_error:
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error_packed A pv = hd_vect_error_red A pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in hd_error_auto as hd_error_red.

Theorem test_hd_error:
  forall (A : Type) (l : list A),
    hd_error A l = hd_error_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * tl and tl_vect
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in tl_vect_auto as tl_vect_red.

Theorem test_tl_vect:
  forall (A : Type) (pv : packed_vector A),
    tl_vect_packed A pv = tl_vect_red A pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in tl_auto as tl_red.

Theorem test_tl:
  forall (A : Type) (l : list A),
    tl A l = tl_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * Application
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in append_vect_auto as append_vect_red. 

(* for understanding reduction, TODO move *)
Definition append_vect_packed_pre_red (A : Type) (pv1 pv2 : packed_vector A) :=
sigT_rect (fun _ : {n : nat & vector A n} => {n : nat & vector A n})
  (fun (n : nat) (v : vector A n) =>
   vector_rect 
     A 
     (fun (n0 : nat) (_ : vector A n0) => {n1 : nat & vector A n1}) 
     pv2
     (fun (n0 : nat) (a : A) (v : vector A n0) (IH : {n1 : nat & vector A n1}) =>
       orn_list_vector 
         A 
         ((fun (al : A) (l : list A) (IHl : list A) => al :: IHl) 
          a 
          (orn_list_vector_inv A (existT (vector A) n0 v)) 
          (orn_list_vector_inv A IH)))
      (*existT (vector A) (S (projT1 IH)) (consV A (projT1 IH) a (projT2 IH))*) 
     n v) pv1.

Theorem test_append_vect_red_index:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = plus_vect_exp A pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

(* Some basic sanity checking, should auto-generate at some point*)
Theorem test_append_vect_red_index_correct_unpacked:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = plus_vect A (projT1 pv1) (projT2 pv1) (projT1 pv2) (projT2 pv2).
Proof.  
  intros. induction pv1. induction p.
  - reflexivity.
  - simpl. simpl in IHp. rewrite IHp. reflexivity.
Qed.

Theorem test_append_vect_red_index_correct:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = projT1 (append_vect_red A pv1 pv2).
Proof.
  intros. induction pv1. induction p.
  - reflexivity.
  - rewrite test_append_vect_red_index_correct_unpacked. 
    unfold plus_vect. simpl. simpl in IHp. rewrite IHp. reflexivity.
Qed.

Theorem test_append_vect:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_packed A pv1 pv2  = append_vect_red A pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in append_auto as append_red.

Theorem test_append :
  forall (A : Type) (l1 : list A) (l2 : list A),
    append A l1 l2  = append_red A l1 l2.
Proof.
  intros. reflexivity.
Qed.

(* --- Proofs --- *)

(* 
 * app_nil_r is a proof that only exists inside of the sigma 
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in app_nil_r_vect_auto as app_nil_r_vect_red.

Reduce ornament orn_list_vector_inv orn_list_vector in app_nil_r_auto as app_nil_r_red.

(* 
 * NOTE: We don't yet have higher lifting implemented; these proofs don't know we've 
 * lifted append, so they still append in terms of the forgetful/promotion function.
 * When we implement a database, we can further handle this step to get the types we really want.
 * For now, we prove equality reflexively to the not higher-lifted version from Apply.v (TODO).
 *)

Theorem test_app_nil_r_vect_lower:
  forall (A : Type) (pv : packed_vector A),
    app_nil_r_vect_red A pv = app_nil_r_vect_packed_lower A pv.
Proof.
  intros. reflexivity.
Qed.

Theorem test_app_nil_r_lower:
  forall (A : Type) (l : list A),
    app_nil_r_red A l  = app_nil_r_lower A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * Next, we prove propositional equality to the higher-lifted version; eventually,
 * these proofs will be obsolete:
 *)
Lemma coh_vect_packed:
  forall (A : Type) (pv : packed_vector A),
    orn_list_vector A (orn_list_vector_inv A pv) = pv.
Proof.
  intros. induction pv. induction p.
  - reflexivity.
  - simpl. apply eq_pv_cons with (a := a) in IHp. apply IHp. 
Qed.

Lemma coh_list:
  forall (A : Type) (l : list A),
    orn_list_vector_inv A (orn_list_vector A l) = l.
Proof.
  intros. induction l. 
  - reflexivity.
  - simpl. apply eq_cons with (a := a) in IHl. apply IHl. 
Qed.

Lemma app_coh:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    orn_list_vector A (append A (orn_list_vector_inv A pv1) (orn_list_vector_inv A pv2)) = append_vect_red A pv1 pv2.
Proof.
  intros. induction pv1. induction p.
  - apply coh_vect_packed. 
  - simpl. apply eq_pv_cons with (a := a) in IHp. apply IHp. 
Qed.

Lemma unpack_rect:
  forall (A : Type) (P : forall (n : nat), vector A n -> Type) pnil pcons (pv : packed_vector A),
    vector_rect A P pnil pcons (projT1 pv) (projT2 pv) =
    sigT_rect 
      (fun (pv : sigT (vector A)) => P (projT1 pv) (projT2 pv)) 
      (fun (n : nat) (v : vector A n) =>
         vector_rect A P pnil pcons n v)
      pv.
Proof.
  intros. induction pv. auto.
Qed.

Theorem app_coh_inv:
  forall (A : Type) (l1 : list A) (l2 : list A),
    orn_list_vector_inv A (append_vect_packed A (orn_list_vector A l1) (orn_list_vector A l2)) = append_red A l1 l2.
Proof.
  intros. induction l1.
  - apply coh_list.
  - simpl. apply eq_cons with (a := a) in IHl1. rewrite unpack_rect. apply IHl1. 
Qed.

(*
 * NOTE: Note the unpack_rect thing which mattered a lot. Can we internalize this
 * into an induction principle itself?
 *)

(*
 * NOTE: The above proofs have predictable structures. Especially consider eq_pv_cons and how it is used
 * in inductive hypotheses here. Can we derive these automatically? Or could we, if we had to?
 *)

(*
 * Using that, we show the theorem we actually want. Again, the intermediate proofs will eventually
 * be obsolete and we'll produce this term directly, though maybe this tells us more about
 * how to compose what we have with some function to get the higher-lifted version:
 *)

Theorem test_app_nil_r_vect:
  forall (A : Type) (pv : packed_vector A),
    append_vect_red A pv (existT (vector A) 0 (nilV A)) = pv.
Proof.
  intros. rewrite <- app_coh. rewrite app_nil_r_vect_red. apply coh_vect_packed. 
Qed.

(* 
 * NOTE: We can simplify the above term at some point, which will give more clarity on
 * the lifted term we're looking for.
 *)

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  intros. rewrite <- app_coh_inv. rewrite app_nil_r_red. apply coh_list.
Qed.

(* 
 * NOTE: The app_nil_r case needs an automatic proof of indices, which it doesn't have yet.
 * The proof should be automatically derivable from app_nil_r, but the tool only tries to infer an indexing
 * function in the case that we lift back to vectors, like with append_vect and tl_vect.
 * Below we manually derive the proofs we would want, so we can implement this later (TODO).
 *)

(* --- Unimplemented ideas --- *)

(* TODO more proofs *)

(* TODO other types besides lists *)