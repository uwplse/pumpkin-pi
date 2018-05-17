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
 * hd and hd_vect for flectors
 *)

Reduce ornament orn_flist_flector_nat orn_flist_flector_nat_inv in hd_vectF_auto as hd_vectF_red.

Theorem test_hd_vectF:
  forall (default : nat) (pv : sigT natFlector.flector),
    hd_vect_packedF default pv = hd_vectF_red default pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_flist_flector_nat_inv orn_flist_flector_nat in hd_autoF as hd_redF.

Theorem test_hdF:
  forall (default : nat) (l : natFlector.flist),
    hdF default l = hd_redF default l.
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

Print tl_vect_red_index.

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

Theorem test_append_vect_red_index:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = plus_vect_exp A pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Theorem test_append_vect_red_index_correct_unpacked:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = plus_vect A (projT1 pv1) (projT2 pv1) (projT1 pv2) (projT2 pv2).
Proof.  
  intros. induction pv1. induction p.
  - reflexivity.
  - simpl. simpl in IHp. rewrite <- IHp. reflexivity.
Qed.

Theorem test_append_vect_red_index_correct:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_red_index A pv1 pv2 = projT1 (append_vect_red A pv1 pv2).
Proof.
  intros. induction pv1. induction p.
  - reflexivity.
  - rewrite test_append_vect_red_index_correct_unpacked in IHp.
    rewrite test_append_vect_red_index_correct_unpacked.
    simpl. simpl in IHp. rewrite IHp. reflexivity.
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

(* Append with flector *)

Reduce ornament orn_flist_flector_nat orn_flist_flector_nat_inv in append_vectF_auto as append_vectF_red. 

Definition addEvensF (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector) :=
  natFlector.flector_rect 
    (fun (n : nat) (_ : natFlector.flector n) => nat) 
    (projT1 pv2)
    (fun (n : nat) (a : natFlector.A) (f : natFlector.flector n) (IH : nat) =>
      natFlector.SIfEven a IH)
    (projT1 pv1) 
    (projT2 pv1).

(* TODO the index is correct, but reduces SIfEven which we would rather it keep in-tact as in addEvensF *)
Theorem test_append_vect_red_indexF:
  forall (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector),
    append_vectF_red_index pv1 pv2 = addEvensF pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Theorem test_append_vectF:
  forall (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector),
    append_vect_packedF pv1 pv2 = append_vectF_red pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_flist_flector_nat_inv orn_flist_flector_nat in appendF_auto as appendF_red.

Theorem test_appendF :
  forall (l1 : natFlector.flist) (l2 : natFlector.flist),
    appendF l1 l2  = appendF_red l1 l2.
Proof.
  intros. reflexivity.
Qed.

(* In *)

Reduce ornament orn_list_vector orn_list_vector_inv in In_vect_auto as In_vect_red.

Theorem test_in_vect:
  forall (A : Type) (a : A) (pv : packed_vector A),
    In_vect A a pv = In_vect_red A a pv.
Proof.
  intros. reflexivity.
Qed.

Reduce ornament orn_list_vector_inv orn_list_vector in In_auto as In_red.

Theorem test_in:
  forall (A : Type) (a : A) (l : list A),
    In A a l = In_red A a l.
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

Theorem app_coh_inv:
  forall (A : Type) (l1 : list A) (l2 : list A),
    orn_list_vector_inv A (append_vect_packed A (orn_list_vector A l1) (orn_list_vector A l2)) = append_red A l1 l2.
Proof.
  intros. induction l1.
  - apply coh_list.
  - simpl. apply eq_cons with (a := a) in IHl1. apply IHl1. 
Qed.

(*
 * NOTE: The above proofs have predictable structures. Especially consider eq_pv_cons and how it is used
 * in inductive hypotheses here. Can we derive these automatically? Or could we, if we had to?
 *)

(*
 * Using that, we show the theorem we actually want. Again, the intermediate proofs will eventually
 * be obsolete and we'll produce this term directly, though maybe this tells us more about
 * how to compose what we have with some function to get the higher-lifted version:
 *)

(* TODO move this *)
Lemma conv:
  forall (A : Type) (P : A -> Type) (s : sigT P),
    s = existT P (projT1 s) (projT2 s).
Proof.
  intros. induction s. reflexivity.
Qed. 

Theorem test_app_nil_r_vect:
  forall (A : Type) (pv : packed_vector A),
    append_vect_red A pv (existT (vector A) 0 (nilV A)) = pv.
Proof.
  intros.
  rewrite (conv nat (vector A) pv). 
  rewrite <- app_coh. rewrite app_nil_r_vect_red. apply coh_vect_packed. 
Qed.

(* 
 * NOTE: We can simplify the above term at some point, which will give more clarity on
 * the lifted term we're looking for.
 *)

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  intros. rewrite <- app_coh_inv. unfold orn_list_vector. rewrite app_nil_r_red. apply coh_list.
Qed.

(* app_nil_r on flectors *)

Reduce ornament orn_flist_flector_nat orn_flist_flector_nat_inv in app_nil_r_vectF_auto as app_nil_r_vectF_red.

(* TODO opposite direction *)

(* 
 * NOTE: The app_nil_r case needs an automatic proof of indices, which it doesn't have yet.
 * The proof should be automatically derivable from app_nil_r, but the tool only tries to infer an indexing
 * function in the case that we lift back to vectors, like with append_vect and tl_vect.
 * Below we manually derive the proofs we would want, so we can implement this later (TODO).
 *)

Reduce ornament orn_list_vector orn_list_vector_inv in in_split_vect_auto as in_split_vect_red.

(* TODO test *)
(* TODO opposite direction too once it's done *)

(* needed for porting discriminate proofs *)
Reduce ornament orn_list_vector orn_list_vector_inv in is_cons_vect_auto as is_cons_vect_red.

(* TODO test, opposite *)

Reduce ornament orn_list_vector orn_list_vector_inv in hd_error_some_nil_vect_auto as hd_error_some_nil_vect_red.

(* TODO test, opposite *)

(* --- Unimplemented ideas --- *)

(* TODO more proofs *)

(* TODO other types besides lists *)