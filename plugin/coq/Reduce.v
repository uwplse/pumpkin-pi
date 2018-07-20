Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.
Require Import Lift.

(* --- Simple functions on lists --- *)

(*
 * tl and tl_vect
 *)

Ornamental Reduction tl_vect_red from tl_vect_auto using orn_list_vector orn_list_vector_inv.

Print tl_vect_red_index.

Theorem test_tl_vect:
  forall (A : Type) (pv : packed_vector A),
    tl_vect_packed A pv = tl_vect_red A pv.
Proof.
  intros. reflexivity.
Qed.

Ornamental Reduction tl_red from tl_auto using orn_list_vector_inv orn_list_vector.

Theorem test_tl:
  forall (A : Type) (l : list A),
    tl A l = tl_red A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * Application
 *)

(* In *)

Ornamental Reduction In_vect_red from In_vect_auto using orn_list_vector orn_list_vector_inv.

Theorem test_in_vect:
  forall (A : Type) (a : A) (pv : packed_vector A),
    In_vect A a pv = In_vect_red A a pv.
Proof.
  intros. reflexivity.
Qed.

Ornamental Reduction In_red from In_auto using orn_list_vector_inv orn_list_vector.

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

Ornamental Reduction app_nil_r_vect_red from app_nil_r_vect_auto using orn_list_vector orn_list_vector_inv.
Ornamental Reduction app_nil_r_red from app_nil_r_auto using orn_list_vector_inv orn_list_vector.

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
(*
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
    orn_list_vector_inv A (append_vect A (orn_list_vector A l1) (orn_list_vector A l2)) = append_red A l1 l2.
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
Qed.*)

(* app_nil_r on flectors *)

Ornamental Reduction app_nil_r_vectF_red from app_nil_r_vectF_auto using orn_flist_flector_nat orn_flist_flector_nat_inv.

(* TODO opposite direction *)

(* 
 * NOTE: The app_nil_r case needs an automatic proof of indices, which it doesn't have yet.
 * The proof should be automatically derivable from app_nil_r, but the tool only tries to infer an indexing
 * function in the case that we lift back to vectors, like with append_vect and tl_vect.
 * Below we manually derive the proofs we would want, so we can implement this later (TODO).
 *)

Ornamental Reduction in_split_vect_red from in_split_vect_auto using orn_list_vector orn_list_vector_inv.

(* TODO test *)
(* TODO opposite direction too once it's done *)

(* needed for porting discriminate proofs *)
Ornamental Reduction is_cons_vect_red from is_cons_vect_auto using orn_list_vector orn_list_vector_inv.

(* TODO test, opposite *)

Ornamental Reduction hd_error_some_nil_vect_red from hd_error_some_nil_vect_auto using orn_list_vector orn_list_vector_inv.

(* TODO test, opposite *)

(* --- Unimplemented ideas --- *)

(* TODO more proofs *)

(* TODO other types besides lists *)
