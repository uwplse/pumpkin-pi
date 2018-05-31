Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.
Require Import Reduce.

(*
 * Tests for higher lifting.
 *)

Print app_nil_r.

Print app_nil_r_vect_red.

Higher lift orn_list_vector orn_list_vector_inv in app_nil_r_vect_red as app_nil_r_vect_red_higher.

Print app_nil_r_vect_red_higher.

Theorem test_app_nil_r_vect_exact:
  forall (A : Type) (pv : sigT (vector A)),
    append_vect_red A (existT (vector A) (projT1 pv) (projT2 pv)) (existT (vector A) 0 (nilV A)) = (existT (vector A) (projT1 pv) (projT2 pv)).
Proof.
  exact app_nil_r_vect_red_higher.
Qed.

(*
 * Convert between representations, should do automatically eventually
 *)
Lemma conv:
  forall (A : Type) (P : A -> Type) (s : sigT P),
    s = existT P (projT1 s) (projT2 s).
Proof.
  intros. induction s. reflexivity.
Qed. 

(*
 * TODO now that we are using eliminators instead, need to transfer proof 
 * over to better type. Should do this automatically eventually.
 *)
Theorem test_app_nil_r_vect:
  forall (A : Type) (pv : sigT (vector A)),
    append_vect_red A pv (existT (vector A) 0 (nilV A)) = pv.
Proof.
  intros.
  rewrite (conv nat (vector A) pv).
  apply app_nil_r_vect_red_higher.
Qed.

Higher lift orn_list_vector_inv orn_list_vector in app_nil_r_red as app_nil_r_red_higher.

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  exact app_nil_r_red_higher.
Qed.

(* over flectors *)

Print app_nil_r_vectF_red.
Higher lift orn_flist_flector_nat orn_flist_flector_nat_inv in app_nil_r_vectF_red as app_nil_r_vectF_red_higher.

Print app_nil_r_vectF_red_higher.

Theorem test_app_nil_r_vectF_exact:
  forall (pv : sigT natFlector.flector),
    append_vectF_red (existT natFlector.flector (projT1 pv) (projT2 pv)) (existT natFlector.flector 0 natFlector.nilFV) = (existT natFlector.flector (projT1 pv) (projT2 pv)).
Proof.
    exact app_nil_r_vectF_red_higher.
Qed.

(*
 * TODO now that we are using eliminators instead, need to transfer proof 
 * over to better type. Should do this automatically eventually.
 *)
Theorem test_app_nil_r_vectF:
  forall (pv : sigT natFlector.flector),
    append_vectF_red pv (existT natFlector.flector 0 natFlector.nilFV) = pv.
Proof.
  intros.
  rewrite (conv nat natFlector.flector pv).
  apply app_nil_r_vectF_red_higher.
Qed.

(* in_split_vect *)

Higher lift orn_list_vector orn_list_vector_inv in in_split_vect_red as in_split_vect_higher.

(*
 * TODO note how the type still doesn't look even as nice as the one we state below,
 * even though it indeed has that type.
 *)

Theorem test_in_split_vect_exact:
  forall (A : Type) (x : A) (pv : sigT (vector A)),
    In_vect_red A x (existT (vector A) (projT1 pv) (projT2 pv)) ->
       exists pv1 pv2 : sigT (vector A),
         existT (vector A) (projT1 pv) (projT2 pv) =
         append_vect_red A pv1
           (existT (vector A) (S (projT1 pv2)) (consV A (projT1 pv2) x (projT2 pv2))).
Proof.
  exact in_split_vect_higher.
Qed.

Theorem test_in_split_vect:
  forall (A : Type) (x : A) (pv : sigT (vector A)),
    In_vect_red A x pv ->
      exists pv1 pv2 : sigT (vector A),
        pv = 
        append_vect_red A pv1 
          (existT (vector A) (S (projT1 pv2)) (consV A (projT1 pv2) x (projT2 pv2))).
Proof.
  intros A x pv.
  rewrite (conv nat (vector A) pv).
  intros. 
  apply in_split_vect_higher.
  apply H. 
Qed.

(*
 * Note the above is still predictable enough to derive, which is very good 
 * Should we do it?
 *)

Higher lift orn_list_vector orn_list_vector_inv in hd_error_some_nil_vect_red as hd_error_some_nil_vect_higher.

Theorem test_hd_error_some_nil_vect_exact:
  forall (A : Type) (l : {H : nat & vector A H}) (a : A),
    hd_vect_error_red A (existT (vector A) (projT1 l) (projT2 l)) = Some a ->
    existT (vector A) (projT1 l) (projT2 l) <> existT (vector A) 0 (nilV A).
Proof.
   exact hd_error_some_nil_vect_higher.
Qed.

(* TODO test non-exact, opposite *)


