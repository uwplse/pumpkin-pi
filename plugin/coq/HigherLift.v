Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.
Require Import Reduce.

(*
 * Tests for higher lifting.
 *)

Higher lift orn_list_vector orn_list_vector_inv in app_nil_r_vect_red as app_nil_r_vect_red_higher.

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

Higher lift orn_list_vector orn_list_vector_inv in in_split_vect_red as in_split_vect_higher.

(*
 * Interestingly, the trouble with the old definition here is with f_equal.
 *
 * Must know to reduce this:
 *
 * (λ (f : sigT nat (vector A) -> sigT nat (vector A)) . 
 *   orn_list_vector A (f (existT nat (vector A) n v0))))
 *
 * We want:
 *
 * (λ (f : sigT nat (vector A) -> sigT nat (vector A)) . 
 *   f (existT nat (vector A) n v0)))
 *
 * But the normal substitute and reduce strategy doesn't figure that out.
 *
 * Also, f_equal takes (cons A a) as a parameter, and that's
 * a function still. How do we know to lift that?
 *
 * TODO investigate later
 *)

Print in_split_vect_higher.

(* TODO test *)