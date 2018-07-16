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
Check app_nil_r_vect_auto.
Check app_nil_r_vect_red.

Print app_nil_r_vect_auto. (* Should do existT ... projT1 and projT2 .. l, so that reduction is type-preserving fwiw *)
Print app_nil_r.

(* Note how this version doesn't yet promote append, but preserves the
type of the auto version. When we higher-lift, we then promote append itself,
which changes the type along the equivalence. We do that by substituting in
our already-lifted append. We do the same thing if we have applications of another
theorem, like app_nil_r (really should try this case)
Definition app_nil_r_vect_red' (A : Type) (l : {H : nat & vector A H}) :=
  vector_rect 
    A
    (fun (n : nat) (v : vector A n) =>
      append A (orn_list_vector_inv A (existT (fun H : nat => vector A H) n v)) nil =
      orn_list_vector_inv A (existT (fun H : nat => vector A H) n v)) eq_refl
  (fun (n : nat) (a : A) (v : vector A n)
     (H : append A (orn_list_vector_inv A (existT (fun H : nat => vector A H) n v)) nil =
          orn_list_vector_inv A (existT (fun H : nat => vector A H) n v)) =>
   eq_ind_r
     (fun l1 : list A =>
      a :: l1 =
      a :: orn_list_vector_inv A (existT (fun H0 : nat => vector A H0) n v))
     eq_refl H) (projT1 l) (projT2 l)
*)

Ornamental Modularization app_nil_r_vect_red_higher from app_nil_r_vect_red using orn_list_vector orn_list_vector_inv.

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

Ornamental Modularization app_nil_r_red_higher from app_nil_r_red using orn_list_vector_inv orn_list_vector.

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  exact app_nil_r_red_higher.
Qed.

(* over flectors *)

Print app_nil_r_vectF_red.
Ornamental Modularization app_nil_r_vectF_red_higher from app_nil_r_vectF_red using orn_flist_flector_nat orn_flist_flector_nat_inv.

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

Ornamental Modularization in_split_vect_higher from in_split_vect_red using orn_list_vector orn_list_vector_inv.

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

Eval compute in (fun A a l => orn_list_vector A (cons a l)).

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

Ornamental Modularization hd_error_some_nil_vect_higher from hd_error_some_nil_vect_red using orn_list_vector orn_list_vector_inv.

Theorem test_hd_error_some_nil_vect_exact:
  forall (A : Type) (l : {H : nat & vector A H}) (a : A),
    hd_vect_error_red A (existT (vector A) (projT1 l) (projT2 l)) = Some a ->
    existT (vector A) (projT1 l) (projT2 l) <> existT (vector A) 0 (nilV A).
Proof.
   exact hd_error_some_nil_vect_higher.
Qed.

(* TODO test non-exact, opposite *)


