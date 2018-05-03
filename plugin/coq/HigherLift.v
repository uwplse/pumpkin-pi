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

Theorem test_app_nil_r_vect:
  forall (A : Type) (pv : packed_vector A),
    append_vect_red A pv (existT (vector A) 0 (nilV A)) = pv.
Proof.
  exact app_nil_r_vect_red_higher.
Qed.

Higher lift orn_list_vector_inv orn_list_vector in app_nil_r_red as app_nil_r_red_higher.

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_red A l (@nil A) = l.
Proof.
  exact app_nil_r_red_higher.
Qed.

Print in_split_vect_red.
Print in_split.

(*
 * List version
 *)
Definition check_list (A : Type) (a : A) (l0 : list A) (x1 : list A) (x : A) (x0 : list A)
                      (H6 : l0 = append A x0 (cons x x1)) :=
  ex_intro
    (fun (l2 : list A) =>
      cons a l0 =
      append A (cons a x0) (cons x l2)) 
    x1
    (eq_ind_r
      (fun (l0 : list A) =>
         cons a l0 =
         cons a (append A x0 (cons x x1)))
       (eq_refl (cons a (append A x0 (cons x x1))))
       H6).

(*
 * List version, alt
 *)
Definition check_list_alt (A : Type) (a : A) (l0 : list A) (x1 : list A) (x : A) (x0 : list A)
                      (H6 : l0 = append A x0 (cons x x1)) :=
  ex_intro
    (fun (l2 : list A) =>
      cons a l0 =
      append A (cons a x0) (cons x l2)) 
    x1
    (eq_ind_r
      (fun (l0 : list A) =>
         cons a l0 =
         append A (cons a x0) (cons x x1))
       (eq_refl (cons a (append A x0 (cons x x1))))
       H6).

Print in_split_vect_red.

(*
 * I think I get it. This particular term is impossible, since it goes through an equality proof that won't hold in the unpacked version?
 * So not every proof is one you can port directly.
 * Let's try to simplify our proof to one that does work.
 *)

Definition check_lower (A : Type) (a : A) (n : nat) (v0 : vector A n) (x1 : list A) (x : A) (x0 : list A)
                 (H6 : orn_list_vector_inv A (existT (vector A) n v0) = append A x0 (cons x x1)) :=
  ex_intro
    (fun (l2 : list A) =>
      cons a (orn_list_vector_inv A (existT (vector A) n v0)) =
      append A (cons a x0) (cons x l2))
    x1
    (eq_ind_r
      (fun (l0 : list A) =>
        cons a l0 =
        cons a (append A x0 (x :: x1)))
      eq_refl 
      H6).

Definition check_sub (A : Type) (a : A) (n : nat) (v0 : vector A n) (x1 : sigT (vector A)) (x : A) (x0 : sigT (vector A))
                 (H6 : existT (vector A) n v0 = append_vect_red A x0 (existT (fun H6 : nat => vector A H6) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))) :=
  eq_ind_r 
      (fun (l0 : sigT (vector A)) =>
         existT (vector A) (S (projT1 l0)) (consV A (projT1 l0) a (projT2 l0)) = 
         existT 
           (vector A) 
           (S 
             (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))))) 
           (consV 
             A
             (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))) 
             a 
             (projT2 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))))) 
      eq_refl 
      H6.

Check check_sub.

(* This would go through, if we changed the property, but no idea if it's what we want: *)
Definition check_different_p (A : Type) (a : A) (n : nat) (v0 : vector A n) (x1 : sigT (vector A)) (x : A) (x0 : sigT (vector A))
                 (H6 : existT (vector A) n v0 = append_vect_red A x0 (existT (fun H6 : nat => vector A H6) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))) :=
  ex_intro 
    (fun (l2 : sigT (vector A)) =>
      existT (vector A) (S (projT1 (existT (vector A) n v0))) (consV A (projT1 (existT (vector A) n v0)) a (projT2 (existT (vector A) n v0))) = 
      existT (vector A) (S (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 l2)) (consV A (projT1 l2) x (projT2 l2)))))) (consV A (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 l2)) (consV A (projT1 l2) x (projT2 l2))))) a (projT2 (append_vect_red A x0 (existT (vector A) (S (projT1 l2)) (consV A (projT1 l2) x (projT2 l2)))))))
    x1
    (eq_ind_r 
      (fun (l0 : sigT (vector A)) =>
         existT (vector A) (S (projT1 l0)) (consV A (projT1 l0) a (projT2 l0)) = 
         existT 
           (vector A) 
           (S 
             (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))))) 
           (consV 
             A
             (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))) 
             a 
             (projT2 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))))) 
      eq_refl 
      H6).

Print append_vect_red.

Definition append_vect_red_alt :=
fun (A : Type) (l1 l2 : {H : nat & vector A H}) =>
  vector_rect 
    A
    (fun (n : nat) (_ : vector A n) => sigT (vector A)) 
    l2
    (fun (n : nat) (a : A) (_ : vector A n) (H1 : sigT (vector A)) =>
      existT (vector A) (S (projT1 H1)) (consV A (projT1 H1) a (projT2 H1))) 
    (projT1 l1)
    (projT2 l1).

(*
 * Does that version of append have better properties?
 *)
Definition check_alt (A : Type) (a : A) (n : nat) (v0 : vector A n) (x1 : sigT (vector A)) (x : A) (x0 : sigT (vector A))
                 (H6 : existT (vector A) n v0 = append_vect_red_alt A x0 (existT (fun H6 : nat => vector A H6) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))) :=
  ex_intro 
    (fun (l2 : sigT (vector A)) =>
      existT (vector A) (S (projT1 (existT (vector A) n v0))) (consV A (projT1 (existT (vector A) n v0)) a (projT2 (existT (vector A) n v0))) = 
      append_vect_red_alt A (existT (vector A) (S (projT1 x0)) (consV A (projT1 x0) a (projT2 x0))) (existT (vector A) (S (projT1 l2)) (consV A (projT1 l2) x (projT2 l2))))
    x1
    (eq_ind_r 
      (fun (l0 : sigT (vector A)) =>
         existT (vector A) (S (projT1 l0)) (consV A (projT1 l0) a (projT2 l0)) = 
         existT 
           (vector A) 
           (S 
             (projT1 (append_vect_red_alt A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))))) 
           (consV 
             A
             (projT1 (append_vect_red_alt A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))) 
             a 
             (projT2 (append_vect_red_alt A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))))) 
      eq_refl 
      H6).

(*
 * Term that is failing:
Definition check (A : Type) (a : A) (n : nat) (v0 : vector A n) (x1 : sigT (vector A)) (x : A) (x0 : sigT (vector A))
                 (H6 : existT (vector A) n v0 = append_vect_red A x0 (existT (fun H6 : nat => vector A H6) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))) :=
  ex_intro 
    (fun (l2 : sigT (vector A)) =>
      existT (vector A) (S (projT1 (existT (vector A) n v0))) (consV A (projT1 (existT (vector A) n v0)) a (projT2 (existT (vector A) n v0))) = 
      append_vect_red A (existT (vector A) (S (projT1 x0)) (consV A (projT1 x0) a (projT2 x0))) (existT (vector A) (S (projT1 l2)) (consV A (projT1 l2) x (projT2 l2))))
    x1
    (eq_ind_r 
      (fun (l0 : sigT (vector A)) =>
         existT (vector A) (S (projT1 l0)) (consV A (projT1 l0) a (projT2 l0)) = 
         existT 
           (vector A) 
           (S 
             (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1)))))) 
           (consV 
             A
             (projT1 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))) 
             a 
             (projT2 (append_vect_red A x0 (existT (vector A) (S (projT1 x1)) (consV A (projT1 x1) x (projT2 x1))))))) 
      eq_refl 
      H6).
*)

(*
 * Problem is that these don't quite compute:

 existT (vector A)
  (S
     (let (a0, _) :=
        let (H, H0) := x0 in  (* project out first *)
        (...) H H0 in
      a0))
  (consV A
     (let (a0, _) :=
        let (H, H0) := x0 in  (* project out first *)
        (...) H H0 in
      a0) a
     (let (x2, h) as x2 return (vector A (let (a0, _) := x2 in a0)) :=
        let (H, H0) := x0 in  (* project out first *)
        (...) H H0 in
      h)) =
existT (fun H2 : nat => vector A H2)
  (S
     (let (a0, _) :=
        (...) (let (a0, _) := x0 in a0) (let (x2, h) as x2 return (vector A (let (a0, _) := x2 in a0)) := x0 in h) in
      a0))
  (consV A
     (let (a0, _) :=
        (...) (let (a0, _) := x0 in a0) (let (x2, h) as x2 return (vector A (let (a0, _) := x2 in a0)) := x0 in h) in
      a0) a
     (let (x2, h) as x2 return (vector A (let (a0, _) := x2 in a0)) :=
        (...) (let (a0, _) := x0 in a0) (let (x2, h) as x2 return (vector A (let (a0, _) := x2 in a0)) := x0 in h) in
      h))

 Note the projections 
 *)

Print projT2.

Check in_split_vect_red.

Higher lift orn_list_vector orn_list_vector_inv in in_split_vect_red as in_split_vect_higher.

(*
 * Interestingly, the trouble here is with f_equal.
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
 *)

Print in_split_vect_higher.