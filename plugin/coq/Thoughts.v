Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Apply.

(*
 * Brainstorming file to avoid cluttering tests
 *)

(* Now what happens if we try to directly use this? We can remove the outer existT with no issue: *)
Definition app_nil_r_vect_het (A : Type) (n : nat) (v : vector A n) :=
  vector_ind 
    A
    (fun (n0 : nat) (v0 : vector A n0) => 
      append_vect_packed A (existT (vector A) n0 v0) (existT (vector A) O (nilV A)) = existT (vector A) n0 v0)
    (@eq_refl (sigT (vector A)) (existT (vector A) O (nilV A)))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IHp : append_vect_packed A (existT (vector A) n0 v0) (existT (vector A) O (nilV A)) = existT (vector A) n0 v0) =>
      @eq_ind_r 
        (sigT (vector A)) 
        (existT (vector A) n0 v0)
        (fun (pv1 : sigT (vector A)) => 
          existT (vector A) (S (projT1 pv1)) (consV A (projT1 pv1) a (projT2 pv1)) = existT (vector A) (S n0) (consV A n0 a v0))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S n0) (consV A n0 a v0)))
        (append_vect_packed A (existT (vector A) n0 v0) (existT (vector A) 0 (nilV A)))
        IHp) 
    n 
    v.

(* That gives us the heterogenous equality. *)

(* But this will fail:
Definition app_nil_r_vect (A : Type) (n : nat) (v : vector A n) :=
  vector_ind 
    A
    (fun (n0 : nat) (v0 : vector A n0) => 
      append_vect A n0 v0 0 (nilV A) = v0)
    (@eq_refl (vector A) (nilV A))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IHp : append_vect A n0 v0 0 (nilV A) = v0) =>
      @eq_ind_r 
        (vector A)
        v0
        (fun (v1 : vector A n0) => 
          consV A n0 a v1 = consV A n0 a v0)
        (@eq_refl (vector A) (consV A n0 a v0))
        (append_vect A n0 v0 0 (nilV A))
        IHp) 
    n 
    v.

The property passed to vector_ind fails type-checking:
The term "v0" has type "vector A n0" while it is expected to have type "vector A (plus_vect A n0 v0 O (nilV A))".
We have an equality between sigmas. We can't get this to an equality between right projections in all cases, unless
the indices are definitionally equal.
Does this problem just happen for equality?
What about for other functions we call? It's really that they don't have the same type.
*)

(* Does it work if we try the experimental version and pack it? (TODO try w/ cast)
Definition app_nil_r_vect_exp (A : Type) (pv : sigT (vector A)) :=
  packed_vect_ind
    A
    (fun pv0 : sigT (vector A) => append_vect_packed_experimental A pv0 (existT (vector A) 0 (@nilV A)) = pv0)
    (@eq_refl (sigT (vector A)) (existT (vector A) 0 (@nilV A)))
    (fun (a : A) (pv0 : sigT (vector A)) (IHv : append_vect_packed_experimental A pv0 (existT (vector A) 0 (@nilV A)) = pv0) =>
      @eq_ind_r
        (sigT (vector A))
        pv0
        (fun (pv1 : sigT (vector A)) => existT (vector A) (S (projT1 pv1)) (consV A (projT1 pv1) a (projT2 pv1)) = existT (vector A) (S (projT1 pv0)) (consV A (projT1 pv0) a (projT2 pv0)))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S (projT1 pv0)) (consV A (projT1 pv0) a (projT2 pv0))))
        (append_vect_packed_experimental A pv0 (existT (vector A) 0 (@nilV A)))
        IHv)
    pv.*)

(* (cannot unify 

"(fun pv1 : {x : nat & vector A x} =>
   existT (vector A) (S (projT1 pv1)) (consV A (projT1 pv1) a (projT2 pv1)) =
   existT (vector A) (S (projT1 pv0)) (consV A (projT1 pv0) a (projT2 pv0)))
 (append_vect_packed_experimental A pv0 (existT (vector A) 0 (nilV A)))" and
"(fun pv0 : {x : nat & vector A x} => 
    append_vect_packed_experimental A pv0 (existT (vector A) 0 (nilV A)) = pv0)
  (existT (vector A) (S (projT1 pv0)) (consV A (projT1 pv0) a (projT2 pv0)))").
 
* Not sure where this fails compared to list version but whatever, figure out
* at some point. The proof above works, so why?
* Try the casting.
*)