(*
 * Walkthrough of lifting for Section 4
 *)

Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Search. (* our ornament *)

(*
 * Our arguments to cons are swapped from Coq's in the paper
 *)
Definition vect_rect {T : Type} p f_nil f_cons (n : nat) (v : vector T n) :=
  Vector.t_rect T p
    f_nil
    (fun (t : T) (n : nat) (v : vector T n) (IH : p n v) =>
      f_cons n t v IH)
    n
    v.

(*
 * Note we have this nice equality between eliminators:
 *)
Example lift_elim_correct:
  forall {T : Type} p_A f_nil f_cons n (v : vector T n),
    list_rect p_A 
      f_nil 
      f_cons 
      (forget (existT _ n v)) 
    =
    vect_rect (fun n v => p_A (forget (existT _ n v)))
      f_nil
      (fun n t v IH => f_cons t (forget (existT _ n v)) IH)
      n
      v.
Proof.
  induction v.
  - reflexivity.
  - simpl. f_equal. apply IHv.
Qed. 

(*
 * So, what does it look like when we lift an eliminator
 * application?
 *)
Definition proof T p_A f_nil f_cons (l : list T) :=
  list_rect p_A 
    f_nil 
    f_cons 
    l.

Lift list vector in proof as proofV_p.
Print proofV_p.

(* --- Lifting constructors --- *)

(*
 * In the base case, we just normalize:
 *)
Lift list vector in @nil as nilV_p.
Print nilV_p.

(*
 * As mentioned in the implementation section,
 * refolding happens here to deal with constants.
 * But the equalities should be clear that way:
 *)
Lift list vector in @cons as consV_p.
Print consV_p.


(* --- Lifting --- *)

(* 
 * Let's lift a few simple list functions, now 
 *)

Preprocess hd as hd'.
Lift list vector in hd' as hdV_p.
Print hdV_p.

Preprocess tl as tl'.
Lift list vector in tl' as tlV_p.
Print tlV_p.

Preprocess remove as remove'.
Lift list vector in remove' as removeV_p.
Print removeV_p.
