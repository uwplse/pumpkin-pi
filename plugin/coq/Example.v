Require Import Vector.
Require Import List.

Require Import Ornamental.Ornaments.

From Coq Require Import ssreflect ssrbool ssrfun.

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
  zip_with (@pair A B) =2 zip.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

End hs_to_coq'.


(* --- Preprocess --- *)

Desugar Module hs_to_coq' as hs_to_coq.

(* --- Search --- *)

Find ornament list Vector.t as ltv.

(* --- Lift --- *)

Lift list Vector.t in hs_to_coq.zip as zipV'.
Lift list Vector.t in hs_to_coq.zip_with as zip_withV'.
Lift list Vector.t in hs_to_coq.zip_with_is_zip as zip_with_is_zipV'.

Print zipV'.
Check zipV'.
Check zip_with_is_zipV'.

(* --- Unpack --- *)

Require Import Coq.Logic.EqdepFacts.

(* TODO add in Nate's automation here *)
Definition zipV {a} {b} {n} (v1 : Vector.t a n) (v2 : Vector.t b n) :=
  projT2 (zipV' a b (existT _ n v1) (existT _ n v2)).

Check zipV.

Check sigT_rect.

(* aux function for indexing *)
Lemma elim_sigT:
  forall A P fnil fcons pv,
    VectorDef.t_rect A P fnil fcons (projT1 pv) (projT2 pv) =
    sigT_rect (fun pv' => P (projT1 pv') (projT2 pv')) (VectorDef.t_rect A P fnil fcons) pv. 
Proof. 
  intros. induction pv. auto.
Qed. 

Definition zip_withV {A} {B} {C} {n} (f : A -> B -> C) (v1 : Vector.t A n) (v2 : Vector.t B n) :=
  projT2 (zip_withV' A B C f (existT _ n v1) (existT _ n v2)).

Check zip_with_is_zipV'.
Check eq_sigT_eq_dep.

Check zip_with_is_zipV'.
Check eq_sigT_eq_dep.

Program Definition zip_with_is_zipV {A} {B} {n} (v1 : Vector.t A n) (v2 : Vector.t B n) :=
  eq_sigT_eq_dep _ _ _ _ 
    (zip_withV pair v1 v2) 
    (zipV v1 v2)
    (zip_with_is_zipV' A B (existT _ n v1) (existT _ n v2)).
Next Obligation. unfold zip_withV. induction v1, v2; auto. Qed.
Next Obligation. unfold zipV. induction v1, v2; auto. Qed. (* will Unpack solve this automatically? *)

Check zip_with_is_zipV.

Eval compute in (zipV (Vector.cons nat 2 0 (Vector.nil nat)) (Vector.cons nat 1 0 (Vector.nil nat))).

(* Client code *)

Definition BVand' {n : nat} :=
  @zip_withV _ _ _ n andb.

Print BVand'.
Require Import Bvector.
Print BVand.

Definition bistreamOr {n : nat} (xs ys : Bitstream n) :=
  zipBits Or xs ys.

(* TODO note somewhere: the index types you get here aren't nice yet *)


Definition bitstreamFlip {n : nat} (xs : Bitstream n) : Bitstream n :=
  mapBits Bitflip xs.

(* n is index. n = 0 means set the 0th bit *)
Fixpoint setBit {m : nat} (n : nat) : Bitstream (n + S m) -> Bitstream (n + S m).
  refine (match n as n' return n = n' -> Bitstream (n' + S m) -> Bitstream (n' + S m) with
          | O => fun H v => _
          | S n' => fun H v => _
          end eq_refl); inversion v.
  + exact (cons _ One _ H1).
  + exact (cons _ One _ (setBit _ _ H1)).
Defined.

Fixpoint fetchBit {m : nat} (n : nat) : Bitstream (n + S m) -> Bit.
  refine (match n as n' return n = n' -> Bitstream (n' + S m) -> Bit with
          | O => fun H v => _
          | S n' => fun H v => _
          end eq_refl); inversion v.
  + exact h.
  + exact (fetchBit _ _ H1).
Defined.                                         
  
Theorem  compliment_of_each_other :
  forall (n : nat) (xs : Bitstream n), bitstreamAnd xs (bitstreamFlip xs) = allZero n.
Proof.
  unfold Bitstream; unfold bitstreamAnd; unfold bitstreamFlip;
    unfold zipBits; unfold mapBits; unfold allZero.
  induction xs.
  + auto.
  + cbn. rewrite IHxs. rewrite and_bit_flip.
    auto.
Qed.
 