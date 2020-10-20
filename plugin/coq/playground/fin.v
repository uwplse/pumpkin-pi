(*
 * Vectors and Fin (also from Anders)
 * Thanks to James Wilcox for the missing gaps that I needed!
 * https://gist.github.com/wilcoxjay/10cc817d20ad7148899c3725a1ebf06e
 *)
Require Import Ornamental.Ornaments.

Require Import Coq.Vectors.Fin.
Require Import Coq.Vectors.Vector.

(* needed for this equivalence *)
Require Import Coq.Logic.FunctionalExtensionality.

(*
 * First we need to preprocess to use eliminators, so we can repair later:
 *)
Preprocess Module VectorDef as VectorDef' { opaque
  (* no need: *)
  Coq.Init.Datatypes Coq.Init.Logic Coq.Init.Peano Coq.Init.Nat
  Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Classes.Morphisms
  Coq.Arith.PeanoNat Coq.Classes.Morphisms_Prop Coq.Program.Basics 
  (* needs n-induction: *)
  VectorDef.rectS VectorDef.caseS' VectorDef.rect2
  VectorDef.last VectorDef.nth VectorDef.nth_order VectorDef.replace VectorDef.replace_order
  VectorDef.shiftout VectorDef.shiftrepeat VectorDef.trunc VectorDef.rev_append
  VectorDef.rev VectorDef.map2 VectorDef.fold_right2 VectorDef.fold_left2
}.

(*
 * PUMPKIN Pi still gets annoyed about implicit parameters sometimes, so for now we make
 * T and n explicit.
 *)
Definition A (T : Type) (n : nat) := VectorDef'.t T n.

Definition B (T : Type) (n : nat) := Fin.t n -> T.

(* --- Configuration --- *)

Definition dep_constr_A_0 :=
  VectorDef'.nil.

Definition dep_constr_A_1 (T : Type) (t : T) (n : nat) (a : A T n) : A T (S n) :=
  VectorDef'.cons T t n a.

Program Definition dep_constr_B_0 (T : Type) : B T 0.
Proof.
  unfold B. intros f. apply Fin.case0. apply f.
Defined.

Definition dep_constr_B_1 (T : Type) (t : T) (n : nat) (b : B T n) : B T (S n) :=
  fun f =>
  match f with
  | Fin.F1 => fun _ => t
  | Fin.FS f' => fun b' => b' f'
  end b.

Definition eta_A (T : Type) (n : nat) (a : A T n) : A T n := a.
Definition eta_B (T : Type) (n : nat) (b : B T n) : B T n := b.

(* TODO for practicality, might need this instead, unsure: *)
(*Definition eta_A (n m : nat) (H : n = m) (a : A n) : A m := eq_rect m A a n H.*)
(* and eta B might need to use the tail/hd properties. we'll see *)

Definition dep_elim_A : forall (T : Type) (P : forall n : nat, A T n -> Type) (f0 : P 0 (dep_constr_A_0 T))
  (f1 : forall (t : T) (n : nat) (v : A T n), P n v -> P (S n) (dep_constr_A_1 T t n v)) 
  (n : nat) (v : A T n), P n v 
:=  VectorDef'.t_rect.

Definition hd (T : Type) n (b : B T (S n)) : T :=
  b Fin.F1.

Definition tl (T : Type) n (b : B T (S n)) : B T n :=
  fun f => b (Fin.FS f).

Lemma eta_dep_constr_B_0:
  forall (T : Type) (b : B T 0),
    dep_constr_B_0 T = b.
Proof.
  intros T b.
  apply functional_extensionality_dep_good.
  intros f.
  apply Fin.case0.
  apply f.
Defined.

Lemma eta_dep_constr_B_1:
  forall (T : Type) (n : nat) (b : B T (S n)),
    dep_constr_B_1 T (hd T n b) n (tl T n b) = b.
Proof.
  intros T n b.
  apply functional_extensionality_dep_good.
  intros f.
  revert b.
  refine (
    match f with
    | Fin.F1 => _
    | Fin.FS _ => _
    end
  ); reflexivity.
Defined.

Program Definition dep_elim_B (T : Type) (P : forall n : nat, B T n -> Type) (f0 : P 0 (dep_constr_B_0 T))
  (f1 : forall (t : T) (n : nat) (f : B T n), P n f -> P (S n) (dep_constr_B_1 T t n f)) 
  (n : nat) (b : B T n) 
: P n b. 
Proof.
  induction n.
  - replace b with (@dep_constr_B_0 T) by (apply eta_dep_constr_B_0). auto.
  - replace b with (dep_constr_B_1 T (hd T n b) n (tl T n b)) by (apply eta_dep_constr_B_1). auto.
Defined.

(*
 * iota over A is of course trivial:
 *)
Lemma iota_A_0 :
 forall (T : Type) (P : forall (n : nat), A T n -> Type)
   (f0 : P 0 (dep_constr_A_0 T))
   (f1 : forall (t : T) (n : nat) (f : A T n), P n f -> P (S n) (dep_constr_A_1 T t n f))
   (Q : P 0 (dep_constr_A_0 T) -> Type),
   Q (dep_elim_A T P f0 f1 0 (dep_constr_A_0 T)) ->
   Q f0.
Proof.
  intros. auto.
Defined.

Lemma iota_A_1 :
 forall (T : Type) (P : forall (n : nat), A T n -> Type)
   (f0 : P 0 (dep_constr_A_0 T))
   (f1 : forall (t : T) (n : nat) (f : A T n), P n f -> P (S n) (dep_constr_A_1 T t n f))
   (t : T) (n : nat) (f : A T n) (Q : P (S n) (dep_constr_A_1 T t n f) -> Type),
   Q (dep_elim_A T P f0 f1 (S n) (dep_constr_A_1 T t n f)) ->
   Q (f1 t n f (dep_elim_A T P f0 f1 n f)).
Proof.
  intros. auto.
Defined.

(*
 * Needed for iota_B_0:
 *)
Lemma eta_refl_B_0:
  forall (T : Type), eta_dep_constr_B_0 T (dep_constr_B_0 T) = eq_refl.
Proof.
  intros. unfold eta_dep_constr_B_0.
  symmetry. eapply eq_trans.
  - symmetry. apply functional_extensionality_dep_good_refl.
  - f_equal. extensionality f.
    apply Fin.case0. apply f.
Defined.

Lemma iota_B_0 :
 forall (T : Type) (P : forall (n : nat), B T n -> Type)
   (f0 : P 0 (dep_constr_B_0 T))
   (f1 : forall (t : T) (n : nat) (f : B T n), P n f -> P (S n) (dep_constr_B_1 T t n f))
   (Q : P 0 (dep_constr_B_0 T) -> Type),
   Q (dep_elim_B T P f0 f1 0 (dep_constr_B_0 T)) ->
   Q f0.
Proof.
  intros. simpl in X. rewrite eta_refl_B_0 in X. apply X.
Defined.

(*
 * Needed for iota_B_1:
 *)
Lemma eta_refl_B_1:
  forall (T : Type) (n : nat) (t : T) (b : B T n),
    eta_dep_constr_B_1 T n (dep_constr_B_1 T t n b) = eq_refl.
Proof.
  intros. unfold eta_dep_constr_B_1. unfold hd. unfold tl. simpl.
  symmetry. eapply eq_trans.
  - symmetry. apply functional_extensionality_dep_good_refl.
  - f_equal. extensionality f.
    revert b. 
    refine (
    match f with
    | Fin.F1 => _
    | Fin.FS _ => _
    end); auto.
Defined.

Lemma iota_B_1 :
 forall (T : Type) (P : forall (n : nat), B T n -> Type)
   (f0 : P 0 (dep_constr_B_0 T))
   (f1 : forall (t : T) (n : nat) (f : B T n), P n f -> P (S n) (dep_constr_B_1 T t n f))
   (t : T) (n : nat) (b : B T n) (Q : P (S n) (dep_constr_B_1 T t n b) -> Type),
   Q (dep_elim_B T P f0 f1 (S n) (dep_constr_B_1 T t n b)) ->
   Q (f1 t n b (dep_elim_B T P f0 f1 n b)).
Proof.
  intros. simpl in X. unfold hd in X. unfold tl in X. simpl in X.
  rewrite eta_refl_B_1 in X. apply X.
Defined.

(* --- Induced equivalence --- *)

(*
 * These should form their own equivalence:
 *)
Definition f (T : Type) (n : nat) (a : A T n) : B T n :=
  dep_elim_A
    T
    (fun n _ => B T n) 
    (dep_constr_B_0 T)
    (fun t n b IH => dep_constr_B_1 T t n IH)
    n
    a.

Definition g (T : Type) (n : nat) (b : B T n) : A T n :=
  dep_elim_B
    T
    (fun n _ => A T n) 
    (dep_constr_A_0 T)
    (fun t n b IH => dep_constr_A_1 T t n IH)
    n
    b.

(*
 * This could be much easier, but I want to make a point of doing this algorithmically!
 *)
Lemma section (T : Type) (n : nat) (a : A T n) : g T n (f T n a) = a.
Proof.
  apply dep_elim_A with (v := a); unfold f; unfold g; intros.
  - unfold dep_constr_A_0 at 1. unfold dep_constr_A_0 at 1.
    apply (iota_B_0 T (fun n _ => A T n) (dep_constr_A_0 T) (fun t n b IH => dep_constr_A_1 T t n IH)).
    unfold dep_constr_B_0 at 1.
    apply (iota_A_0 T (fun n _ => B T n) (dep_constr_B_0 T) (fun t n a IH => dep_constr_B_1 T t n IH)).
    reflexivity.
  - unfold dep_constr_A_1 at 1. unfold dep_constr_A_1 at 1.
    replace (dep_constr_A_1 T t n0 v) with (dep_constr_A_1 T t n0 (g T n0 (f T n0 v))).
    + unfold g. unfold f.
      apply (iota_B_1 T (fun n _ => A T n) (dep_constr_A_0 T) (fun t n b IH => dep_constr_A_1 T t n IH) t n0).
      apply (iota_A_1 T (fun n _ => B T n) (dep_constr_B_0 T) (fun t n a IH => dep_constr_B_1 T t n IH)).
      reflexivity.
    + unfold g. unfold f. rewrite H. reflexivity. 
Defined.

(*
 * The point being that this direction should mirror this exactly, despite iota actually mattering here.
 *)
Lemma retraction (T : Type) (n : nat) (b : B T n) : f T n (g T n b) = b.
Proof.
  apply dep_elim_B with (b := b); unfold f; unfold g; intros.
  - unfold dep_constr_B_0 at 1. unfold dep_constr_B_0 at 1.
    apply (iota_A_0 T (fun n _ => B T n) (dep_constr_B_0 T) (fun t n a IH => dep_constr_B_1 T t n IH)).
    unfold dep_constr_A_0 at 1.
    apply (iota_B_0 T (fun n _ => A T n) (dep_constr_A_0 T) (fun t n b IH => dep_constr_A_1 T t n IH)).
    reflexivity.
  - unfold dep_constr_B_1 at 1. unfold dep_constr_B_1 at 1.
    replace (dep_constr_B_1 T t n0 f0) with (dep_constr_B_1 T t n0 (f T n0 (g T n0 f0))).
    + unfold f. unfold g.
      apply (iota_A_1 T (fun n _ => B T n) (dep_constr_B_0 T) (fun t n a IH => dep_constr_B_1 T t n IH) t n0).
      apply (iota_B_1 T (fun n _ => A T n) (dep_constr_A_0 T) (fun t n a IH => dep_constr_A_1 T t n IH)).
      reflexivity.
    + unfold f. unfold g. rewrite H. reflexivity. 
Defined.

Print retraction.

(* hahaha holy shit *)

(* --- Saving the equivalence --- *)

Save equivalence A B { promote = f; forget = g }.

(*
 * We explicitly refer to VectorDef' here to work around the combination of
 * universe bugs and lack of unification heuristics.
 *)
Configure Lift A B {
  constrs_a = dep_constr_A_0 dep_constr_A_1;
  constrs_b = dep_constr_B_0 dep_constr_B_1;
  elim_a = VectorDef'.t_rect;
  elim_b = dep_elim_B;
  eta_a = eta_A;
  eta_b = eta_B;
  iota_a = iota_A_0 iota_A_1;
  iota_b = iota_B_0 iota_B_1
}.

(* --- Repair --- *)

(*
 * Functions (provided preprocess worked) are easy, since we don't need iota.
 * But we still need to make dep_constr_A_1 explicit because, yes, lack of unification heuristics
 * makes things that dire, though I think that is fixable to some degree).
 *
 * To do that, we use "Replace Convertible" from PUMPKIN PATCH, but this won't
 * build without PUMPKIN PATCH, so TODO expose this inside of PUMPKIN Pi.
 * This at least proves that the problem is unification heuristics here,
 * and that the solution is at least in some cases really not hard.
 *)
Require Import Patcher.Patch.
Module Over_A.

Replace Convertible dep_constr_A_1 in VectorDef'.caseS as caseS.
Replace Convertible dep_constr_A_1 caseS in VectorDef'.hd as hd.
Replace Convertible caseS in VectorDef'.tl as tl.
Replace Convertible dep_constr_A_1 in VectorDef'.const as const.
Replace Convertible dep_constr_A_1 in VectorDef'.shiftin as shiftin.
Replace Convertible dep_constr_A_1 in VectorDef'.take as take.
Replace Convertible dep_constr_A_1 in VectorDef'.append as append.
Replace Convertible dep_constr_A_1 in VectorDef'.rev_append_tail as rev_append_tail.
Replace Convertible dep_constr_A_1 in VectorDef'.map as map.
Replace Convertible dep_constr_A_1 in VectorDef'.fold_left as fold_left.
Replace Convertible dep_constr_A_1 in VectorDef'.fold_right as fold_right.

(* TODO universe bugs prevent us from lifting Forall, Exists, In, and so on. *)

End Over_A.

Set DEVOID lift type.
Repair Module A B in Over_A as Over_B { opaque nat_rect VectorDef'.Coq_Arith_PeanoNat_Nat_nle_succ_0 VectorDef'.Coq_Arith_Le_le_S_n False_rect VectorDef'.Coq_Arith_PeanoNat_Nat_add VectorDef'.Coq_Arith_Plus_tail_plus }.
Print Over_B.

(*
 * TODO some proofs (with iota, will be annoying), some stuff with matrices
 *)