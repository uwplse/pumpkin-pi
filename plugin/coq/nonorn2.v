Require Import Coq.Program.Tactics.
Require Import PeanoNat.
Require Import Ornamental.Ornaments.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Set DEVOID search prove equivalence.
Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.

(*
 * Now we use the standard Coq binary natural number.
 *)

(* This just helps us preprocess only what we want for later *)
Module Bin_pre.
  Definition nat := N.
  Definition succ := N.succ.
End Bin_pre.

Preprocess Module Bin_pre as Bin { opaque BinPos.Pos Coq.Init.Logic Coq.Classes.Morphisms Coq.Classes.RelationClasses }.
Definition binnat := Bin.nat.

(* --- DepConstr --- *)

Definition dep_constr_A_O := 0.
Definition dep_constr_A_1 := S.
Definition dep_constr_B_O := 0%N.
Definition dep_constr_B_1 := Bin.succ.

(* --- DepElim --- *)

(*
 * For this type, Coq already has a nice DepElim:
 * (Because of an annoying universe bug, we need to set dep_elim for each universe):
 *)
Definition dep_elim_A_Prop := nat_ind.
Definition dep_elim_A_Set := nat_rec.
Definition dep_elim_A_Type := nat_rect.
Definition dep_elim_B := N.peano_rect.

(* --- IdEta --- *)

Definition id_eta_A (n : nat) := nat.
Definition id_eta_B (b : binnat) := binnat.

(* --- RewEta --- *)

Definition rew_eta_A_O :=
 (fun (P : nat -> Type) (PO : P O) (PS : forall n, P n -> P (S n)) (Q : P O -> Type) (H : Q PO) =>
   H).

Definition rew_eta_A_1_typ :=
forall (P : nat -> Type) (PO : P O) (PS : forall x : nat, P x -> P (S x)) 
         (n : nat) (Q : P (S n) -> Type),
       Q (PS n (nat_rect P PO PS n)) -> Q (nat_rect P PO PS (S n)).

Definition rew_eta_A_1 :=
  (fun (P : nat -> Type) (PO : P O) (PS : forall n, P n -> P (S n)) n (Q : P (S n) -> Type) (H : Q (PS n (nat_rect P PO PS n))) =>
   eq_rect
    (PS n (nat_rect P PO PS n))
    (fun (H : P (S n)) => Q H)
    H
    (nat_rect P PO PS (S n))
    (@eq_refl (P (S n)) (PS n (nat_rect P PO PS n)))) : rew_eta_A_1_typ.

Definition rew_eta_B_O :=
 (fun (P : binnat -> Type) (PO : P 0%N) (PS : forall b, P b -> P (Bin.succ b)) (Q : P 0%N -> Type) (H : Q PO) =>
   H).

Definition rew_eta_B_1_typ :=
  forall (P : binnat -> Type) (PO : P 0%N) (PS : forall x : binnat, P x -> P (Bin.succ x)) 
         (n : binnat) (Q : P (Bin.succ n) -> Type),
       Q (PS n (N.peano_rect P PO PS n)) -> Q (N.peano_rect P PO PS (Bin.succ n)).

Definition rew_eta_B_1  :=
  (fun (P : binnat -> Type) (PO : P 0%N) (PS : forall b, P b -> P (Bin.succ b)) n (Q : P (Bin.succ n) -> Type) (H : Q (PS n (N.peano_rect P PO PS n))) =>
  eq_rect
    (PS n (N.peano_rect P PO PS n))
    (fun (H : P (Bin.succ n)) => Q H)
    H
    (N.peano_rect P PO PS (Bin.succ n))
    (eq_sym (N.peano_rect_succ P PO PS n))) : rew_eta_B_1_typ.

(* --- Our nat functions and proofs we'll want to lift --- *)

Module Nat.
  Definition add := Nat.add.
  Definition plus_n_Sm := plus_n_Sm.
End Nat.

Preprocess Module Nat as Nat_pre { opaque nat_ind f_equal_nat f_equal }.

(* --- Lifting addition --- *)

Save equivalence nat binnat { promote = N.of_nat; forget = N.to_nat }.
Configure Lift nat binnat {
  constrs_a = dep_constr_A_O dep_constr_A_1;
  constrs_b = dep_constr_B_O dep_constr_B_1;
  elim_a = dep_elim_A_Set;
  elim_b = dep_elim_B;
  id_eta_a = id_eta_A;
  id_eta_b = id_eta_B;
  rew_eta_a = rew_eta_A_O rew_eta_A_1;
  rew_eta_b = rew_eta_B_O rew_eta_B_1
}.

Lift nat binnat in Nat_pre.add as slow_add.

(*
 * Fast addition behaves like slow addition!
 *)
Lemma add_fast_add:
  forall (n m : Bin.nat),
    slow_add n m = N.add n m.
Proof.
  induction n using N.peano_rect; intros m; auto.
  unfold slow_add.
  rewrite N.peano_rect_succ. (* <- RewEta *)
  unfold slow_add in IHn. rewrite IHn.
  rewrite N.add_succ_l.
  reflexivity.
Qed.

(* --- RewEta for add --- *)

(*
 * We should generate this automatically at some point, but this just instantiates
 * RewEta to add. Then we can lift it to binnat easily.
 *)

Definition rew_eta_A_plus (n : nat) Q (H: Q (fun m : nat => S (Nat_pre.add n m))) : Q (Nat_pre.add (S n)) :=
  rew_eta_A_1 _ (fun p => p) (fun _ IH p => S (IH p)) n Q H.

Lift nat binnat in rew_eta_A_plus as rew_eta_B_plus.

(* --- Lifting a theorem about addition --- *)

(*
 * This is a theorem so we need the Prop eliminator.
 * We need to reconfigure just because of the universe bug.
*)
Configure Lift nat binnat {
  constrs_a = dep_constr_A_O dep_constr_A_1;
  constrs_b = dep_constr_B_O dep_constr_B_1;
  elim_a = dep_elim_A_Prop; (* <- annoying but will fix soon *)
  elim_b = dep_elim_B;
  id_eta_a = id_eta_A;
  id_eta_b = id_eta_B;
  rew_eta_a = rew_eta_A_O rew_eta_A_1;
  rew_eta_b = rew_eta_B_O rew_eta_B_1
}.

(* Now we tweak add_n_Sm to manually add rew_eta where we have casts: *)
Print Nat_pre.Coq_Init_Peano_plus_n_Sm.

(* That gives us this: *)
Definition plus_n_Sm (n m : nat) :=
  nat_ind
    (fun n0 : nat => S (Nat_pre.add n0 m) = Nat_pre.add n0 (S m))
    eq_refl
    (fun (n0 : nat) (IHn : S (Nat_pre.add n0 m) = Nat_pre.add n0 (S m)) =>
      f_equal_nat nat S (S (Nat_pre.add n0 m)) (Nat_pre.add n0 (S m)) IHn)
    n.

(* And then we apply that where we have casts to make them explicit: *)
Definition plus_n_Sm_expanded (n m : nat) :=
  nat_ind
    (fun n0 : nat => S (Nat_pre.add n0 m) = Nat_pre.add n0 (S m))
    eq_refl
    (fun (n0 : nat) (IHn : S (Nat_pre.add n0 m) = Nat_pre.add n0 (S m)) =>
      rew_eta_A_plus _ (fun PS => S (PS m) = Nat_pre.add (S n0) (S m))
        (rew_eta_A_plus _ (fun PS => S (S (Nat_pre.add n0 m)) = PS (S m))
          (f_equal_nat nat S (S (Nat_pre.add n0 m)) (Nat_pre.add n0 (S m)) IHn)))
    n.

(*
 * That's really the only annoying step, and I think we can automate it
 * at some point.
 *)


Lift nat binnat in f_equal_nat as f_equal_binnat.
Lift nat binnat in plus_n_Sm_expanded as binnat_plus_n_Sm.

(* --- Now we can show our theorem over fast addition --- *)

Lemma add_n_Sm :
  forall n m,
    Bin.succ (N.add n m) = N.add n (Bin.succ m).
Proof.
  intros. repeat rewrite <- add_fast_add. apply binnat_plus_n_Sm.
Qed.
