Require Import Coq.Program.Tactics.
Require Import PeanoNat.
Require Import Ornamental.Ornaments.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.

Set DEVOID search prove equivalence.
Set DEVOID search prove coherence.
Set DEVOID search smart eliminators.
Set DEVOID lift type.

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
 *)
Definition dep_elim_A := nat_rect.
Preprocess N.peano_rect as dep_elim_B.

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

Save equivalence nat binnat { promote = N.of_nat; forget = N.to_nat }.
Configure Lift nat binnat {
  constrs_a = dep_constr_A_O dep_constr_A_1;
  constrs_b = dep_constr_B_O dep_constr_B_1;
  elim_a = dep_elim_A;
  elim_b = dep_elim_B;
  id_eta_a = id_eta_A;
  id_eta_b = id_eta_B;
  rew_eta_a = rew_eta_A_O rew_eta_A_1;
  rew_eta_b = rew_eta_B_O rew_eta_B_1
}.

(* Basic tests *)
Lift nat binnat in O as O_lifted.
Lift nat binnat in S as S_lifted.
Lift binnat nat in 0%N as Bin_O_lifted.
Lift binnat nat in Bin.succ as Bin_S_lifted.

(* Lift addition (bug right now with nat_rec & universes so we use nat_rect) *)
Definition add (n m : nat) : nat :=
nat_rect (fun _ : nat => nat -> nat) (fun m : nat => m)
  (fun (_ : nat) (add : nat -> nat) (m : nat) => S (add m)) n m.

Lift nat binnat in add as binnat_add.

Definition f_equal_term (m : nat) (n0 : nat) (IHn : (S (add n0 m)) = (add n0 (S m))) :=
  @f_equal
             nat
             nat
             (fun (n : nat) => S n)
             (S (add n0 m))
             (add n0 (S m))
             IHn.

Configure Lift nat binnat {
  opaque f_equal eq_rect N_rect binnat_add (* TODO make rew_S_elim opaque automatically? and why is the fact that it's cached not triggering? *)
}.

Lift nat binnat in f_equal_term as f_equal_term_binnat.

Lift nat binnat in rew_eta_A_1_typ as rew_eta_A_1_typ_lifted. 
Lemma foo:
  rew_eta_B_1_typ =
  rew_eta_A_1_typ_lifted.
Proof.
  reflexivity.
Defined.

Lift nat binnat in rew_eta_A_1 as rew_eta_A_1_lifted.
Print rew_eta_A_1_lifted.

(* TODO There is some evar map bug if we don't prove foo. investigate *)



Definition inner_term (m : nat) (n0 : nat) (IHn : (S (add n0 m)) = (add n0 (S m))) :=
(rew_eta_A_1
           (fun _ => nat -> nat)
           (fun p => p)
           (fun _ IH p => S (IH p))
           n0
           (fun PS => S (S (add n0 m)) = PS (S m))
           (f_equal_term m n0 IHn)).


Lift nat binnat in inner_term as inner_term_lifted.


Definition plus_n_Sm_inductive (m : nat) 
  (n0 : nat) (IHn : (S (add n0 m)) = (add n0 (S m))) :=
       rew_eta_A_1
         (fun _ => nat -> nat)
         (fun p => p)
         (fun _ IH p => S (IH p))
         n0
         (fun PS => S (PS m) = add (S n0) (S m))
         (inner_term m n0 IHn).

Lift nat binnat in plus_n_Sm_inductive as binnat_plus_n_Sm_inductive.

(* expanded reweta ourselves *)
Definition plus_n_Sm (n m : nat) : S (add n m) = add n (S m) :=
  nat_rect
    (fun (n0 : nat) =>
       S (add n0 m) = add n0 (S m))
    (@eq_refl nat (S m))
    (fun (n0 : nat) (IHn : (S (add n0 m)) = (add n0 (S m))) =>
       plus_n_Sm_inductive m n0 IHn)
     n.


Lift nat binnat in plus_n_Sm as binnat_plus_n_Sm.
Print binnat_plus_n_Sm.



