Add LoadPath "coq/examples".
Require Import Example.
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

From Coq Require Import Arith.

(* syntax to match paper *)
Notation vector := Vector.t.
Notation consV n t v := (Vector.cons _ t n v).
Notation nilV := Vector.nil.

Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.
Set DEVOID lift type.

(* Usually, we use this: *)
Definition vanilla_uip
  : forall (x y : nat) (p1 p2 : x = y), p1 = p2
:= Eqdep_dec.UIP_dec Nat.eq_dec.

(*
 * Okay, now let's try to state and prove a lemma that doens't
 * depend on UIP on the type nat, but rather depends
 * on the list and vector types. First:
 *)
Find ornament list vector as ltv.

(*
 * Next, define the adjoints:
 *)

Definition section_adjoint T := Adjoint.fg_id' (ltv_inv T) (ltv T) (ltv_retraction T) (ltv_section T).
Definition retraction_adjoint T := Adjoint.fg_id' (ltv T) (ltv_inv T) (ltv_section T) (ltv_retraction T).

Lemma is_adjoint_section T (pv : sigT (vector T)) : ltv_section T (ltv_inv T pv) = f_equal (ltv_inv T) (retraction_adjoint T pv).
Proof.
  apply Adjoint.g_adjoint.
Defined.

Lemma is_adjoint_retraction T (l : list T) : ltv_retraction T (ltv T l) = f_equal (ltv T) (section_adjoint T l).
Proof.
  apply Adjoint.g_adjoint.
Defined.

(* Try the Jason thing first: *)
Definition ltv_u (A : Type) (n : nat) (ll : { l : list A & ltv_index A l = n}) : vector A n :=
  eq_rect
    (ltv_index _ (projT1 ll))
    (vector A)
    (eq_rect
      (projT1 (ltv _ (projT1 ll))) 
      (vector A)
      (projT2 (ltv _ (projT1 ll)))
      (ltv_index _ (projT1 ll))
      (ltv_coh _ (projT1 ll))) 
    n
    (projT2 ll). (* ltv_index A l = n *)

Definition ltv_inv_u (A : Type) (n : nat) (v : vector A n) : { l : list A & ltv_index A l = n} :=
  existT 
    (fun (l : list A) => ltv_index _ l = n)
    (ltv_inv _ (existT _ n v)) 
    (eq_rect
      (projT1 (ltv A (ltv_inv A (existT _ n v))))
      (fun n0 : nat => n0 = n)
      (eq_rect
        (existT _ n v)
        (fun s : sigT (vector A) => projT1 s = n)
        (eq_refl (projT1 (existT _ n v)))
        (ltv A (ltv_inv A (existT _ n v)))
        (eq_sym (ltv_retraction _ (existT _ n v))))
      (ltv_index _ (ltv_inv _ (existT _ n v)))
      (ltv_coh _ (ltv_inv _ (existT _ n v)))).

Lemma section_u : forall A n v, ltv_inv_u A n (ltv_u A n v) = v.
Proof.
  intros A n [l H]; apply eq_sigT_uncurried; subst n.
  cbv [ltv_u ltv_inv_u ltv_coh].
  cbn [projT1 projT2 eq_rect].
  change (existT _ (ltv_index A l) (projT2 (ltv A l))) with (ltv A l).
  exists (section_adjoint _ _).
  rewrite (is_adjoint_retraction A l).
  destruct (section_adjoint A l).
  reflexivity.
Qed.

Lemma retraction_u : forall A n v, ltv_u A n (ltv_inv_u A n v) = v.
Proof.
  cbv [ltv_u ltv_inv_u].
  cbn [projT1 projT2].
  intros.
  set (p := ltv_retraction A (existT _ n v)).
  set (q := ltv_coh _ _).
  clearbody p q.
  cbv beta in *.
  generalize dependent (ltv A (ltv_inv A (existT _ n v))).
  intros [x y] p q.
  cbn [projT1 projT2] in *.
  subst x.
  inversion_sigma.
  repeat match goal with H : _ = ?v |- _ => is_var v; destruct H end.
  reflexivity.
Qed.


(* So, what variant of UIP do we get this way? It should be in the proof of section somewhere. *)
(* TODO WIP, see issue 39 *)

Definition zip := packed_list.zip.
Definition zip_with := packed_list.zip_with.

Lemma zip_with_is_zip :
  forall A B n (pl1 : { l1 : list A & length l1 = n }) (pl2 : { l2 : list B & length l2 = n }),
    zip_with A B (A * B) pair n pl1 pl2 = zip A B n pl1 pl2.
Proof.
  intros A B n pl1. 
  apply packed_list_rect with (P := fun (pl1 : {l1 : list A & length l1 = n}) => forall pl2 : {l2 : list B & length l2 = n}, zip_with A B (A * B) pair n pl1 pl2 = zip A B n pl1 pl2). 
  intros l H pl2.
  unfold zip_with, zip, packed_list_rect, hs_to_coqV_p.list_to_t_rect, packed_rect. simpl.
  apply eq_existT_uncurried.
  (* list proof: *)
  exists (hs_to_coq.zip_with_is_zip A B l (projT1 pl2)).
  (* length invariant: *)
  apply (Eqdep_dec.UIP_dec Nat.eq_dec).
Defined.