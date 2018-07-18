Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Temporary file to test lifting induction principles, before we cut
 * out extra steps of the old algorithm.
 *)

Definition hd (A : Type) (default : A) (l : list A) :=
  list_rect
    (fun (_ : list A) => A)
    default
    (fun (x : A) (_ : list A) (_ : A) =>
      x)
    l.

Definition hd_vect (A : Type) (default : A) (v : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => A)
    default
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : A) =>
      x)
    (projT1 v)
    (projT2 v).

Lift induction orn_list_vector orn_list_vector_inv in hd as hd_vect_ind.
Print hd_vect_ind.

Lift induction orn_list_vector_inv orn_list_vector in hd_vect as hd_ind.
Print hd_ind.

(* flist/flector version *)

Definition hdF (default : nat) (l : natFlector.flist) :=
  natFlector.flist_rect
    (fun (_ : natFlector.flist) => nat)
    default
    (fun (x : nat) (_ : natFlector.flist) (_ : nat) =>
      x)
    l.

Definition hd_vectF (default : nat) (v : sigT natFlector.flector) :=
  natFlector.flector_rect
    (fun (n0 : nat) (_ : natFlector.flector n0) => nat)
    default
    (fun (n0 : nat) (x : nat) (_ : natFlector.flector n0) (_ : nat) =>
      x)
    (projT1 v)
    (projT2 v).

Lift induction orn_flist_flector_nat orn_flist_flector_nat_inv in hdF as hd_vectF_ind.
Print hd_vectF_ind.

Lift induction orn_flist_flector_nat_inv orn_flist_flector_nat in hd_vectF as hdF_ind.
Print hdF_ind.

(* hd_error *)

Definition hd_error (A : Type) (l:list A) :=
  list_rect
    (fun (_ : list A) => option A)
    None
    (fun (x : A) (_ : list A) (_ : option A) =>
      Some x)
    l.

Definition hd_vect_error (A : Type) (v : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => option A)
    None
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : option A) =>
      Some x)
    (projT1 v)
    (projT2 v).

Lift induction orn_list_vector orn_list_vector_inv in hd_error as hd_vect_error_ind.
Print hd_vect_error_ind.

Lift induction orn_list_vector_inv orn_list_vector in hd_vect_error as hd_error_ind.
Print hd_error_ind.

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

Definition append_vect (A : Type) (pv1 : sigT (vector A)) (pv2 : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => sigT (fun (n : nat) => vector A n))
    pv2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : sigT (fun (n : nat) => vector A n)) =>
      existT
        (vector A)
        (S (projT1 IH))
        (consV A (projT1 IH) a (projT2 IH)))
    (projT1 pv1)
    (projT2 pv1).

Lift induction orn_list_vector orn_list_vector_inv in append as append_vect_ind.
Print append_vect_ind.

Lift induction orn_list_vector_inv orn_list_vector in append_vect as append_ind.
Print append_ind.

(* append for flectors *)

Definition appendF (l1 : natFlector.flist) (l2 : natFlector.flist) :=
  natFlector.flist_rect
    (fun (_ : natFlector.flist) => natFlector.flist)
    l2
    (fun (a : nat) (_ : natFlector.flist) (IH : natFlector.flist) =>
      natFlector.consF a IH)
    l1.

Definition append_vectF (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector) :=
  natFlector.flector_rect
    (fun (n0 : nat) (v0 : natFlector.flector n0) => sigT natFlector.flector)
    pv2
    (fun (n0 : nat) (a : nat) (v0 : natFlector.flector n0) (IH : sigT natFlector.flector) =>
      existT
        natFlector.flector
        (natFlector.SIfEven a (projT1 IH))
        (natFlector.consFV (projT1 IH) a (projT2 IH)))
    (projT1 pv1)
    (projT2 pv1).

Lift induction orn_flist_flector_nat orn_flist_flector_nat_inv in appendF as append_vectF_ind.
Print append_vectF_ind.

Lift induction orn_flist_flector_nat_inv orn_flist_flector_nat in append_vectF as appendF_ind.
Print appendF_ind.

(* tl *)

Definition tl (A : Type) (l : list A) :=
  @list_rect
    A
    (fun (l0 : list A) => list A)
    (@nil A)
    (fun (a : A) (l0 : list A) (_ : list A) =>
      l0)
    l.

(* This version might only work since we don't need the index of the IH *)
Definition tl_vect (A : Type) (pv : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => sigT (fun (n : nat) => vector A n))
    (existT (vector A) 0 (nilV A))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : sigT (fun (n : nat) => vector A n)) =>
      existT (vector A) n0 v0)
    (projT1 pv)
    (projT2 pv).

Lift induction orn_list_vector orn_list_vector_inv in tl as tl_vect_ind.
Print tl_vect_ind.

Lift induction orn_list_vector_inv orn_list_vector in tl_vect as tl_ind.
Print tl_ind.

(*
 * In as an application of an induction principle
 *)
Definition In (A : Type) (a : A) (l : list A) : Prop :=
  @list_rect
    A
    (fun (_ : list A) => Prop)
    False
    (fun (b : A) (l0 : list A) (IHl : Prop) =>
      a = b \/ IHl)
    l.

Definition In_vect (A : Type) (a : A) (pv : sigT (vector A)) : Prop :=
  @vector_rect
    A
    (fun (n1 : nat) (_ : vector A n1) => Prop)
    False
    (fun (n1 : nat) (b : A) (_ : vector A n1) (IHv : Prop) =>
      a = b \/ IHv)
    (projT1 pv)
    (projT2 pv).

Lift induction orn_list_vector orn_list_vector_inv in In as In_vect_ind.
Print In_vect_ind.

Lift induction orn_list_vector_inv orn_list_vector in In_vect as In_ind.
Print In_ind.

(* --- Interesting parts: Trying some proofs --- *)

Definition app_nil_r (A : Type) (l : list A) :=
  @list_ind
    A
    (fun (l0 : list A) => append A l0 (@nil A) = l0)
    (@eq_refl (list A) (@nil A))
    (fun (a : A) (l0 : list A) (IHl : append A l0 (@nil A) = l0) =>
      @eq_ind_r
        (list A)
        l0
        (fun (l1 : list A) => @cons A a l1 = @cons A a l0)
        (@eq_refl (list A) (@cons A a l0))
        (append A l0 (@nil A))
        IHl)
    l.

Definition app_nil_r_vect (A : Type) (pv : sigT (vector A)) :=
  vector_ind 
    A
    (fun (n0 : nat) (v0 : vector A n0) => 
      append_vect A (existT (vector A) n0 v0) (existT (vector A) O (nilV A)) = existT (vector A) n0 v0)
    (@eq_refl (sigT (vector A)) (existT (vector A) O (nilV A)))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IHp : append_vect A (existT (vector A) n0 v0) (existT (vector A) O (nilV A)) = existT (vector A) n0 v0) =>
      @eq_ind_r 
        (sigT (vector A)) 
        (existT (vector A) n0 v0)
        (fun (pv1 : sigT (vector A)) => 
          existT (vector A) (S (projT1 pv1)) (consV A (projT1 pv1) a (projT2 pv1)) = existT (vector A) (S n0) (consV A n0 a v0))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S n0) (consV A n0 a v0)))
        (append_vect A (existT (vector A) n0 v0) (existT (vector A) 0 (nilV A)))
        IHp)
    (projT1 pv) 
    (projT2 pv).

Lift induction orn_list_vector orn_list_vector_inv in app_nil_r as app_nil_r_vect_ind.
Print app_nil_r_vect_ind.

Lift induction orn_list_vector_inv orn_list_vector in app_nil_r_vect as app_nil_r_ind.
Print app_nil_r_ind.


aaa

(* app_nil_r with flectors *)

Definition app_nil_rF (l : natFlector.flist) :=
  natFlector.flist_ind
    (fun (l0 : natFlector.flist) => appendF l0 natFlector.nilF = l0)
    (@eq_refl natFlector.flist natFlector.nilF)
    (fun (a : nat) (l0 : natFlector.flist) (IHl : appendF l0 natFlector.nilF = l0) =>
      @eq_ind_r
        natFlector.flist
        l0
        (fun (l1 : natFlector.flist) => natFlector.consF a l1 = natFlector.consF a l0)
        (@eq_refl natFlector.flist (natFlector.consF a l0))
        (appendF l0 natFlector.nilF)
        IHl)
    l.

(* TODO opposite direction *)

Ornamental Application app_nil_r_vectF_auto from app_nil_rF using orn_flist_flector_nat orn_flist_flector_nat_inv.

(* in_split *)

Theorem in_split : 
  forall A x (l:list A), In A x l -> exists l1 l2, l = append A l1 (x::l2).
Proof.
  induction l; simpl; destruct 1.
  subst a; auto.
  exists nil, l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1), l2; simpl. apply f_equal. auto.
Defined. (* TODO any way around defined? *)

Ornamental Application in_split_vect_auto from in_split using orn_list_vector orn_list_vector_inv.

(* TODO opposite direction too *)
(* TODO prove it's OK *)

(*
 * Necessary to port proofs that use discriminate
 *)
Definition is_cons (A : Type) (l : list A) :=
  list_rect
    (fun (_ : list A) => Prop)
    False
    (fun (_ : A) (_ : list A) (_ : Prop) => True)
    l.

Ornamental Application is_cons_vect_auto from is_cons using orn_list_vector orn_list_vector_inv.

(* TODO port to induction everywhere, revisit
Lemma hd_error_tl_repr : forall A l (a:A) r,
  hd_error A l = Some a /\ tl A l = r <-> l = a :: r.
Proof. induction l.
  - unfold hd_error, tl; intros a r. split; firstorder discriminate.
  - intros. simpl. split.
   * intros (H1, H2). inversion H1. rewrite H2. reflexivity.
   * inversion 1. subst. auto.
Defined.

Ornamental Application hd_error_tl_repr_vect_auto from hd_error_tl_repr using orn_list_vector orn_list_vector_inv.
*)

(* ported to induction *)
Lemma hd_error_some_nil : forall A l (a:A), hd_error A l = Some a -> l <> nil.
Proof. 
  (*unfold hd_error. [TODO] *) induction l. (* destruct l; now disccriminate [ported below] *)
  - now discriminate.
  - simpl. intros. unfold not. intros.
    apply eq_ind with (P := is_cons A) in H0.
    * apply H0. 
    * simpl. auto. 
Defined.

Ornamental Application hd_error_some_nil_vect_auto from hd_error_some_nil using orn_list_vector orn_list_vector_inv.

(* --- Proofs that don't induct over list/vector. TODO can we do anything about these? --- *)

(*
Theorem nil_cons : 
  forall (A : Type) (x:A) (l:list A), nil <> x :: l.
Proof.
  intros; discriminate.
Qed.

Theorem nil_consV :
  forall (A : Type) (x:A) (pv : packed_vector A),
    (existT (vector A) 0 (nilV A)) <> (existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) x (projT2 pv))).
Proof.
  intros; discriminate.
Qed.

 (** Destruction *)

  Theorem destruct_list : forall (A : Type) (l : list A), {x:A & {tl:list A | l = x::tl}}+{l = nil}.
  Proof.
    induction l as [|a tail].
    right; reflexivity.
    left; exists a, tail; reflexivity.
  Qed.

Theorem hd_error_nil : 
  forall A, hd_error A (@nil A) = None.
Proof.
  simpl; reflexivity.
Qed.

Theorem hd_error_nil_vect :
  forall A, hd_vect_error_packed A (existT (vector A) 0 (nilV A)) = None.
Proof.
  simpl; reflexivity.
Qed.

(* TODO this is only actual worth doing anything with if you higher-lift [but it works]: *)
Ornamental Modularization hd_error_nil_red from hd_error_nil using orn_list_vector orn_list_vector_inv.

Theorem hd_error_cons : 
  forall A (l : list A) (x : A), hd_error A (x::l) = Some x.
Proof.
  intros; simpl; reflexivity.
Qed.

 *)

(* TODO decide what to do with these, see if can port, etc. *)

(* TODO the rest of the list library *)

(* --- *)

(* TODO non list/vect tests *)

(* TODO test more once basic code works at all *)
(* TODO try w/ eta, etc *)
(* TODO try types w/ indices in different places, a tree function, stuff from case studies *)
