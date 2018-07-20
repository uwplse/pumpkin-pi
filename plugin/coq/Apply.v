Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test Lift.

(*
 * TODO proofs at some point that this is OK
 *)

(* --- Interesting parts: Trying some proofs --- *)

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
