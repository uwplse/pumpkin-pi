Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test Lift.

(*
 * TODO proofs at some point that this is OK
 *)

(* --- Interesting parts: Trying some proofs --- *)

(* This is our favorite proof app_nil_r, which has no exact analogue when
   indexing becomes relevant for vectors. *)
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

(* what we can get without doing a higher lifting of append inside of the proof *)
Definition app_nil_r_lower (A : Type) (l : list A) :=
  @list_ind
    A
    (fun (l0 : list A) => 
      append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0)
    (@eq_refl (sigT (vector A)) (existT (vector A) 0 (nilV A)))
    (fun (a : A) (l0 : list A) (IHl : append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0) =>
      @eq_ind_r
        (sigT (vector A))
        (orn_list_vector A l0)
        (fun (v1 : sigT (vector A)) => existT (vector A) (S (projT1 v1)) (consV A (projT1 v1) a (projT2 v1)) = existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0))))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0)))))
        (append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A))) 
        IHl)
    l.

(* what we can get without doing a higher lifting of append inside of the proof *)
Definition app_nil_r_lower_alt (A : Type) (l : list A) :=
  @list_ind
    A
    (fun (l0 : list A) => 
      append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0)
    (@eq_refl (sigT (vector A)) (existT (vector A) 0 (nilV A)))
    (fun (a : A) (l0 : list A) (IHl : append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0) =>
      @eq_ind_r
        (sigT (vector A))
        (orn_list_vector A l0)
        (fun (v1 : sigT (vector A)) => existT (vector A) (S (projT1 v1)) (consV A (projT1 v1) a (projT2 v1)) = existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0))))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0)))))
        (append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A))) 
        IHl)
    l.

(* packed vector version *)
Definition app_nil_r_vect_packed (A : Type) (pv : packed_vector A) :=
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

(* what we can get without doing a higher lifting of append inside of the proof *)
Definition app_nil_r_vect_packed_lower (A : Type) (pv : packed_vector A) :=
  vector_ind 
    A
    (fun (n0 : nat) (v0 : vector A n0) => 
      append A (orn_list_vector_inv A (existT (vector A) n0 v0)) (@nil A) = orn_list_vector_inv A (existT (vector A) n0 v0))
    (@eq_refl (list A) (@nil A))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IHp : append A (orn_list_vector_inv A (existT (vector A) n0 v0)) (@nil A) = orn_list_vector_inv A (existT (vector A) n0 v0)) =>
       @eq_ind_r 
       (list A) 
       (orn_list_vector_inv A (existT (vector A) n0 v0))
       (fun (pv1 : list A) => 
         @cons A a pv1 = @cons A a (orn_list_vector_inv A (existT (vector A) n0 v0)))
         (@eq_refl (list A) (@cons A a (orn_list_vector_inv A (existT (vector A) n0 v0))))
         (append A (orn_list_vector_inv A (existT (vector A) n0 v0)) (@nil A))
         IHp)
    (projT1 pv)
    (projT2 pv).

(* What happens if we try to immediately lift app_nil_r to use new app _before_ doing "lower" step? *)
Definition app_nil_r_higher (A : Type) (l : list A) :=
  @list_ind
    A
    (fun (l0 : list A) => append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0)
    (@eq_refl (packed_vector A) (existT (vector A) 0 (nilV A)))
    (fun (a : A) (l0 : list A) (IHl : append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0) =>
      @eq_ind_r
        (packed_vector A)
        (orn_list_vector A l0)
        (fun (pv : packed_vector A) => existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)) = existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0))))
        (@eq_refl (packed_vector A) (existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0)))))
        (append_vect A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)))
        IHl)
    l.

Ornamental Application app_nil_r_vect_auto from app_nil_r using orn_list_vector orn_list_vector_inv.
Ornamental Application app_nil_r_auto from app_nil_r_vect_packed using orn_list_vector_inv orn_list_vector.

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
