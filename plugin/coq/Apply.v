Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.

(*
 * Test applying ornaments to lift functions, without internalizing
 * the ornamentation (so the type won't be useful yet).
 *)

(* hd_error *)

Definition hd_error (A : Type) (l:list A) :=
  list_rect
    (fun (_ : list A) => option A)
    None
    (fun (x : A) (_ : list A) (_ : option A) =>
      Some x)
    l.

Definition hd_vect_error (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => option A)
    None
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : option A) =>
      Some x)
    n
    v.

Definition hd_vect_error_packed (A : Type) (pv : packed_vector A) :=
  hd_vect_error A (projT1 pv) (projT2 pv).

Ornamental Application hd_vect_error_auto from hd_error using orn_list_vector orn_list_vector_inv.
Ornamental Application hd_error_auto from hd_vect_error_packed using orn_list_vector_inv orn_list_vector.

(*
 * Same situation as above
 *)
Theorem test_orn_hd_error :
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error_auto A pv = hd_vect_error_packed A pv.
Proof.
  intros. induction pv; induction p; auto.
Qed.

Theorem test_orn_hd_error_proj :
  forall (A : Type) (n : nat) (v : vector A n),
    hd_vect_error_auto A (existT (vector A) n v) = hd_vect_error A n v.
Proof.
  intros. induction v; auto.
Qed.

Theorem test_deorn_hd_error :
  forall (A : Type) (a : A) (l : list A),
    hd_error_auto A l = hd_error A l.
Proof.
  intros. induction l; auto.
Qed.

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

(* For now, we don't eliminate the vector reference, since incides might refer to other things *)
Definition plus_vect (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => nat)
    n2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : nat) =>
      S (IH))
    n1
    v1.

(*
 * Not used yet.
 *)
Definition plus_vect_exp (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A) :=
  vector_rect
     A
     (fun (n0 : nat) (_ : vector A n0) => nat)
     (projT1 pv2)
     (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : nat) =>
        S IH)
     (projT1 pv1)
     (projT2 pv1).

Definition append_vect (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => vector A (plus_vect A n0 v0 n2 v2))
    v2
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : vector A (plus_vect A n0 v0 n2 v2)) =>
      consV A (plus_vect A n0 v0 n2 v2) a IH)
    n1
    v1.

(*
 * This version doesn't reference new indexer.
 * Eventually want to be able to get index from this too.
 *)
Definition append_vect_packed (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A) :=
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

Ornamental Application append_vect_auto from append using orn_list_vector orn_list_vector_inv.
Ornamental Application append_auto from append_vect_packed using orn_list_vector_inv orn_list_vector.

(*
 * For this one, we can't state the equality, but we can use existsT.
 *)
Lemma eq_S:
  forall n n',
    n = n' ->
    S n = S n'.
Proof.
  intros. subst. auto. 
Qed.

Lemma eq_vect_cons:
  forall A n (v : vector A n) n' (v' : vector A n'), 
    existT (vector A) n v = existT (vector A) n' v' ->
    forall (a : A),
      (existT (vector A) (S n) (consV A n a v)) =
      (existT (vector A) (S n') (consV A n' a v')).
Proof.
  intros. inversion H. subst. auto.
Qed.

Lemma eq_pv_cons:
  forall A (pv : sigT (vector A)) (pv' : sigT (vector A)),
    pv = pv' ->
    forall (a : A),
      (existT 
        (vector A)
        (S (projT1 pv)) 
        (consV A (projT1 pv) a (projT2 pv))) =
      (existT 
        (vector A)
        (S (projT1 pv')) 
        (consV A (projT1 pv') a (projT2 pv'))).
Proof.
  intros. inversion H. subst. auto.
Qed.

Lemma vect_iso:
  forall (A : Type) (pv : packed_vector A),
    pv = orn_list_vector A (orn_list_vector_inv A pv).
Proof.
  intros. induction pv. induction p; try apply eq_vect_cons; auto.
Qed.

Theorem test_plus:
  forall A (pv1 : packed_vector A) (pv2 : packed_vector A),
    (projT1 (append_vect_packed A pv1 pv2) = projT1 (append_vect_auto A pv1 pv2)).
Proof.
  intros. induction pv1; induction pv2; induction p; induction p0; try apply eq_S; auto.
Qed.

Theorem test_orn_append:
  forall A (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect_packed A pv1 pv2 = append_vect_auto A pv1 pv2.
Proof.
  intros. induction pv1.
  induction p.
  - unfold append_vect_auto. simpl. apply vect_iso.
  - apply eq_pv_cons with (a := a) in IHp. apply IHp.
Qed.

Theorem test_orn_append_proj :
  forall (A : Type) (n1 : nat) (v1 : vector A n1) (n2 : nat) (v2 : vector A n2),
    existT
      (vector A)
      (projT1 (append_vect_auto A (existT (vector A) n1 v1) (existT (vector A) n2 v2)))
      (projT2 (append_vect_auto A (existT (vector A) n1 v1) (existT (vector A) n2 v2))) =
    existT
      (vector A)
      (plus_vect A n1 v1 n2 v2)
      (append_vect A n1 v1 n2 v2).
Proof.
  intros. induction v1; induction v2; try apply eq_vect_cons; auto.
Qed.

(*
 * To prove the deornamentation case, we need the same lemma,
 * but we can state the equality directly.
 *)
Lemma eq_cons:
  forall A (l : list A) (l' : list A),
    l = l' ->
    forall (a : A), a :: l = a :: l'.
Proof.
  intros. inversion H. subst. auto.
Qed.

Lemma vect_inv_iso:
  forall (A : Type) (l : list A),
    l = orn_list_vector_inv A (orn_list_vector A l).
Proof.
  intros. induction l; try apply eq_cons; auto.
Qed.

Theorem append_cons:
  forall (A : Type) (a : A) (l l' : list A),
    append_auto A (a :: l) l' =
    a :: append_auto A l l'.
Proof.
  intros. unfold append_auto. induction l, l'; auto.
Qed.

Theorem test_deorn_append:
  forall A (l : list A) (l' : list A),
    append A l l' = append_auto A l l'.
Proof.
  intros. induction l, l'.
  - auto.
  - simpl. apply vect_inv_iso.
  - simpl. rewrite append_cons. apply eq_cons. apply IHl. 
  - simpl. rewrite append_cons. apply eq_cons. apply IHl. 
Qed.

(* append for flectors *)

Definition appendF (l1 : natFlector.flist) (l2 : natFlector.flist) :=
  natFlector.flist_rect
    (fun (_ : natFlector.flist) => natFlector.flist)
    l2
    (fun (a : nat) (_ : natFlector.flist) (IH : natFlector.flist) =>
      natFlector.consF a IH)
    l1.

(*
 * This version doesn't reference new indexer.
 * Eventually want to be able to get index from this too.
 *)
Definition append_vect_packedF (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector) :=
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

Ornamental Application append_vectF_auto from appendF using orn_flist_flector_nat orn_flist_flector_nat_inv.
Ornamental Application appendF_auto from append_vect_packedF using orn_flist_flector_nat_inv orn_flist_flector_nat.

(* TODO test before reduction *)

(* pred *)

(* For now, we don't eliminate the vector reference, since incides might refer to other things *)
Definition pred_vect (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => nat)
    0
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : nat) =>
      n0)
    n
    v.

Definition pred_vect_exp (A : Type) (pv : packed_vector A) :=
  pred_vect A (projT1 pv) (projT2 pv).

Definition tl (A : Type) (l : list A) :=
  @list_rect
   A
   (fun (l0 : list A) => list A)
   (@nil A)
   (fun (a : A) (l0 : list A) (_ : list A) =>
     l0)
   l.

Definition tl_vect (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
   A
   (fun (n0 : nat) (v0 : vector A n0) => vector A (pred_vect A n0 v0))
   (nilV A)
   (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : vector A (pred_vect A n0 v0)) =>
     v0)
   n
   v.

(* This version might only work since we don't need the index of the IH *)
Definition tl_vect_packed (A : Type) (pv : packed_vector A) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => sigT (fun (n : nat) => vector A n))
    (existT (vector A) 0 (nilV A))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : sigT (fun (n : nat) => vector A n)) =>
      existT (vector A) n0 v0)
    (projT1 pv)
    (projT2 pv).

Ornamental Application tl_vect_auto from tl using orn_list_vector orn_list_vector_inv.
Ornamental Application tl_auto from tl_vect_packed using orn_list_vector_inv orn_list_vector.

Lemma coh_vect:
  forall (A : Type) (n : nat) (v : vector A n),
    existT (vector A) (orn_list_vector_index A (orn_list_vector_inv A (existT (vector A) n v))) (projT2 (orn_list_vector A (orn_list_vector_inv A (existT (vector A) n v)))) = 
    existT (vector A) n v.
Proof.
  intros. induction v.
  - reflexivity.
  - apply eq_vect_cons. apply IHv.
Qed.

(*
 * Same situation as above
 *)
Theorem test_orn_tl :
  forall (A : Type) (pv : packed_vector A),
    tl_vect_auto A pv = tl_vect_packed A pv.
Proof.
  intros. induction pv; induction p; try apply coh_vect; auto.
Qed.

Theorem test_orn_tl_proj :
  forall (A : Type) (n : nat) (v : vector A n),
    existT
      (vector A)
      (projT1 (tl_vect_auto A (existT (vector A) n v)))
      (projT2 (tl_vect_auto A (existT (vector A) n v))) =
    existT
      (vector A)
      (pred_vect A n v)
      (tl_vect A n v).
Proof.
  intros. induction v; try apply coh_vect; auto.
Qed.

Lemma coh:
  forall (A : Type) (l : list A),
    orn_list_vector_inv A (existT (vector A) (orn_list_vector_index A l) (projT2 (orn_list_vector A l))) = l.
Proof.
  intros. induction l.
  - reflexivity.
  - apply eq_cons. apply IHl.
Qed.

Theorem test_deorn_tl :
  forall (A : Type) (l : list A),
    tl_auto A l = tl A l.
Proof.
  intros. induction l; try apply coh; auto.
Qed.

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

(* TODO what happens if you curry the vector_rect application? and so on *)

Ornamental Application In_vect_auto from In using orn_list_vector orn_list_vector_inv.
Ornamental Application In_auto from In_vect using orn_list_vector_inv orn_list_vector.

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
      append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0)
    (@eq_refl (sigT (vector A)) (existT (vector A) 0 (nilV A)))
    (fun (a : A) (l0 : list A) (IHl : append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0) =>
      @eq_ind_r
        (sigT (vector A))
        (orn_list_vector A l0)
        (fun (v1 : sigT (vector A)) => existT (vector A) (S (projT1 v1)) (consV A (projT1 v1) a (projT2 v1)) = existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0))))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0)))))
        (append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A))) 
        IHl)
    l.

(* what we can get without doing a higher lifting of append inside of the proof *)
Definition app_nil_r_lower_alt (A : Type) (l : list A) :=
  @list_ind
    A
    (fun (l0 : list A) => 
      append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0)
    (@eq_refl (sigT (vector A)) (existT (vector A) 0 (nilV A)))
    (fun (a : A) (l0 : list A) (IHl : append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0) =>
      @eq_ind_r
        (sigT (vector A))
        (orn_list_vector A l0)
        (fun (v1 : sigT (vector A)) => existT (vector A) (S (projT1 v1)) (consV A (projT1 v1) a (projT2 v1)) = existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0))))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0)))))
        (append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A))) 
        IHl)
    l.

(* packed vector version *)
Definition app_nil_r_vect_packed (A : Type) (pv : packed_vector A) :=
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
    (fun (l0 : list A) => append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0)
    (@eq_refl (packed_vector A) (existT (vector A) 0 (nilV A)))
    (fun (a : A) (l0 : list A) (IHl : append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)) = orn_list_vector A l0) =>
      @eq_ind_r
        (packed_vector A)
        (orn_list_vector A l0)
        (fun (pv : packed_vector A) => existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)) = existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0))))
        (@eq_refl (packed_vector A) (existT (vector A) (S (projT1 (orn_list_vector A l0))) (consV A (projT1 (orn_list_vector A l0)) a (projT2 (orn_list_vector A l0)))))
        (append_vect_packed A (orn_list_vector A l0) (existT (vector A) 0 (nilV A)))
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
