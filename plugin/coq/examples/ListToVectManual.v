(*
 * This is the only example given in the original Pumpkin Pi paper that had
 * a non-trivial eta term. That example had a trivial iota term. 
 * Here, we construct a configuration for the equivalence with trivial eta
 * but non-trivial iota. We manually repair a number of theorems where eta
 * was necessary with the old configuration. That we can do this manual repair
 * with a trivial eta term suggests that eta is actually not necessary for
 * repair at all, and that a configuration should really be comprised of
 * just three components: constructors, eliminators, and iota-reduction 
 * theorems.
 *)

Require Import Vector.
Require Import List.
Require Import ZArith.
Import ListNotations.

Require Import Ornamental.Ornaments.

Notation "( x ; y )" := (existT _ x y) (no associativity).
Notation "p .1" := (projT1 p) (left associativity, at level 8, format "p .1").
Notation "p .2" := (projT2 p) (left associativity, at level 8, format "p .2").
Notation "p .&" := (p.1; p.2) (left associativity, at level 6, format "p .&").

Notation vector := Vector.t.
Notation vnil := Vector.nil.
Notation vcons := Vector.cons.

(* --- Preprocess --- *)

Preprocess Module List as List' { opaque (* ignore these: *)
  RelationClasses
  Nat
  Coq.Init.Nat
                            }.

Definition pvec (A : Type) := {n : nat & vector A n}.

Definition depConstrNilList := @nil.
Definition depConstrConsList := @cons.

Definition depConstrNilVector (A : Type) := existT _ 0 (vnil A).
Definition depConstrConsVector (A : Type) (a : A) (v : {n : nat & vector A n}) :=
  existT _ (S (projT1 v)) (vcons A a (projT1 v) (projT2 v)).

Definition depElimList := @list_rect.

Print VectorDef.t_rect.

Definition depElimVector :
  forall (A : Type) (P : {H : nat & vector A H} -> Type),
    P (depConstrNilVector A) ->
    (forall (a : A) (l : {H : nat & vector A H}),
        P l -> P (depConstrConsVector A a l)) ->
    forall l : {H : nat & vector A H},
      P l.
Proof.
  intros.
  destruct l.
  induction t.
  - apply X.
  - apply (X0 h (existT _ n t)).
    apply IHt.
Defined.

Print depElimVector.

Definition iotaNilList (A : Type) (P : list A -> Type)
    (pnil : P (depConstrNilList A))
    (pcons : forall (a : A) (l : list A) (p : P l),
        P (depConstrConsList A a l))
    (Q : (P (depConstrNilList A)) -> Type) :
  Q (depElimList A P pnil pcons (depConstrNilList A)) -> Q pnil.
Proof.
  intros.
  auto.
Qed.
  
Definition iotaConsList (A : Type) (P : list A -> Type)
    (pnil : P (depConstrNilList A))
    (pcons : forall (a : A) (l : list A) (p : P l),
        P (depConstrConsList A a l))
    (a : A) (l : list A)
    (Q : (P (depConstrConsList A a l)) -> Type) :
    Q (depElimList A P pnil pcons (depConstrConsList A a l)) -> Q (pcons a l (depElimList A P pnil pcons l)). 
Proof.
  intros.
  auto.
Qed.

Definition iotaRevConsList (A : Type) (P : list A -> Type)
    (pnil : P (depConstrNilList A))
    (pcons : forall (a : A) (l : list A) (p : P l),
        P (depConstrConsList A a l))
    (a : A) (l : list A)
    (Q : (P (depConstrConsList A a l)) -> Type) :
    Q (pcons a l (depElimList A P pnil pcons l)) ->
    Q (depElimList A P pnil pcons (depConstrConsList A a l)).
Proof.
  intros.
  auto.
Qed.

Theorem eta_is_id {A : Type} : forall (l : pvec A), l = l.&.
Proof.
  intros.
  destruct l.
  reflexivity.
Qed.

Definition iotaNilVector (A : Type) (P :  pvec A -> Type)
    (pnil : P (depConstrNilVector A))
    (pcons : forall (a : A) (l : pvec A) (p : P l),
        P (depConstrConsVector A a l))
    (Q : (P (depConstrNilVector A)) -> Type) :
  Q (depElimVector A P pnil pcons (depConstrNilVector A)) -> Q pnil.
Proof.
  intros.
  apply X.
Qed.

Definition iotaConsVectorEq (A : Type) (P : pvec A -> Type)
    (pnil : P (depConstrNilVector A))
    (pcons : forall (a : A) (l : pvec A) (p : P l),
        P (depConstrConsVector A a l))
    (a : A) (l : pvec A)
    (Q : (P (depConstrConsVector A a l)) -> Type) :
  depElimVector A P pnil pcons (depConstrConsVector A a l) = pcons a l (depElimVector A P pnil pcons l).
Proof.
  destruct l.
  reflexivity.
Qed.
    
Definition iotaConsVector (A : Type) (P : pvec A -> Type)
    (pnil : P (depConstrNilVector A))
    (pcons : forall (a : A) (l : pvec A) (p : P l),
        P (depConstrConsVector A a l))
    (a : A) (l : pvec A)
    (Q : (P (depConstrConsVector A a l)) -> Type) :
    Q (depElimVector A P pnil pcons (depConstrConsVector A a l)) -> Q (pcons a l (depElimVector A P pnil pcons l)). 
Proof.
  intros.
  rewrite <- iotaConsVectorEq; auto.
Qed.

Definition iotaRevConsVector (A : Type) (P : pvec A -> Type)
    (pnil : P (depConstrNilVector A))
    (pcons : forall (a : A) (l : pvec A) (p : P l),
        P (depConstrConsVector A a l))
    (a : A) (l : pvec A)
    (Q : (P (depConstrConsVector A a l)) -> Type) :
    Q (pcons a l (depElimVector A P pnil pcons l)) ->
    Q (depElimVector A P pnil pcons (depConstrConsVector A a l)).
Proof.
  intros.
  rewrite iotaConsVectorEq; auto.
Qed.

Definition eta_list (A : Type) (l : list A) := l.

Definition eta_vector (A : Type) (v : pvec A) := v.

Definition f (A : Type) (l : list A) :=
  depElimList
    A
    (fun _ => pvec A)
    (depConstrNilVector A)
    (fun (a : A) (l : list A) (v : pvec A) => depConstrConsVector A a v)
    l.

Definition g (A : Type) (v : pvec A) :=
  depElimVector
    A
    (fun _ => list A)
    (depConstrNilList A)
    (fun (a : A) (v : pvec A) (l : list A) => depConstrConsList A a l)
    v.

Definition list_elim A P : P nil -> (forall x xs, P xs -> P (cons x xs)) -> forall xs, P xs :=
  fun H__nil H__cons xs => @list_rect A P H__nil H__cons xs.

Save equivalence list pvec { promote = f ; forget = g }.

Configure Lift list pvec {
    constrs_a = depConstrNilList depConstrConsList ;
    constrs_b = depConstrNilVector depConstrConsVector ;
    elim_a = depElimList ;
    elim_b = depElimVector ;
    eta_a = eta_list ;
    eta_b = eta_vector ;
    iota_a = iotaNilList iotaConsList iotaRevConsList ;
    iota_b = iotaNilVector iotaConsVector iotaRevConsVector
  }.

Definition listApp (A : Type) (l1 l2 : list A) : list A :=
  depElimList A (fun _ => list A) l2 (fun (a : A) (_ l : list A) => depConstrConsList A a l) l1.

Lift list pvec in listApp as vectorApp.

Theorem app_nil_r_list : forall (A : Type) (l : list A), listApp A l (depConstrNilList A) = l.
Proof.
  intros.
  apply (depElimList A (fun (l : list A) => listApp A l (depConstrNilList A) = l)).
  - reflexivity.
  - intros.
    unfold listApp.
    apply iotaRevConsList.
    unfold listApp in H.
    rewrite H.
    reflexivity.
Qed.

Lift list pvec in app_nil_r_list as app_nil_r_vector.

Print app_nil_r_vector.

Lift list pvec in depElimList as depElimVector'.

Print app_assoc.

Theorem app_assoc_list : forall (A : Type) (l m n : list A),
    listApp A l (listApp A m n) = listApp A (listApp A l m) n.
Proof.
  intros.
  apply (depElimList A (fun (l : list A) => listApp A l _ = listApp A (listApp A l m) n)).
  - reflexivity.
  - intros.
    unfold listApp.
    apply iotaRevConsList.
    apply iotaRevConsList.
    apply iotaRevConsList.
    unfold listApp in H.
    rewrite H.
    reflexivity.
Qed.
    
Lift list pvec in app_assoc_list as app_assoc_vector.

Print app_assoc_vector.

Theorem app_cons_not_nil_list_l : forall (A : Type) (l1 l2 : list A) (a : A), [] <> listApp A (depConstrConsList A a l1) l2.
Proof.
  intros.
  unfold listApp.
  apply iotaRevConsList.
  intros H.
  eapply (eq_ind [] (depElimList A (fun _ => Prop) True (fun _ _ _ => False)) I _ H).
Qed.

Lift list pvec in app_cons_not_nil_list_l as app_cons_not_nil_vector_l.

Print app_cons_not_nil_vector_l.

Print app_eq_nil.

Theorem app_eq_nil_list : forall (A : Type) (l l' : list A),
    listApp A l l' = depConstrNilList A -> l = depConstrNilList A /\ l' = depConstrNilList A.
Proof.
  intros.
  apply (depElimList A (fun (l : list A) => listApp A l l' = (depConstrNilList A) -> l = _ /\ l' = _)).
  - intros.
    split.
    + reflexivity.
    + simpl in H0.
      apply H0.
  - intros.
    generalize dependent l'.
    intro l'.
    apply (depElimList A (fun (l' : list A) => listApp A l l' = depConstrNilList A -> (listApp A l0 l' = depConstrNilList A -> l0 = depConstrNilList A /\ l' = depConstrNilList A) -> _ -> a :: l0 = depConstrNilList A /\ l' = depConstrNilList A)).
    + intros.
      symmetry in H1.
      apply app_cons_not_nil_list_l in H1.
      contradiction.
    + intros.
      symmetry in H2.
      apply app_cons_not_nil_list_l in H2.
      contradiction.
  - apply H.
Qed.

Print app_eq_nil_list.

Lift list pvec in app_eq_nil_list as app_eq_nil_vector.

Print app_eq_nil_vector.

Print app_nil_r_vector.
