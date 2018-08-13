Add LoadPath "coq".
Require Import Ornamental.Ornaments.
Require Import List Sorting.Permutation.
Require Import Test Lift.

Notation "p .1" := (projT1 p) (left associativity, at level 8).
Notation "p .2" := (projT2 p) (left associativity, at level 8).
Notation "( x ; y )" := (existT _ x y) (no associativity).

Notation hdV := hd_vect_lifted.
Notation tlV := tl_vect_lifted.

Definition length {A : Type} (xs : list A) : nat :=
  list_rect
    (fun _ => nat)
    O
    (fun _ _ n => S n)
    xs.

Lift orn_list_vector orn_list_vector_inv in @length as lengthV.

(* Ex. 1: Promoting append relation from lists to vectors *)
Section Append.

  Inductive is_app {A : Type} : list A -> list A -> list A -> Type :=
  | is_app_cons (x : A) (xs ys zs : list A) :
      is_app xs ys zs ->
      is_app (x :: xs) ys (x :: zs)
  | is_app_nil (ys : list A) :
      is_app nil ys ys.

  Lift Inductive is_app by orn_list_vector orn_list_vector_inv with "V".
  Print is_appV.

  (* Get the size of an is_app proof. *)
  Definition is_app_size {A : Type} (xs ys zs : list A) (H : is_app xs ys zs) : nat :=
    is_app_rect
      A
      (fun _ _ _ _ => nat)
      (fun _ _ _ _ _ IH => S IH)
      (fun _ => O)
      xs ys zs
      H.
  Lift orn_list_vector orn_list_vector_inv in @is_app_size as is_appV_size.

  Lemma is_app_size_len {A : Type} (xs ys zs : list A) (H : is_app xs ys zs) :
    is_app_size xs ys zs H = length xs.
  Proof.
    induction H; simpl; try rewrite IHis_app; reflexivity.
  Defined.
  Lift orn_list_vector orn_list_vector_inv in @is_app_size_len as is_appV_size_len.

  Lemma is_app_len {A : Type} (xs ys zs : list A) :
    is_app xs ys zs -> length xs + length ys = length zs.
  Proof.
    intro H. induction H; simpl.
    - rewrite IHis_app. reflexivity.
    - reflexivity.
  Defined.
  Lift orn_list_vector orn_list_vector_inv in @is_app_len as is_appV_len.

  (* All the following liftings fail due to the eta-conversion bug. *)

  Lemma app_is_app {A : Type} (xs ys : list A) : is_app xs ys (app xs ys).
  Proof.
    induction xs; simpl; constructor; assumption.
  Defined.
  Fail Lift orn_list_vector orn_list_vector_inv in @app_is_app as appV_is_appV_ok.

  (* NOTE: Also needs match desugaring. *)
  Lemma is_app_tl {A : Type} (xs ys zs : list A) :
    is_app xs ys zs ->
    is_app (tl A xs) ys (match xs with cons _ _ => (tl A zs) | nil => zs end).
  Proof.
    intro H. induction H; simpl.
    - assumption.
    - constructor.
  Defined.
  Fail Lift orn_list_vector orn_list_vector_inv in @is_app_tl as is_appV_tl.

  (* NOTE: Also needs match desugaring. *)
  Lemma is_app_uncons (A : Type) (x : A) (xs ys zs : list A) :
    is_app (x :: xs) ys (x :: zs) -> is_app xs ys zs.
  Proof.
    remember (x :: xs) as xs' eqn:Exs. remember (x :: zs) as zs' eqn:Ezs.
    intro H. destruct H.
    - inversion Exs. inversion Ezs. rewrite H2, H4 in H. assumption.
    - inversion Exs.
  Defined.
  Fail Lift orn_list_vector orn_list_vector_inv in is_app_uncons as is_appV_uncons.

End Append.

(* Ex. 2: Promoting permutation relation from lists to vectors *)
Section Permute.

  Inductive perm {A : Type} : list A -> list A -> Type :=
  | perm_nil :
      perm nil nil
  | perm_skip (x : A) (xs ys : list A) :
      perm xs ys ->
      perm (x :: xs)
           (x :: ys)
  | perm_swap (x y : A) (xs : list A) :
      perm (x :: y :: xs)
           (y :: x :: xs)
  | perm_trans (xs ys zs : list A) :
      perm xs ys -> perm ys zs -> perm xs zs.

  Lift Inductive perm by orn_list_vector orn_list_vector_inv with "V".
  Print permV.

  (* Get the size of a perm proof. *)
  Definition perm_size {A : Type} (xs ys : list A) (H : perm xs ys) : nat :=
    perm_rect
      A
      (fun _ _ _ => nat)
      O
      (fun _ _ _ _ IH => S IH)
      (fun _ _ _ => O)
      (fun _ _ _ _ IH_l _ IH_r => S (IH_l + IH_r))
      xs ys H.
  Lift orn_list_vector orn_list_vector_inv in @perm_size as permV_size.

  Lemma perm_len {A : Type} (xs ys : list A) :
    perm xs ys -> length xs = length ys.
  Proof.
    intro H. induction H; simpl.
    - reflexivity.
    - rewrite IHperm. reflexivity.
    - reflexivity.
    - eapply eq_trans; eauto.
  Defined.
  Lift orn_list_vector orn_list_vector_inv in @perm_len as permV_len.

End Permute.
