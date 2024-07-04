Require Import Ornamental.Ornaments.
Require Import List Sorting.Permutation.
Require Import Foo.Test Foo.TestLift.

Notation "( x ; y )" := (existT _ x y) (no associativity).
Notation "p .1" := (projT1 p) (left associativity, at level 8, format "p .1").
Notation "p .2" := (projT2 p) (left associativity, at level 8, format "p .2").
Notation "p .&" := (p.1; p.2) (left associativity, at level 6, format "p .&").

Notation hdV := hd_vect_lifted.
Notation tlV := tl_vect_lifted.

Definition length {A : Type} (xs : list A) : nat :=
  list_rect
    (fun _ => nat)
    O
    (fun _ _ n => S n)
    xs.
Lift list vector in @length as lengthV.

(* Ex. 1: Promoting append relation from lists to vectors *)
Section Append.

  Inductive is_app {A : Type} : list A -> list A -> list A -> Type :=
  | is_app_cons (x : A) (xs ys zs : list A) :
      is_app xs ys zs ->
      is_app (x :: xs) ys (x :: zs)
  | is_app_nil (ys : list A) :
      is_app nil ys ys.
  Lift list vector in @is_app as ..V.

  (* Does the lifted type former have the expected type? *)
  Example check_is_appV
    : forall (A : Type) (xs ys zs : {n:nat & vector A n}), Type :=
    is_appV.

  (* Does the lifted constructor for is_app_cons have the expected type? *)
  Example check_is_app_consV
    : forall (A : Type) (x : A) (xs ys zs : {n:nat & vector A n}),
      is_appV A xs.& ys.& zs.& ->
      is_appV A
              (S xs.1; consV A xs.1 x xs.2)
              ys.&
              (S zs.1; consV A zs.1 x zs.2) :=
    is_app_consV.

  (* Does the lifted constructor for is_app_nil have the expected type? *)
  Example check_is_app_nilV
    : forall (A : Type) (ys : {n:nat & vector A n}),
      is_appV A (O; nilV A) ys.& ys.& :=
    is_app_nilV.

  (* Get the size of an is_app proof. *)
  Definition is_app_size {A : Type} (xs ys zs : list A) (H : is_app xs ys zs) : nat :=
    is_app_rect
      A
      (fun _ _ _ _ => nat)
      (fun _ _ _ _ _ IH => S IH)
      (fun _ => O)
      xs ys zs
      H.
  Lift list vector in @is_app_size as is_appV_size.

  Lemma is_app_size_len {A : Type} (xs ys zs : list A) (H : is_app xs ys zs) :
    is_app_size xs ys zs H = length xs.
  Proof.
    induction H; simpl; try rewrite IHis_app; reflexivity.
  Defined.
  Lift list vector in @is_app_size_len as is_appV_size_len.

  Lemma is_app_len {A : Type} (xs ys zs : list A) :
    is_app xs ys zs -> length xs + length ys = length zs.
  Proof.
    intro H. induction H; simpl.
    - rewrite IHis_app. reflexivity.
    - reflexivity.
  Defined.
  Lift list vector in @is_app_len as is_appV_len.

  Lemma is_app_tl (A : Type) (xs ys zs : list A) :
    is_app xs ys zs ->
    is_app (tl A xs) ys (match xs with cons _ _ => (tl A zs) | nil => zs end).
  Proof.
    intro H. induction H; simpl.
    - assumption.
    - constructor.
  Defined.
  Preprocess is_app_tl as is_app_tl'.
  Lift list vector in is_app_tl' as is_appV_tl.

  Lemma is_app_uncons (A : Type) (x : A) (xs ys zs : list A) :
    is_app (x :: xs) ys (x :: zs) -> is_app xs ys zs.
  Proof.
    remember (x :: xs) as xs' eqn:Exs. remember (x :: zs) as zs' eqn:Ezs.
    intro H. destruct H.
    - inversion Exs. inversion Ezs. rewrite H2, H4 in H. assumption.
    - inversion Exs.
  Defined.
  Preprocess is_app_uncons as is_app_uncons'.
  Lift list vector in is_app_uncons' as is_appV_uncons { opaque eq_rect_r }.

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
  Lift list vector in @perm as ..V.

  (* Does the lifted type former have the expected type? *)
  Example check_permV
    : forall (A : Type) (xs ys : {n:nat & vector A n}), Type :=
    permV.

  (* Does the lifted constructor for perm_nil have the expected type? *)
  Example check_perm_nilV
    : forall (A : Type), permV A (O; nilV A) (O; nilV A) :=
    perm_nilV.

  (* Does the lifted constructor for perm_skip have the expected type? *)
  Example check_perm_skipV
    : forall (A : Type) (x : A) (xs ys : {n:nat & vector A n}),
      permV A xs.& ys.& ->
      permV A
            (S xs.1; consV A xs.1 x xs.2)
            (S ys.1; consV A ys.1 x ys.2) :=
    perm_skipV.

  (* Does the lifted constructor for perm_swap have the expected type? *)
  Example check_perm_swapV
    : forall (A : Type) (x y : A) (xs : {n:nat & vector A n}),
      permV A
            (S (S xs.1); consV A (S xs.1) x (consV A xs.1 y xs.2))
            (S (S xs.1); consV A (S xs.1) y (consV A xs.1 x xs.2)) :=
    perm_swapV.

  (* Does the lifted constructor for perm_trans have the expected type? *)
  Example check_perm_transV
    : forall (A : Type) (xs ys zs : {n:nat & vector A n}),
      permV A xs.& ys.& -> permV A ys.& zs.& -> permV A xs.& zs.& :=
    perm_transV.

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
  Lift list vector in @perm_size as permV_size.

  Lemma perm_len {A : Type} (xs ys : list A) :
    perm xs ys -> length xs = length ys.
  Proof.
    intro H. induction H; simpl.
    - reflexivity.
    - rewrite IHperm. reflexivity.
    - reflexivity.
    - eapply eq_trans; eauto.
  Defined.
  Lift list vector in @perm_len as permV_len.

End Permute.
