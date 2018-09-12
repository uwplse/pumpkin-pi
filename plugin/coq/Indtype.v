Add LoadPath "coq".
Require Import Ornamental.Ornaments.
Require Import List Sorting.Permutation.
Require Import Test Lift.

Notation "( x ; y )" := (existT _ x y) (no associativity).
Notation "p .1" := (projT1 p) (left associativity, at level 8).
Notation "p .2" := (projT2 p) (left associativity, at level 8).
Notation "p .&" := (p.1; p.2) (left associativity, at level 6).

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

  Fixpoint is_appV_rect_sig
           (A : Type)
           (P :
              forall (xs ys zs : {n:nat & vector A n}),
                is_appV A xs.& ys.& zs.& -> Type)
           (P_cons :
              forall (x : A) (xs ys zs : {n:nat & vector A n})
                     (tl : is_appV A xs.& ys.& zs.&),
                P xs.& ys.& zs.& tl ->
                P (S xs.1; consV A xs.1 x xs.2)
                  ys.&
                  (S zs.1; consV A zs.1 x zs.2)
                  (is_app_consV A x xs.& ys.& zs.& tl))
           (P_nil :
              forall (ys : {n:nat & vector A n}),
                P (O; nilV A) ys.& ys.& (is_app_nilV A ys))
           (xs ys zs : {n:nat & vector A n})
           (pf : is_appV A xs.& ys.& zs.&) {struct pf} :
    P xs.& ys.& zs.& pf :=
    match pf as pf in is_appV _ ((_; _) as xs) ((_; _) as ys) ((_; _) as zs) return P (xs.1; xs.2) (ys.1; ys.2) (zs.1; zs.2) pf with
    | is_app_consV _ x ((_; _) as xs') ((_; _) as ys') ((_; _) as zs') pf' =>
      P_cons x xs' ys' zs' pf' (is_appV_rect_sig A P P_cons P_nil xs' ys' zs' pf')
    | is_app_nilV _ ys' =>
      P_nil ys'
    end.

  Canonical Structure is_app_rect_lift : Lifted.t :=
    {| Lifted.base := is_app_rect;
       Lifted.lift := is_appV_rect_sig |}.

  Fixpoint is_appV_ind_sig
           (A : Type)
           (P :
              forall (xs ys zs : {n:nat & vector A n}),
                is_appV A xs.& ys.& zs.& -> Prop)
           (P_cons :
              forall (x : A) (xs ys zs : {n:nat & vector A n})
                     (tl : is_appV A xs.& ys.& zs.&),
                P xs.& ys.& zs.& tl ->
                P (S xs.1; consV A xs.1 x xs.2)
                  ys.&
                  (S zs.1; consV A zs.1 x zs.2)
                  (is_app_consV A x xs.& ys.& zs.& tl))
           (P_nil :
              forall (ys : {n:nat & vector A n}),
                P (O; nilV A) ys.& ys.& (is_app_nilV A ys))
           (xs ys zs : {n:nat & vector A n})
           (pf : is_appV A xs.& ys.& zs.&) {struct pf} :
    P xs.& ys.& zs.& pf :=
    match pf as pf in is_appV _ ((_; _) as xs) ((_; _) as ys) ((_; _) as zs) return P (xs.1; xs.2) (ys.1; ys.2) (zs.1; zs.2) pf with
    | is_app_consV _ x ((_; _) as xs') ((_; _) as ys') ((_; _) as zs') pf' =>
      P_cons x xs' ys' zs' pf' (is_appV_ind_sig A P P_cons P_nil xs' ys' zs' pf')
    | is_app_nilV _ ys' =>
      P_nil ys'
    end.

  Canonical Structure is_app_ind_lift : Lifted.t :=
    {| Lifted.base := is_app_ind;
       Lifted.lift := is_appV_ind_sig |}.

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

  Fixpoint permV_rect_sig
           (A : Type)
           (P :
              forall (xs ys : {n:nat & vector A n}),
                permV A xs.& ys.& -> Type)
           (P_nil : P (O; nilV A) (O; nilV A) (perm_nilV A))
           (P_skip :
              forall (x : A) (xs ys : {n:nat & vector A n})
                     (pf' : permV A xs.& ys.&),
                P xs.& ys.& pf' ->
                P (S xs.1; consV A xs.1 x xs.2)
                  (S ys.1; consV A ys.1 x ys.2)
                  (perm_skipV A x xs.& ys.& pf'))
           (P_swap :
              forall (x y : A) (xs : {n:nat & vector A n}),
                P (S (S xs.1); consV A (S xs.1) x (consV A xs.1 y xs.2))
                  (S (S xs.1); consV A (S xs.1) y (consV A xs.1 x xs.2))
                  (perm_swapV A x y xs.&))
           (P_trans :
              forall (xs ys zs : {n:nat & vector A n})
                     (pf' : permV A xs.& ys.&)
                     (_ : P xs.& ys.& pf')
                     (pf'' : permV A ys.& zs.&)
                     (_ : P ys.& zs.& pf''),
                P xs.& zs.& (perm_transV A xs.& ys.& zs.& pf' pf''))
           (xs ys : {n:nat & vector A n})
           (pf : permV A xs.& ys.&) {struct pf} :
    P xs.& ys.& pf :=
    match pf as pf in permV _ ((_; _) as xs) ((_; _) as ys) return P (xs.1; xs.2) (ys.1; ys.2) pf with
    | perm_nilV _ =>
      P_nil
    | perm_skipV _ x ((_; _) as xs') ((_; _) as ys') pf' =>
      P_skip x xs' ys' pf' (permV_rect_sig A P P_nil P_skip P_swap P_trans xs' ys' pf')
    | perm_swapV _ x y ((_; _) as xs') =>
      P_swap x y xs'
    | perm_transV _ ((_; _) as xs') ((_; _) as ys') ((_; _) as zs') pf' pf'' =>
      P_trans xs' ys' zs'
              pf' (permV_rect_sig A P P_nil P_skip P_swap P_trans xs' ys' pf')
              pf'' (permV_rect_sig A P P_nil P_skip P_swap P_trans ys' zs' pf'')
    end.

  Canonical Structure perm_rect_lift : Lifted.t :=
    {| Lifted.base := perm_rect;
       Lifted.lift := permV_rect_sig |}.

  Fixpoint permV_ind_sig
           (A : Type)
           (P :
              forall (xs ys : {n:nat & vector A n}),
                permV A xs.& ys.& -> Prop)
           (P_nil : P (O; nilV A) (O; nilV A) (perm_nilV A))
           (P_skip :
              forall (x : A) (xs ys : {n:nat & vector A n})
                     (pf' : permV A xs.& ys.&),
                P xs.& ys.& pf' ->
                P (S xs.1; consV A xs.1 x xs.2)
                  (S ys.1; consV A ys.1 x ys.2)
                  (perm_skipV A x xs.& ys.& pf'))
           (P_swap :
              forall (x y : A) (xs : {n:nat & vector A n}),
                P (S (S xs.1); consV A (S xs.1) x (consV A xs.1 y xs.2))
                  (S (S xs.1); consV A (S xs.1) y (consV A xs.1 x xs.2))
                  (perm_swapV A x y xs.&))
           (P_trans :
              forall (xs ys zs : {n:nat & vector A n})
                     (pf' : permV A xs.& ys.&)
                     (_ : P xs.& ys.& pf')
                     (pf'' : permV A ys.& zs.&)
                     (_ : P ys.& zs.& pf''),
                P xs.& zs.& (perm_transV A xs.& ys.& zs.& pf' pf''))
           (xs ys : {n:nat & vector A n})
           (pf : permV A xs.& ys.&) {struct pf} :
    P xs.& ys.& pf :=
    match pf as pf in permV _ ((_; _) as xs) ((_; _) as ys) return P (xs.1; xs.2) (ys.1; ys.2) pf with
    | perm_nilV _ =>
      P_nil
    | perm_skipV _ x ((_; _) as xs') ((_; _) as ys') pf' =>
      P_skip x xs' ys' pf' (permV_ind_sig A P P_nil P_skip P_swap P_trans xs' ys' pf')
    | perm_swapV _ x y ((_; _) as xs') =>
      P_swap x y xs'
    | perm_transV _ ((_; _) as xs') ((_; _) as ys') ((_; _) as zs') pf' pf'' =>
      P_trans xs' ys' zs'
              pf' (permV_ind_sig A P P_nil P_skip P_swap P_trans xs' ys' pf')
              pf'' (permV_ind_sig A P P_nil P_skip P_swap P_trans ys' zs' pf'')
    end.

  Canonical Structure perm_ind_lift : Lifted.t :=
    {| Lifted.base := perm_ind;
       Lifted.lift := permV_ind_sig |}.

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
