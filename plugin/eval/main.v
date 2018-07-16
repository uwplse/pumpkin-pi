Require Import Ornamental.Ornaments.
Require Import PeanoNat Nat List Sorting.Permutation.
Require Import lemmas cast.
Import ListNotations.

Open Scope bool_scope.

Infix "==" := Nat.eqb (at level 70, no associativity) : nat_scope.
Infix "==>" := implb (at level 40, left associativity) : bool_scope.
Notation "x <= y" := (Nat.leb x y) (at level 70, y at next level, no associativity) : nat_scope.
Notation "p '.1'" := (projT1 p) (at level 20, left associativity).
Notation "p '.2'" := (projT2 p) (at level 20, left associativity).

Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.


Module Type Comparable.

  Parameter t : Type.
  Parameter leb : t -> t -> bool.
  Parameter refl : forall x, leb x x.
  Parameter antisym : forall x y, leb x y -> leb y x -> x = y.

  Definition eqb x y := leb x y && leb y x.
  Definition ltb x y := leb x y && negb (leb y x).

  Definition eqb_dec x y : if eqb x y then (x = y) else (x <> y).
  Proof.
    destruct (eqb x y) eqn:E; unfold eqb in E.
    - apply Bool.andb_true_iff in E as [E_l E_r]. apply antisym; [exact E_l|exact E_r].
    - apply Bool.andb_false_iff in E as [E|E]; intro H; rewrite H, refl in E; discriminate.
  Defined.

  Definition min x y := if leb x y then x else y.
  Definition max x y := if leb x y then y else x.

End Comparable.


Module CaseStudy (Elem : Comparable).

  Module Base.

    Inductive tree : Type :=
    | Branch (val : Elem.t) (left right : tree)
    | Leaf (val : Elem.t).

    Definition preorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => [x] ++ ys ++ zs)
        (fun x => [x])
        t.

    Definition inorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ [x] ++ zs)
        (fun x => [x])
        t.

    Definition postorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ zs ++ [x])
        (fun x => [x])
        t.

    Definition mirror (t : tree) : tree :=
      tree_rect
        (fun _ => tree)
        (fun v _ l _ r => Branch v r l)
        (fun v => Leaf v)
        t.

    Lemma pre_permutes : forall t : tree,
        permutes (preorder t) (inorder t).
    Proof.
      induction t; simpl.
      - apply perm_cons_app. apply perm_app; assumption.
      - apply perm_skip. apply perm_nil.
    Defined.

    Lemma post_permutes : forall t : tree,
        permutes (postorder t) (inorder t).
    Proof.
      induction t; simpl.
      - apply perm_app. assumption. apply perm_sym. apply perm_cons_app.
        rewrite app_nil_r. apply perm_sym. assumption.
      - apply perm_skip. apply perm_nil.
    Defined.

    Lemma pre_post_permutes : forall t : tree,
        permutes (preorder t) (postorder t).
    Proof.
      intro t. eapply perm_trans. apply pre_permutes.
      apply perm_sym, post_permutes.
    Defined.

    Lemma mirror_permutes : forall t : tree,
        permutes (inorder t) (inorder (mirror t)).
    Proof.
      induction t; simpl.
      - apply perm_sym. eapply perm_trans. apply perm_app_comm. simpl.
        apply perm_cons_app. apply perm_sym. apply perm_app; assumption.
      - apply perm_skip. apply perm_nil.
    Defined.

  End Base.

  Module Sized.

    Inductive tree : nat -> Type :=
    | Branch (n_l n_r : nat)
             (val : Elem.t)
             (left : tree n_l) (right : tree n_r)
      : tree (S (n_l + n_r))
    | Leaf (val : Elem.t) : tree (S O).

    Find ornament Base.tree tree as orn_size.

    Lift orn_size orn_size_inv in Base.preorder as preorder'.
    Definition preorder n t := preorder' (existT _ n t).

    Lift orn_size orn_size_inv in Base.inorder as inorder'.
    Definition inorder n t := inorder' (existT _ n t).

    Lift orn_size orn_size_inv in Base.postorder as postorder'.
    Definition postorder n t := postorder' (existT _ n t).

    Lift orn_size orn_size_inv in Base.mirror as mirror'.
    Definition mirror (n : nat) (t : tree n) : tree n.
      pose (T := (mirror' (existT _ n t))). replace n with (T.1). exact (T.2).
      induction t as [s_l s_r v t_l IH_l t_r IH_r|v]; [|reflexivity].
      cbn zeta in IH_l, IH_r. rewrite add_comm, <- IH_l, <- IH_r. reflexivity.
    Defined.

    Lift orn_size orn_size_inv in Base.pre_permutes as pre_permutes'.
    Definition pre_permutes (n : nat) (t : tree n) : permutes (preorder n t) (inorder n t) :=
      pre_permutes' (existT _ n t).

    Lift orn_size orn_size_inv in Base.post_permutes as post_permutes'.
    Definition post_permutes (n : nat) (t : tree n) : permutes (postorder n t) (inorder n t) :=
      post_permutes' (existT _ n t).

    Ornamental Modularization pre_post_permutes' from Base.pre_post_permutes using orn_size orn_size_inv.
    Definition pre_post_permutes (n : nat) (t : tree n) : permutes (preorder n t) (postorder n t) :=
      pre_post_permutes' (existT _ n t).

    Lift orn_size orn_size_inv in Base.mirror_permutes as mirror_permutes'.
    Lemma mirror_permutes (n : nat) (t : tree n) : permutes (inorder n t) (inorder n (mirror n t)).
    Proof.
      unfold inorder, mirror. rewrite cast_sigma. rewrite <- sigT_eta.
      set (T := existT _ n t). apply mirror_permutes'.
    Defined.

  End Sized.

  Module Measured.

    Inductive tree : nat -> Type :=
    | Branch (h_l h_r : nat)
             (val : Elem.t)
             (left : tree h_l) (right : tree h_r)
      : tree (S (Nat.max h_l h_r))
    | Leaf (val : Elem.t) : tree O.

    Find ornament Base.tree tree as orn_height.

    Lift orn_height orn_height_inv in Base.preorder as preorder'.
    Definition preorder h t := preorder' (existT _ h t).

    Lift orn_height orn_height_inv in Base.inorder as inorder'.
    Definition inorder h t := inorder' (existT _ h t).

    Lift orn_height orn_height_inv in Base.postorder as postorder'.
    Definition postorder h t := postorder' (existT _ h t).

    Lift orn_height orn_height_inv in Base.mirror as mirror'.
    Definition mirror (h : nat) (t : tree h) : tree h.
      set (T := (mirror' (existT _ h t))). replace h with (T.1). exact (T.2).
      induction t as [h_l h_r v t_l IH_l t_r IH_r|v]; [|reflexivity].
      cbn zeta in IH_l, IH_r. rewrite max_comm, <- IH_l, <- IH_r. reflexivity.
    Defined.

    Lift orn_height orn_height_inv in Base.pre_permutes as pre_permutes'.
    Definition pre_permutes (h : nat) (t : tree h) : permutes (preorder h t) (inorder h t) :=
      pre_permutes' (existT _ h t).

    Lift orn_height orn_height_inv in Base.post_permutes as post_permutes'.
    Definition post_permutes (h : nat) (t : tree h) : permutes (postorder h t) (inorder h t) :=
      post_permutes' (existT _ h t).

    Ornamental Modularization pre_post_permutes' from Base.pre_post_permutes using orn_height orn_height_inv.
    Definition pre_post_permutes (h : nat) (t : tree h) : permutes (preorder h t) (postorder h t) :=
      pre_post_permutes' (existT _ h t).

    Lift orn_height orn_height_inv in Base.mirror_permutes as mirror_permutes'.
    Lemma mirror_permutes (h : nat) (t : tree h) : permutes (inorder h t) (inorder h (mirror h t)).
    Proof.
      unfold inorder, mirror. rewrite cast_sigma. rewrite <- sigT_eta.
      set (T := existT _ h t). apply mirror_permutes'.
    Defined.

    (* Definition current (h : nat) (t : tree h) : Elem.t := *)
    (*   tree_rect *)
    (*     (fun _ _ => Elem.t) *)
    (*     (fun _ _ val _ _ _ _ => val) *)
    (*     (fun val => val) *)
    (*     h *)
    (*     t. *)

    (* Check (@nat_rect (fun _ => list Elem.t)). *)
    (* Check (@nat_rect (fun i => forall h, tree h -> list Elem.t)). *)
    (* Check (@tree_rect (fun h t => nat -> list Elem.t)). *)
    (* Definition level (h d : nat) (t : tree h) : list Elem.t := *)
    (*   tree_rect *)
    (*     (fun h t => nat -> list Elem.t) *)
    (*     (fun h_l h_r v t_l rec_l t_r rec_r d => *)
    (*        nat_rect *)
    (*          (fun _ => list Elem.t) *)
    (*          [v] *)
    (*          (fun d _ => rec_l d ++ rec_r d) *)
    (*          d) *)
    (*     (fun v d => *)
    (*        nat_rect (fun _ => list Elem.t) [v] (fun _ _ => []) d) *)
    (*     h *)
    (*     t *)
    (*     d. *)

    (* Definition sub (h : nat) (ts : list (tree (S h))) : list (tree h) := *)
    (*   tree_rect *)
    (*     (fun h => list (tree h) -> list Elem.t) *)
    (*     (row O) *)
    (*     (fun h rec ts => (row h ts) ++ (rec )) *)
    (*     h *)
    (*     [t]. *)

    (* Check (@nat_rect (fun i => forall h, tree h -> list Elem.t)). *)
    (* Definition roworder (h : nat) (t : tree h) : list Elem.t := *)
    (*   let row h ts := map (@current h) ts in *)
    (*   nat_rect *)
    (*     (fun h => list (tree h) -> list Elem.t) *)
    (*     (row O) *)
    (*     (fun h rec ts => (row h ts) ++ (rec )) *)
    (*     h *)
    (*     [t]. *)

    (*   tree_rect *)
    (*     (fun _ _ => list Elem.t) *)
    (*     (fun h_l h_r val l IH_l r IH_r => *)
    (*     ) *)

  End Measured.

  Module Heaped.

    Inductive _minheap : nat -> Elem.t -> Type :=
    | Branch_ (min_l min_r : Elem.t) (h_l h_r : nat) (val : Elem.t)
              (left : _minheap h_l min_l) (right : _minheap h_r min_r)
      : _minheap (S (Nat.max h_l h_r)) val
    | Leaf_ (val : Elem.t) : _minheap O val.

    Definition inv h_l h_r min_l min_r inv_l inv_r val : bool :=
      inv_l && inv_r && (h_l == h_r) && Elem.ltb min_l val && Elem.ltb min_r val.

    Inductive minheap : nat -> Elem.t -> bool -> Type :=
    | Branch (inv_l inv_r : bool) (min_l min_r : Elem.t) (h_l h_r : nat)
             (val : Elem.t)
             (left : minheap h_l min_l inv_l) (right : minheap h_r min_r inv_r)
      : minheap (S (Nat.max h_l h_r)) val (inv h_l h_r min_l min_r inv_l inv_r val)
    | Leaf (val : Elem.t) : minheap O val true.

    Find ornament Measured.tree _minheap as _orn_heap.
    Find ornament _minheap minheap as orn_heap.

    Lift _orn_heap _orn_heap_inv in Measured.preorder as _preorder'.
    Definition _preorder h min (t : _minheap h min) := _preorder' h (existT _ min t).
    Lift orn_heap orn_heap_inv in _preorder as preorder'.
    Definition preorder h min ord (t : minheap h min ord) := preorder' h min (existT _ ord t).

    Lift _orn_heap _orn_heap_inv in Measured.inorder as _inorder'.
    Definition _inorder h min (t : _minheap h min) := _inorder' h (existT _ min t).
    Lift orn_heap orn_heap_inv in _inorder as inorder'.
    Definition inorder h min ord (t : minheap h min ord) := inorder' h min (existT _ ord t).

    Lift _orn_heap _orn_heap_inv in Measured.postorder as _postorder'.
    Definition _postorder h min (t : _minheap h min) := _postorder' h (existT _ min t).
    Lift orn_heap orn_heap_inv in _postorder as postorder'.
    Definition postorder h min ord (t : minheap h min ord) := postorder' h min (existT _ ord t).

  End Heaped.

  Module Ordered.

    Inductive __bst : Elem.t -> Type :=
    | __Branch (min_l min_r : Elem.t)
               (val : Elem.t)
               (left : __bst min_l) (right : __bst min_r)
      : __bst min_l
    | __Leaf (val : Elem.t) : __bst val.

    Inductive _bst : Elem.t -> Elem.t -> Type :=
    | _Branch (min_l min_r : Elem.t) (max_l max_r : Elem.t)
              (val : Elem.t)
              (left : _bst min_l max_l) (right : _bst min_r max_r)
      : _bst min_l max_r
    | _Leaf (val : Elem.t) : _bst val val.

    Definition inv (ord_l ord_r : bool) (max_l val min_r : Elem.t) : bool :=
      ord_l && ord_r && Elem.ltb max_l val && Elem.ltb val min_r.

    Inductive bst : Elem.t -> Elem.t -> bool -> Type :=
    | Branch (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
             (val : Elem.t)
             (left : bst min_l max_l ord_l) (right : bst min_r max_r ord_r)
      : bst min_l max_r (inv ord_l ord_r max_l val min_r)
    | Leaf (val : Elem.t) : bst val val true.

    Find ornament Base.tree __bst as __orn_order.
    Find ornament __bst _bst as _orn_order.
    Find ornament _bst bst as orn_order.

    Lift __orn_order __orn_order_inv in Base.preorder as __preorder'.
    Definition __preorder min (tree : __bst min) := __preorder' (existT _ min tree).
    Lift _orn_order _orn_order_inv in __preorder as _preorder'.
    Definition _preorder min max (tree : _bst min max) := _preorder' min (existT _ max tree).
    Lift orn_order orn_order_inv in _preorder as preorder'.
    Definition preorder min max ord (tree : bst min max ord) := preorder' min max (existT _ ord tree).

    Lift __orn_order __orn_order_inv in Base.inorder as __inorder'.
    Definition __inorder min (tree : __bst min) := __inorder' (existT _ min tree).
    Lift _orn_order _orn_order_inv in __inorder as _inorder'.
    Definition _inorder min max (tree : _bst min max) := _inorder' min (existT _ max tree).
    Lift orn_order orn_order_inv in _inorder as inorder'.
    Definition inorder min max ord (tree : bst min max ord) := inorder' min max (existT _ ord tree).

    Lift __orn_order __orn_order_inv in Base.postorder as __postorder'.
    Definition __postorder min (tree : __bst min) := __postorder' (existT _ min tree).
    Lift _orn_order _orn_order_inv in __postorder as _postorder'.
    Definition _postorder min max (tree : _bst min max) := _postorder' min (existT _ max tree).
    Lift orn_order orn_order_inv in _postorder as postorder'.
    Definition postorder min max ord (tree : bst min max ord) := postorder' min max (existT _ ord tree).

    Definition search {min max ord} (tree : bst min max ord) (val' : Elem.t) : bool :=
      bst_rect
        (fun min max ord tree => bool)
        (fun ord_l ord_r min_l min_r max_l max_r val left IH_left right IH_right =>
           Elem.leb min_l val' &&
                    Elem.leb val' max_r &&
                    Elem.eqb val' val ||
           (Elem.leb val' max_l ==> IH_left) ||
           (Elem.leb min_r val' ==> IH_right))
        (fun val => Elem.eqb val' val)
        min max ord tree.

  End Ordered.

  Module Balanced.

    Inductive _avl : Elem.t -> Elem.t -> bool -> nat -> Type :=
    | _Branch (h_l h_r : nat) (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
              (val : Elem.t)
              (left : _avl min_l max_l ord_l h_l) (right : _avl min_r max_r ord_r h_r)
      : _avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) (S (Nat.max h_l h_r))
    | _Leaf (val : Elem.t) : _avl val val true O.

    Definition inv (bal_l bal_r : bool) (h_l h_r : nat) : bool :=
      bal_l && bal_r && (h_l - h_r <= 1) && (h_r - h_l <= 1).

    Inductive avl : Elem.t -> Elem.t -> bool -> nat -> bool -> Type :=
    | Branch (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
             (val : Elem.t)
             (left : avl min_l max_l ord_l h_l bal_l) (right : avl min_r max_r ord_r h_r bal_r)
      : avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) (S (Nat.max h_l h_r)) (inv bal_l bal_r h_l h_r)
    | Leaf (val : Elem.t) : avl val val true O true.

    Find ornament Ordered.bst _avl as _orn_balance.
    Find ornament _avl avl as orn_balance.

    Lift _orn_balance _orn_balance_inv in Ordered.preorder as _preorder'.
    Definition _preorder min max ord height (tree : _avl min max ord height) :=
      _preorder' min max ord (existT _ height tree).
    Lift orn_balance orn_balance_inv in _preorder as preorder'.
    Definition preorder min max ord height bal (tree : avl min max ord height bal) :=
      preorder' min max ord height (existT _ bal tree).

    Lift _orn_balance _orn_balance_inv in Ordered.inorder as _inorder'.
    Definition _inorder min max ord height (tree : _avl min max ord height) :=
      _inorder' min max ord (existT _ height tree).
    Lift orn_balance orn_balance_inv in _inorder as inorder'.
    Definition inorder min max ord height bal (tree : avl min max ord height bal) :=
      inorder' min max ord height (existT _ bal tree).

    Lift _orn_balance _orn_balance_inv in Ordered.postorder as _postorder'.
    Definition _postorder min max ord height (tree : _avl min max ord height) :=
      _postorder' min max ord (existT _ height tree).
    Lift orn_balance orn_balance_inv in _postorder as postorder'.
    Definition postorder min max ord height bal (tree : avl min max ord height bal) :=
      postorder' min max ord height (existT _ bal tree).

    Lift _orn_balance _orn_balance_inv in @Ordered.search as _search'.
    Definition _search {min max ord height} (tree : _avl min max ord height) (value : Elem.t) :=
      _search' min max ord (existT _ height tree) value.
    Lift orn_balance orn_balance_inv in @_search as search'.
    Definition search {min max ord height bal} (tree : avl min max ord height bal) value :=
      search' min max ord height (existT _ bal tree) value.

  End Balanced.

End CaseStudy.


Module NatComparable <: Comparable.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition refl (x : nat) : leb x x := Nat.leb_refl x.
  Lemma antisym (x y : nat) : leb x y -> leb y x -> x = y.
  Proof.
    revert y. induction x; destruct y; cbn; try reflexivity.
    - intros _ H. inversion H.
    - intros H. inversion H.
    - intros H_l H_r. specialize (IHx y H_l H_r). rewrite IHx. reflexivity.
  Defined.

  Definition eqb x y := leb x y && leb y x.
  Definition ltb x y := leb x y && negb (leb y x).
  Definition eqb_dec x y : if eqb x y then (x = y) else (x <> y).
  Proof.
    destruct (eqb x y) eqn:E; unfold eqb in E.
    - apply Bool.andb_true_iff in E as [E_l E_r]. apply antisym; [exact E_l|exact E_r].
    - apply Bool.andb_false_iff in E as [E|E]; intro H; rewrite H, refl in E; discriminate.
  Defined.

  Definition min x y := if leb x y then x else y.
  Definition max x y := if leb x y then y else x.

  Definition x := 0.
  Definition y := 3.
  Definition z := 7.
End NatComparable.


Module NatCaseStudy := CaseStudy NatComparable.
Import NatCaseStudy.
