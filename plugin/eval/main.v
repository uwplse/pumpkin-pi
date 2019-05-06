Require Import Ornamental.Ornaments.
Require Import PeanoNat Nat List Sorting.Permutation.
Require Import lemmas cast.
Import ListNotations.

(* Generate equivalences for use with EFF, and to ensure search is correct. *)
Set DEVOID search prove equivalence.

Open Scope bool_scope.

Infix "==" := Nat.eqb (at level 70, no associativity) : nat_scope.
Infix "==>" := implb (at level 40, left associativity) : bool_scope.
Notation "x <= y" := (Nat.leb x y) (at level 70, y at next level, no associativity) : nat_scope.
Notation "p '.1'" := (projT1 p) (at level 3, left associativity).
Notation "p '.2'" := (projT2 p) (at level 3, left associativity).

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

  Parameters x y z : t.

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

    (* --- Test trees --- *)
      Local Coercion Leaf : Elem.t >-> tree.

      (* 21 nodes, to be exact *)
      Definition tree20 :=
        Branch Elem.x
               (Branch Elem.y (Branch Elem.z (Branch Elem.x Elem.y Elem.z) (Branch Elem.x Elem.y Elem.z)) (Branch Elem.x Elem.y Elem.z))
               (Branch Elem.z (Branch Elem.x Elem.y Elem.z) (Branch Elem.x Elem.y (Branch Elem.x Elem.y Elem.z))).

      (* 43 nodes, to be exact *)
      Definition tree40 :=
        Branch Elem.z tree20 tree20.

      (* 65 nodes, to be exact *)
      Definition tree60 :=
        Branch Elem.y tree20 tree40.

      (* 87 nodes, to be exact *)
      Definition tree80 :=
        Branch Elem.x tree40 tree40.

      (* 109 nodes, to be exact *)
      Definition tree100 :=
        Branch Elem.y tree40 tree60.

      (* 219 nodes, to be exact *)
      Definition tree200 :=
        Branch Elem.x tree100 tree100.

      (* 439 nodes, to be exact *)
      Definition tree400 :=
        Branch Elem.y tree200 tree200.

      (* 659 nodes, to be exact *)
      Definition tree600 :=
        Branch Elem.x tree200 tree400.

      (* 879 nodes, to be exact *)
      Definition tree800 :=
        Branch Elem.z tree200 tree600.

      (* 1099 nodes, to be exact *)
      Definition tree1000 :=
        Branch Elem.x tree400 tree600.

      (* 2101 nodes, to be exact *)
      Definition tree2000 :=
        Branch Elem.y (Branch Elem.z tree200 tree800) tree1000.

      (* 4203 nodes, to be exact *)
      Definition tree4000 :=
        Branch Elem.x tree2000 tree2000.

      (* 6305 nodes, to be exact *)
      Definition tree6000 :=
        Branch Elem.z tree2000 tree4000.

      (* 8407 nodes, to be exact *)
      Definition tree8000 :=
        Branch Elem.z tree4000 tree4000.

      (* 10509 nodes, to be exact *)
      Definition tree10000 :=
        Branch Elem.z tree2000 tree8000.

    (* --- Let Coq warm up on each tree, so that base numbers aren't slower than they should be --- *)
    Redirect "out/tree20" Time Eval vm_compute in tree20.
    Redirect "out/tree40" Time Eval vm_compute in tree40.
    Redirect "out/tree60" Time Eval vm_compute in tree60.
    Redirect "out/tree80" Time Eval vm_compute in tree80.
    Redirect "out/tree100" Time Eval vm_compute in tree100.
    Redirect "out/tree2000" Time Eval vm_compute in tree2000.
    Redirect "out/tree4000" Time Eval vm_compute in tree4000.
    Redirect "out/tree6000" Time Eval vm_compute in tree6000.
    Redirect "out/tree8000" Time Eval vm_compute in tree8000.
    Redirect "out/tree10000" Time Eval vm_compute in tree10000.

    (* --- Base data --- *)
    Redirect "out/preorder/base2000" Time Eval vm_compute in (preorder tree2000).
    Redirect "out/preorder/base4000" Time Eval vm_compute in (preorder tree4000).
    Redirect "out/preorder/base6000" Time Eval vm_compute in (preorder tree6000).
    Redirect "out/preorder/base8000" Time Eval vm_compute in (preorder tree8000).
    Redirect "out/preorder/base10000" Time Eval vm_compute in (preorder tree10000).

    Redirect "out/inorder/base2000" Time Eval vm_compute in (inorder tree2000).
    Redirect "out/inorder/base4000" Time Eval vm_compute in (inorder tree4000).
    Redirect "out/inorder/base6000" Time Eval vm_compute in (inorder tree6000).
    Redirect "out/inorder/base8000" Time Eval vm_compute in (inorder tree8000).
    Redirect "out/inorder/base10000" Time Eval vm_compute in (inorder tree10000).

    Redirect "out/postorder/base2000" Time Eval vm_compute in (postorder tree2000).
    Redirect "out/postorder/base4000" Time Eval vm_compute in (postorder tree4000).
    Redirect "out/postorder/base6000" Time Eval vm_compute in (postorder tree6000).
    Redirect "out/postorder/base8000" Time Eval vm_compute in (postorder tree8000).
    Redirect "out/postorder/base10000" Time Eval vm_compute in (postorder tree10000).

    Redirect "out/preorder/base20" Time Eval vm_compute in (preorder tree20).
    Redirect "out/preorder/base40" Time Eval vm_compute in (preorder tree40).
    Redirect "out/preorder/base60" Time Eval vm_compute in (preorder tree60).
    Redirect "out/preorder/base80" Time Eval vm_compute in (preorder tree80).
    Redirect "out/preorder/base100" Time Eval vm_compute in (preorder tree100).

    Redirect "out/inorder/base20" Time Eval vm_compute in (inorder tree20).
    Redirect "out/inorder/base40" Time Eval vm_compute in (inorder tree40).
    Redirect "out/inorder/base60" Time Eval vm_compute in (inorder tree60).
    Redirect "out/inorder/base80" Time Eval vm_compute in (inorder tree80).
    Redirect "out/inorder/base100" Time Eval vm_compute in (inorder tree100).

    Redirect "out/postorder/base20" Time Eval vm_compute in (postorder tree20).
    Redirect "out/postorder/base40" Time Eval vm_compute in (postorder tree40).
    Redirect "out/postorder/base60" Time Eval vm_compute in (postorder tree60).
    Redirect "out/postorder/base80" Time Eval vm_compute in (postorder tree80).
    Redirect "out/postorder/base100" Time Eval vm_compute in (postorder tree100).
  End Base.

  (* --- Single iteration: from binary trees to sized binary trees --- *)

  Module Sized.

    Inductive tree : nat -> Type :=
    | Branch (n_l n_r : nat)
             (val : Elem.t)
             (left : tree n_l) (right : tree n_r)
      : tree (S (n_l + n_r))
    | Leaf (val : Elem.t) : tree (S O).

    Find ornament Base.tree tree as orn_size.

    (* --- Generated equivalences --- *)
    Redirect "out/equivalences/orn_size_index" Print orn_size_index.
    Redirect "out/equivalences/orn_size" Print orn_size.
    Redirect "out/equivalences/orn_size_inv" Print orn_size_inv.
    Redirect "out/equivalences/orn_size_section" Print orn_size_section.
    Redirect "out/equivalences/orn_size_retraction" Print orn_size_retraction.

    Lift Base.tree tree in Base.preorder as preorder'.
    Unpack preorder' as preorder.

    Lift Base.tree tree in Base.inorder as inorder'.
    Unpack inorder' as inorder.

    Lift Base.tree tree in Base.postorder as postorder'.
    Unpack postorder' as postorder.

    Lift Base.tree tree in Base.pre_permutes as pre_permutes'.
    Unpack pre_permutes' as pre_permutes.

    Lift Base.tree tree in Base.post_permutes as post_permutes'.
    Unpack post_permutes' as post_permutes.

    Lift Base.tree tree in Base.pre_post_permutes as pre_post_permutes'.
    Unpack pre_post_permutes' as pre_post_permutes.

    (* --- Lifted inputs --- *)
    Lift Base.tree tree in Base.tree2000 as tree2000.
    Lift Base.tree tree in Base.tree4000 as tree4000.
    Lift Base.tree tree in Base.tree6000 as tree6000.
    Lift Base.tree tree in Base.tree8000 as tree8000.
    Lift Base.tree tree in Base.tree10000 as tree10000.

    (* --- Sized data --- *)
    Redirect "out/preorder/sized2000" Time Eval vm_compute in (preorder' tree2000).
    Redirect "out/preorder/sized4000" Time Eval vm_compute in (preorder' tree4000).
    Redirect "out/preorder/sized6000" Time Eval vm_compute in (preorder' tree6000).
    Redirect "out/preorder/sized8000" Time Eval vm_compute in (preorder' tree8000).
    Redirect "out/preorder/sized10000" Time Eval vm_compute in (preorder' tree10000).

    Redirect "out/inorder/sized2000" Time Eval vm_compute in (inorder' tree2000).
    Redirect "out/inorder/sized4000" Time Eval vm_compute in (inorder' tree4000).
    Redirect "out/inorder/sized6000" Time Eval vm_compute in (inorder' tree6000).
    Redirect "out/inorder/sized8000" Time Eval vm_compute in (inorder' tree8000).
    Redirect "out/inorder/sized10000" Time Eval vm_compute in (inorder' tree10000).

    Redirect "out/postorder/sized2000" Time Eval vm_compute in (postorder' tree2000).
    Redirect "out/postorder/sized4000" Time Eval vm_compute in (postorder' tree4000).
    Redirect "out/postorder/sized6000" Time Eval vm_compute in (postorder' tree6000).
    Redirect "out/postorder/sized8000" Time Eval vm_compute in (postorder' tree8000).
    Redirect "out/postorder/sized10000" Time Eval vm_compute in (postorder' tree10000).

    (* --- Normalized term sizes --- *)
    Redirect "out/normalized/preorder-sized" Eval compute in preorder'.
    Redirect "out/normalized/postorder-sized" Eval compute in postorder'.
    Redirect "out/normalized/inorder-sized" Eval compute in inorder'.
    Redirect "out/normalized/pre_permutes-sized" Eval compute in pre_permutes'.
  End Sized.

  (* --- Multiple iterations: from binary trees to binary search trees to AVL trees --- *)

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

    (* Invariant for fitting into algebraic ornaments *)
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

    (* --- Generated equivalences --- *)
    Redirect "out/equivalences/__orn_order_index" Print __orn_order_index.
    Redirect "out/equivalences/__orn_order" Print __orn_order.
    Redirect "out/equivalences/__orn_order_inv" Print __orn_order_inv.
    Redirect "out/equivalences/__orn_order_section" Print __orn_order_section.
    Redirect "out/equivalences/__orn_order_retraction" Print __orn_order_retraction.
    Redirect "out/equivalences/_orn_order_index" Print _orn_order_index.
    Redirect "out/equivalences/_orn_order" Print _orn_order.
    Redirect "out/equivalences/_orn_order_inv" Print _orn_order_inv.
    Redirect "out/equivalences/_orn_order_section" Print _orn_order_section.
    Redirect "out/equivalences/_orn_order_retraction" Print _orn_order_retraction.
    Redirect "out/equivalences/orn_order_index" Print orn_order_index.
    Redirect "out/equivalences/orn_order" Print orn_order.
    Redirect "out/equivalences/orn_order_inv" Print orn_order_inv.
    Redirect "out/equivalences/orn_order_section" Print orn_order_section.
    Redirect "out/equivalences/orn_order_retraction" Print orn_order_retraction.

    Lift Base.tree __bst in Base.preorder as __preorder'.
    Unpack __preorder' as __preorder.
    Lift __bst _bst in __preorder as _preorder'.
    Unpack _preorder' as _preorder.
    Lift _bst bst in _preorder as preorder'.
    Unpack preorder' as preorder.

    Lift Base.tree __bst in Base.inorder as __inorder'.
    Unpack __inorder' as __inorder.
    Lift __bst _bst in __inorder as _inorder'.
    Unpack _inorder' as _inorder.
    Lift _bst bst in _inorder as inorder'.
    Unpack inorder' as inorder.

    Lift Base.tree __bst in Base.postorder as __postorder'.
    Unpack __postorder' as __postorder.
    Lift __bst _bst in __postorder as _postorder'.
    Unpack _postorder' as _postorder.
    Lift _bst bst in _postorder as postorder'.
    Unpack postorder' as postorder.

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

     (* --- Lifted inputs --- *)
     (* Small *)
     Lift Base.tree __bst in Base.tree20 as __tree20.
     Lift __bst _bst in __tree20 as _tree20. 
     Lift _bst bst in _tree20 as tree20'''.
     Unpack tree20''' as tree20''.
     Unpack tree20'' as tree20'.
     Unpack tree20' as tree20.
     Lift Base.tree __bst in Base.tree40 as __tree40.
     Lift __bst _bst in __tree40 as _tree40. 
     Lift _bst bst in _tree40 as tree40'''.
     Unpack tree40''' as tree40''.
     Unpack tree40'' as tree40'.
     Unpack tree40' as tree40.
     Lift Base.tree __bst in Base.tree60 as __tree60.
     Lift __bst _bst in __tree60 as _tree60. 
     Lift _bst bst in _tree60 as tree60'''.
     Unpack tree60''' as tree60''.
     Unpack tree60'' as tree60'.
     Unpack tree60' as tree60.
     Lift Base.tree __bst in Base.tree80 as __tree80.
     Lift __bst _bst in __tree80 as _tree80. 
     Lift _bst bst in _tree80 as tree80'''.
     Unpack tree80''' as tree80''.
     Unpack tree80'' as tree80'.
     Unpack tree80' as tree80.
     Lift Base.tree __bst in Base.tree100 as __tree100.
     Lift __bst _bst in __tree100 as _tree100. 
     Lift _bst bst in _tree100 as tree100'''.
     Unpack tree100''' as tree100''.
     Unpack tree100'' as tree100'.
     Unpack tree100' as tree100.

    (* --- Let Coq warm up on each tree, so that base numbers aren't slower than they should be --- *)
    Redirect "out/tree20" Time Eval vm_compute in tree20.
    Redirect "out/tree40" Time Eval vm_compute in tree40.
    Redirect "out/tree60" Time Eval vm_compute in tree60.
    Redirect "out/tree80" Time Eval vm_compute in tree80.
    Redirect "out/tree100" Time Eval vm_compute in tree100.

    (* --- Base search data --- *)
    Redirect "out/search/base20" Time Eval vm_compute in (search tree20 Elem.x).
    Redirect "out/search/base40" Time Eval vm_compute in (search tree40 Elem.x).
    Redirect "out/search/base60" Time Eval vm_compute in (search tree60 Elem.x).
    Redirect "out/search/base80" Time Eval vm_compute in (search tree80 Elem.x).
    Redirect "out/search/base100" Time Eval vm_compute in (search tree100 Elem.x).
  End Ordered.

  Module Balanced.

    Inductive _avl : Elem.t -> Elem.t -> bool -> nat -> Type :=
    | _Branch (h_l h_r : nat) (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
              (val : Elem.t)
              (left : _avl min_l max_l ord_l h_l) (right : _avl min_r max_r ord_r h_r)
      : _avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) (S (Nat.max h_l h_r))
    | _Leaf (val : Elem.t) : _avl val val true O.

    (* Invariant for fitting into algebraic ornaments *)
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

    (* --- Generated equivalences --- *)
    Redirect "out/equivalences/_orn_balance_index" Print _orn_balance_index.
    Redirect "out/equivalences/_orn_balance" Print _orn_balance.
    Redirect "out/equivalences/_orn_balance_inv" Print _orn_balance_inv.
    Redirect "out/equivalences/_orn_balance_section" Print _orn_balance_section.
    Redirect "out/equivalences/_orn_balance_retraction" Print _orn_balance_retraction.
    Redirect "out/equivalences/orn_balance_index" Print orn_balance_index.
    Redirect "out/equivalences/orn_balance" Print orn_balance.
    Redirect "out/equivalences/orn_balance_inv" Print orn_balance_inv.
    Redirect "out/equivalences/orn_balance_section" Print orn_balance_section.
    Redirect "out/equivalences/orn_balance_retraction" Print orn_balance_retraction.

    Lift Ordered.bst _avl in Ordered.preorder as _preorder'.
    Unpack _preorder' as _preorder.
    Lift _avl avl in _preorder as preorder'.
    Unpack preorder' as preorder.

    Lift Ordered.bst _avl in Ordered.inorder as _inorder'.
    Unpack _inorder' as _inorder.
    Lift _avl avl in _inorder as inorder'.
    Unpack inorder' as inorder.

    Lift Ordered.bst _avl in Ordered.postorder as _postorder'.
    Unpack _postorder' as _postorder.
    Lift _avl avl in _postorder as postorder'.
    Unpack postorder' as postorder.

    Lift Ordered.bst _avl in @Ordered.search as _search'.
    Unpack _search' as _search.
    Lift _avl avl in @_search as search'.
    Unpack search' as search.
    Arguments search {_ _ _ _ _} _ _.

    (* --- Lifted inputs --- *)
    (* Small: *)
    Lift Ordered.bst _avl in Ordered.tree20''' as _tree20.
    Lift _avl avl in _tree20 as tree20''''.
    Unpack tree20'''' as tree20'''.
    Unpack tree20''' as tree20''.
    Unpack tree20'' as tree20'.
    Unpack tree20' as tree20.
    Lift Ordered.bst _avl in Ordered.tree40''' as _tree40.
    Lift _avl avl in _tree40 as tree40''''.
    Unpack tree40'''' as tree40'''.
    Unpack tree40''' as tree40''.
    Unpack tree40'' as tree40'.
    Unpack tree40' as tree40.
    Lift Ordered.bst _avl in Ordered.tree60''' as _tree60.
    Lift _avl avl in _tree60 as tree60''''.
    Unpack tree60'''' as tree60'''.
    Unpack tree60''' as tree60''.
    Unpack tree60'' as tree60'.
    Unpack tree60' as tree60.
    Lift Ordered.bst _avl in Ordered.tree80''' as _tree80.
    Lift _avl avl in _tree80 as tree80''''.
    Unpack tree80'''' as tree80'''.
    Unpack tree80''' as tree80''.
    Unpack tree80'' as tree80'.
    Unpack tree80' as tree80.
    Lift Ordered.bst _avl in Ordered.tree100''' as _tree100.
    Lift _avl avl in _tree100 as tree100''''.
    Unpack tree100'''' as tree100'''.
    Unpack tree100''' as tree100''.
    Unpack tree100'' as tree100'.
    Unpack tree100' as tree100.

    (* --- AVL data --- *)
    Redirect "out/preorder/avl20" Time Eval vm_compute in (preorder' _ _ _ _ tree20).
    Redirect "out/preorder/avl40" Time Eval vm_compute in (preorder' _ _ _ _ tree40).
    Redirect "out/preorder/avl60" Time Eval vm_compute in (preorder' _ _ _ _ tree60).
    Redirect "out/preorder/avl80" Time Eval vm_compute in (preorder' _ _ _ _ tree80).
    Redirect "out/preorder/avl100" Time Eval vm_compute in (preorder' _ _ _ _ tree100).

    Redirect "out/inorder/avl20" Time Eval vm_compute in (inorder' _ _ _ _ tree20).
    Redirect "out/inorder/avl40" Time Eval vm_compute in (inorder' _ _ _ _ tree40).
    Redirect "out/inorder/avl60" Time Eval vm_compute in (inorder' _ _ _ _ tree60).
    Redirect "out/inorder/avl80" Time Eval vm_compute in (inorder' _ _ _ _ tree80).
    Redirect "out/inorder/avl100" Time Eval vm_compute in (inorder' _ _ _ _ tree100).

    Redirect "out/postorder/avl20" Time Eval vm_compute in (postorder' _ _ _ _ tree20).
    Redirect "out/postorder/avl40" Time Eval vm_compute in (postorder' _ _ _ _ tree40).
    Redirect "out/postorder/avl60" Time Eval vm_compute in (postorder' _ _ _ _ tree60).
    Redirect "out/postorder/avl80" Time Eval vm_compute in (postorder' _ _ _ _ tree80).
    Redirect "out/postorder/avl100" Time Eval vm_compute in (postorder' _ _ _ _ tree100).

    Redirect "out/search/avl20" Time Eval vm_compute in (search' _ _ _ _ tree20 Elem.x).
    Redirect "out/search/avl40" Time Eval vm_compute in (search' _ _ _ _ tree40 Elem.x).
    Redirect "out/search/avl60" Time Eval vm_compute in (search' _ _ _ _ tree60 Elem.x).
    Redirect "out/search/avl80" Time Eval vm_compute in (search' _ _ _ _ tree80 Elem.x).
    Redirect "out/search/avl100" Time Eval vm_compute in (search' _ _ _ _ tree100 Elem.x).

    (* --- Normalized term sizes --- *)
    Redirect "out/normalized/preorder-avl" Eval compute in preorder'.
    Redirect "out/normalized/postorder-avl" Eval compute in postorder'.
    Redirect "out/normalized/inorder-avl" Eval compute in inorder'.
    Redirect "out/normalized/search-avl" Eval compute in search'.
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
