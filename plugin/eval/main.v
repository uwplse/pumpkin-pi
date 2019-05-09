Require Import Ornamental.Ornaments.
Require Import PeanoNat Nat List Sorting.Permutation.
Require Import lemmas cast.
Import ListNotations.

(* Generate equivalences for use with EFF, and to ensure search is correct. *)
Set DEVOID search prove equivalence.

(* Set a timeout for Coq commands *)
Set Default Timeout 100.

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

      (* 1 node *)
      Definition tree1 :=
        Leaf Elem.y.

      (* 11 nodes, to be exact *)
      Definition tree10 :=
        Branch Elem.y (Branch Elem.z (Branch Elem.x Elem.y Elem.z) (Branch Elem.x Elem.y Elem.z)) (Branch Elem.x Elem.y Elem.z).

      (* 21 nodes, to be exact *)
      Definition tree20 :=
        Branch Elem.x tree10
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

    (* --- Print the inputs for control purposes for EFF code --- *)
    Redirect "out/inputs/tree1-base" Print tree1.
    Redirect "out/inputs/tree10-base" Print tree10.
    Redirect "out/inputs/tree20-base" Print tree20.
    Redirect "out/inputs/tree40-base" Print tree40.
    Redirect "out/inputs/tree60-base" Print tree60.
    Redirect "out/inputs/tree80-base" Print tree80.
    Redirect "out/inputs/tree100-base" Print tree100.
    Redirect "out/inputs/tree200-base" Print tree200.
    Redirect "out/inputs/tree400-base" Print tree400.
    Redirect "out/inputs/tree600-base" Print tree600.
    Redirect "out/inputs/tree800-base" Print tree800.
    Redirect "out/inputs/tree1000-base" Print tree1000.
    Redirect "out/inputs/tree2000-base" Print tree2000.
    Redirect "out/inputs/tree4000-base" Print tree4000.
    Redirect "out/inputs/tree6000-base" Print tree6000.
    Redirect "out/inputs/tree8000-base" Print tree8000.
    Redirect "out/inputs/tree10000-base" Print tree10000.

    (* --- Base data --- *)
    Redirect "out/preorder/base1" Time Eval vm_compute in (preorder tree1).
    Redirect "out/preorder/base10" Time Eval vm_compute in (preorder tree10).
    Redirect "out/preorder/base100" Time Eval vm_compute in (preorder tree100).
    Redirect "out/preorder/base1000" Time Eval vm_compute in (preorder tree1000).
    Redirect "out/preorder/base10000" Time Eval vm_compute in (preorder tree10000).

    Redirect "out/inorder/base1" Time Eval vm_compute in (inorder tree1).
    Redirect "out/inorder/base10" Time Eval vm_compute in (inorder tree10).
    Redirect "out/inorder/base100" Time Eval vm_compute in (inorder tree100).
    Redirect "out/inorder/base1000" Time Eval vm_compute in (inorder tree1000).
    Redirect "out/inorder/base10000" Time Eval vm_compute in (inorder tree10000).

    Redirect "out/postorder/base1" Time Eval vm_compute in (postorder tree1).
    Redirect "out/postorder/base10" Time Eval vm_compute in (postorder tree10).
    Redirect "out/postorder/base100" Time Eval vm_compute in (postorder tree100).
    Redirect "out/postorder/base1000" Time Eval vm_compute in (postorder tree1000).
    Redirect "out/postorder/base10000" Time Eval vm_compute in (postorder tree10000).
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
    (* 
     * For large constants, lifting intermediate terms helps with caching for performance.
     * Note that we don't measure lifting performance or performance for large constants,
     * and in the together version of the case study, we run on EFF's lifted constants anyways.
     *)
    Lift Base.tree tree in Base.tree1 as tree1.
    Lift Base.tree tree in Base.tree10 as tree10.
    Lift Base.tree tree in Base.tree20 as tree20.
    Lift Base.tree tree in Base.tree40 as tree40.
    Lift Base.tree tree in Base.tree60 as tree60.
    Lift Base.tree tree in Base.tree80 as tree80.
    Lift Base.tree tree in Base.tree100 as tree100.
    Lift Base.tree tree in Base.tree200 as tree200.
    Lift Base.tree tree in Base.tree400 as tree400.
    Lift Base.tree tree in Base.tree600 as tree600.
    Lift Base.tree tree in Base.tree800 as tree800.
    Lift Base.tree tree in Base.tree1000 as tree1000.
    Lift Base.tree tree in Base.tree2000 as tree2000.
    Lift Base.tree tree in Base.tree4000 as tree4000.
    Lift Base.tree tree in Base.tree6000 as tree6000.
    Lift Base.tree tree in Base.tree8000 as tree8000.
    Lift Base.tree tree in Base.tree10000 as tree10000.

    (* --- Print the inputs for control purposes for EFF code --- *)
    Redirect "out/inputs/tree1-sized" Print tree1.
    Redirect "out/inputs/tree10-sized" Print tree10.
    Redirect "out/inputs/tree20-sized" Print tree20.
    Redirect "out/inputs/tree40-sized" Print tree40.
    Redirect "out/inputs/tree60-sized" Print tree60.
    Redirect "out/inputs/tree80-sized" Print tree80.
    Redirect "out/inputs/tree100-sized" Print tree100.
    Redirect "out/inputs/tree200-sized" Print tree200.
    Redirect "out/inputs/tree400-sized" Print tree400.
    Redirect "out/inputs/tree600-sized" Print tree600.
    Redirect "out/inputs/tree800-sized" Print tree800.
    Redirect "out/inputs/tree1000-sized" Print tree1000.
    Redirect "out/inputs/tree2000-sized" Print tree2000.
    Redirect "out/inputs/tree4000-sized" Print tree4000.
    Redirect "out/inputs/tree6000-sized" Print tree6000.
    Redirect "out/inputs/tree8000-sized" Print tree8000.
    Redirect "out/inputs/tree10000-sized" Print tree10000.

    (* --- Sized data --- *)
    Redirect "out/preorder/sized1" Time Eval vm_compute in (preorder' tree1).
    Redirect "out/preorder/sized10" Time Eval vm_compute in (preorder' tree10).
    Redirect "out/preorder/sized100" Time Eval vm_compute in (preorder' tree100).
    Redirect "out/preorder/sized1000" Time Eval vm_compute in (preorder' tree1000).
    Redirect "out/preorder/sized10000" Time Eval vm_compute in (preorder' tree10000).

    Redirect "out/inorder/sized1" Time Eval vm_compute in (inorder' tree1).
    Redirect "out/inorder/sized10" Time Eval vm_compute in (inorder' tree10).
    Redirect "out/inorder/sized100" Time Eval vm_compute in (inorder' tree100).
    Redirect "out/inorder/sized1000" Time Eval vm_compute in (inorder' tree1000).
    Redirect "out/inorder/sized10000" Time Eval vm_compute in (inorder' tree10000).

    Redirect "out/postorder/sized1" Time Eval vm_compute in (postorder' tree1).
    Redirect "out/postorder/sized10" Time Eval vm_compute in (postorder' tree10).
    Redirect "out/postorder/sized100" Time Eval vm_compute in (postorder' tree100).
    Redirect "out/postorder/sized1000" Time Eval vm_compute in (postorder' tree1000).
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
    Lift Base.tree __bst in Base.tree1 as __tree1.
    Lift Base.tree __bst in Base.tree10 as __tree10.
    Lift Base.tree __bst in Base.tree20 as __tree20.
    Lift Base.tree __bst in Base.tree40 as __tree40.
    Lift Base.tree __bst in Base.tree60 as __tree60.
    Lift Base.tree __bst in Base.tree80 as __tree80.
    Lift Base.tree __bst in Base.tree100 as __tree100.
    Lift Base.tree __bst in Base.tree200 as __tree200.
    Lift Base.tree __bst in Base.tree400 as __tree400.
    Lift Base.tree __bst in Base.tree600 as __tree600.
    Lift Base.tree __bst in Base.tree800 as __tree800.
    Lift Base.tree __bst in Base.tree1000 as __tree1000.
    Lift Base.tree __bst in Base.tree2000 as __tree2000.
    Lift Base.tree __bst in Base.tree400 as __tree4000.
    Lift Base.tree __bst in Base.tree600 as __tree6000.
    Lift Base.tree __bst in Base.tree800 as __tree8000.
    Lift Base.tree __bst in Base.tree10000 as __tree10000.

    Lift __bst _bst in __tree1 as _tree1. 
    Lift __bst _bst in __tree10 as _tree10. 
    Lift __bst _bst in __tree20 as _tree20. 
    Lift __bst _bst in __tree40 as _tree40. 
    Lift __bst _bst in __tree60 as _tree60. 
    Lift __bst _bst in __tree80 as _tree80. 
    Lift __bst _bst in __tree100 as _tree100. 
    Lift __bst _bst in __tree200 as _tree200. 
    Lift __bst _bst in __tree400 as _tree400. 
    Lift __bst _bst in __tree600 as _tree600. 
    Lift __bst _bst in __tree800 as _tree800. 
    Lift __bst _bst in __tree1000 as _tree1000. 
    Lift __bst _bst in __tree2000 as _tree2000. 
    Lift __bst _bst in __tree4000 as _tree4000. 
    Lift __bst _bst in __tree6000 as _tree6000. 
    Lift __bst _bst in __tree8000 as _tree8000. 
    Lift __bst _bst in __tree10000 as _tree10000. 

    Lift _bst bst in _tree1 as tree1'''.
    Lift _bst bst in _tree10 as tree10'''.
    Lift _bst bst in _tree20 as tree20'''.
    Lift _bst bst in _tree40 as tree40'''.
    Lift _bst bst in _tree60 as tree60'''.
    Lift _bst bst in _tree80 as tree80'''.
    Lift _bst bst in _tree100 as tree100'''.
    Lift _bst bst in _tree200 as tree200'''.
    Lift _bst bst in _tree400 as tree400'''.
    Lift _bst bst in _tree600 as tree600'''.
    Lift _bst bst in _tree800 as tree800'''.
    Lift _bst bst in _tree1000 as tree1000'''.
    Lift _bst bst in _tree2000 as tree2000'''.
    Lift _bst bst in _tree4000 as tree4000'''.
    Lift _bst bst in _tree6000 as tree6000'''.
    Lift _bst bst in _tree8000 as tree8000'''.
    Lift _bst bst in _tree10000 as tree10000'''.

    (* --- Unpacked lifted inputs --- *)
    Unpack tree1''' as tree1''.
    Unpack tree1'' as tree1'.
    Unpack tree1' as tree1.
    Unpack tree10''' as tree10''.
    Unpack tree10'' as tree10'.
    Unpack tree10' as tree10.
    Unpack tree100''' as tree100''.
    Unpack tree100'' as tree100'.
    Unpack tree100' as tree100.
    Unpack tree1000''' as tree1000''.
    Unpack tree1000'' as tree1000'.
    Unpack tree1000' as tree1000.
    Unpack tree10000''' as tree10000''.
    Unpack tree10000'' as tree10000'.
    Unpack tree10000' as tree10000.

    (* --- Print the inputs for control purposes for EFF code --- *)
    Redirect "out/inputs/tree1'''-bst" Print tree1'''.
    Redirect "out/inputs/tree10'''-bst" Print tree10'''.
    Redirect "out/inputs/tree20'''-bst" Print tree20'''.
    Redirect "out/inputs/tree40'''-bst" Print tree40'''.
    Redirect "out/inputs/tree60'''-bst" Print tree60'''.
    Redirect "out/inputs/tree80'''-bst" Print tree80'''.
    Redirect "out/inputs/tree100'''-bst" Print tree100'''.
    Redirect "out/inputs/tree200'''-bst" Print tree200'''.
    Redirect "out/inputs/tree400'''-bst" Print tree400'''.
    Redirect "out/inputs/tree600'''-bst" Print tree600'''.
    Redirect "out/inputs/tree800'''-bst" Print tree800'''.
    Redirect "out/inputs/tree1000'''-bst" Print tree1000'''.
    Redirect "out/inputs/tree2000'''-bst" Print tree2000'''.
    Redirect "out/inputs/tree4000'''-bst" Print tree4000'''.
    Redirect "out/inputs/tree6000'''-bst" Print tree6000'''.
    Redirect "out/inputs/tree8000'''-bst" Print tree8000'''.
    Redirect "out/inputs/tree10000'''-bst" Print tree10000'''.

    Redirect "out/inputs/tree1''-bst" Print tree1''.
    Redirect "out/inputs/tree10''-bst" Print tree10''.
    Redirect "out/inputs/tree20''-bst" Print tree20''.
    Redirect "out/inputs/tree40''-bst" Print tree40''.
    Redirect "out/inputs/tree60''-bst" Print tree60''.
    Redirect "out/inputs/tree80''-bst" Print tree80''.
    Redirect "out/inputs/tree100''-bst" Print tree100''.
    Redirect "out/inputs/tree200''-bst" Print tree200''.
    Redirect "out/inputs/tree400''-bst" Print tree400''.
    Redirect "out/inputs/tree600''-bst" Print tree600''.
    Redirect "out/inputs/tree800''-bst" Print tree800''.
    Redirect "out/inputs/tree1000''-bst" Print tree1000''.
    Redirect "out/inputs/tree2000''-bst" Print tree2000''.
    Redirect "out/inputs/tree4000''-bst" Print tree4000''.
    Redirect "out/inputs/tree6000''-bst" Print tree6000''.
    Redirect "out/inputs/tree8000''-bst" Print tree8000''.
    Redirect "out/inputs/tree10000''-bst" Print tree10000''.

    Redirect "out/inputs/tree1'-bst" Print tree1'.
    Redirect "out/inputs/tree10'-bst" Print tree10'.
    Redirect "out/inputs/tree20'-bst" Print tree20'.
    Redirect "out/inputs/tree40'-bst" Print tree40'.
    Redirect "out/inputs/tree60'-bst" Print tree60'.
    Redirect "out/inputs/tree80'-bst" Print tree80'.
    Redirect "out/inputs/tree100'-bst" Print tree100'.
    Redirect "out/inputs/tree200'-bst" Print tree200'.
    Redirect "out/inputs/tree400'-bst" Print tree400'.
    Redirect "out/inputs/tree600'-bst" Print tree600'.
    Redirect "out/inputs/tree800'-bst" Print tree800'.
    Redirect "out/inputs/tree1000'-bst" Print tree1000'.
    Redirect "out/inputs/tree2000'-bst" Print tree2000'.
    Redirect "out/inputs/tree4000'-bst" Print tree4000'.
    Redirect "out/inputs/tree6000'-bst" Print tree6000'.
    Redirect "out/inputs/tree8000'-bst" Print tree8000'.
    Redirect "out/inputs/tree10000'-bst" Print tree10000'.

    Redirect "out/inputs/tree1-bst" Print tree1.
    Redirect "out/inputs/tree10-bst" Print tree10.
    Redirect "out/inputs/tree20-bst" Print tree20.
    Redirect "out/inputs/tree40-bst" Print tree40.
    Redirect "out/inputs/tree60-bst" Print tree60.
    Redirect "out/inputs/tree80-bst" Print tree80.
    Redirect "out/inputs/tree100-bst" Print tree100.
    Redirect "out/inputs/tree200-bst" Print tree200.
    Redirect "out/inputs/tree400-bst" Print tree400.
    Redirect "out/inputs/tree600-bst" Print tree600.
    Redirect "out/inputs/tree800-bst" Print tree800.
    Redirect "out/inputs/tree1000-bst" Print tree1000.
    Redirect "out/inputs/tree2000-bst" Print tree2000.
    Redirect "out/inputs/tree4000-bst" Print tree4000.
    Redirect "out/inputs/tree6000-bst" Print tree6000.
    Redirect "out/inputs/tree8000-bst" Print tree8000.
    Redirect "out/inputs/tree10000-bst" Print tree10000.

    (* --- Base search data --- *)
    Redirect "out/search/base1" Time Eval vm_compute in (search tree1 Elem.x).
    Redirect "out/search/base10" Time Eval vm_compute in (search tree10 Elem.x).
    Redirect "out/search/base100" Time Eval vm_compute in (search tree100 Elem.x).
    Redirect "out/search/base1000" Time Eval vm_compute in (search tree1000 Elem.x).
    Redirect "out/search/base10000" Time Eval vm_compute in (search tree10000 Elem.x).
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
    Lift Ordered.bst _avl in Ordered.tree1''' as _tree1.
    Lift Ordered.bst _avl in Ordered.tree10''' as _tree10.
    Lift Ordered.bst _avl in Ordered.tree20''' as _tree20.
    Lift Ordered.bst _avl in Ordered.tree40''' as _tree40.
    Lift Ordered.bst _avl in Ordered.tree60''' as _tree60.
    Lift Ordered.bst _avl in Ordered.tree80''' as _tree80.
    Lift Ordered.bst _avl in Ordered.tree100''' as _tree100.
    Lift Ordered.bst _avl in Ordered.tree200''' as _tree200.
    Lift Ordered.bst _avl in Ordered.tree400''' as _tree400.
    Lift Ordered.bst _avl in Ordered.tree600''' as _tree600.
    Lift Ordered.bst _avl in Ordered.tree800''' as _tree800.
    Lift Ordered.bst _avl in Ordered.tree1000''' as _tree1000.
    Lift Ordered.bst _avl in Ordered.tree2000''' as _tree2000.
    Lift Ordered.bst _avl in Ordered.tree4000''' as _tree4000.
    Lift Ordered.bst _avl in Ordered.tree6000''' as _tree6000.
    Lift Ordered.bst _avl in Ordered.tree8000''' as _tree8000.
    Lift Ordered.bst _avl in Ordered.tree10000''' as _tree10000.

    Lift _avl avl in _tree1 as tree1''''.
    Lift _avl avl in _tree10 as tree10''''.
    Lift _avl avl in _tree20 as tree20''''.
    Lift _avl avl in _tree40 as tree40''''.
    Lift _avl avl in _tree60 as tree60''''.
    Lift _avl avl in _tree80 as tree80''''.
    Lift _avl avl in _tree100 as tree100''''.
    Lift _avl avl in _tree200 as tree200''''.
    Lift _avl avl in _tree400 as tree400''''.
    Lift _avl avl in _tree600 as tree600''''.
    Lift _avl avl in _tree800 as tree800''''.
    Lift _avl avl in _tree1000 as tree1000''''.
    Lift _avl avl in _tree2000 as tree2000''''.
    Lift _avl avl in _tree4000 as tree4000''''.
    Lift _avl avl in _tree6000 as tree6000''''.
    Lift _avl avl in _tree8000 as tree8000''''.
    Lift _avl avl in _tree10000 as tree10000''''.

    (* --- Unpacked inputs --- *)
    Unpack tree1'''' as tree1'''.
    Unpack tree1''' as tree1''.
    Unpack tree1'' as tree1'.
    Unpack tree1' as tree1.
    Unpack tree10'''' as tree10'''.
    Unpack tree10''' as tree10''.
    Unpack tree10'' as tree10'.
    Unpack tree10' as tree10.
    Unpack tree100'''' as tree100'''.
    Unpack tree100''' as tree100''.
    Unpack tree100'' as tree100'.
    Unpack tree100' as tree100.
    Unpack tree1000'''' as tree1000'''.
    Unpack tree1000''' as tree1000''.
    Unpack tree1000'' as tree1000'.
    Unpack tree1000' as tree1000.
    Unpack tree10000'''' as tree10000'''.
    Unpack tree10000''' as tree10000''.
    Unpack tree10000'' as tree10000'.
    Unpack tree10000' as tree10000.

    (* --- Print the inputs for control purposes for EFF code --- *)
    Redirect "out/inputs/tree1''''-avl" Print tree1''''.
    Redirect "out/inputs/tree10''''-avl" Print tree10''''.
    Redirect "out/inputs/tree20''''-avl" Print tree20''''.
    Redirect "out/inputs/tree40''''-avl" Print tree40''''.
    Redirect "out/inputs/tree60''''-avl" Print tree60''''.
    Redirect "out/inputs/tree80''''-avl" Print tree80''''.
    Redirect "out/inputs/tree100''''-avl" Print tree100''''.
    Redirect "out/inputs/tree200''''-avl" Print tree200''''.
    Redirect "out/inputs/tree400''''-avl" Print tree400''''.
    Redirect "out/inputs/tree600''''-avl" Print tree600''''.
    Redirect "out/inputs/tree800''''-avl" Print tree800''''.
    Redirect "out/inputs/tree1000''''-avl" Print tree1000''''.
    Redirect "out/inputs/tree2000''''-avl" Print tree2000''''.
    Redirect "out/inputs/tree4000''''-avl" Print tree4000''''.
    Redirect "out/inputs/tree6000''''-avl" Print tree6000''''.
    Redirect "out/inputs/tree8000''''-avl" Print tree8000''''.
    Redirect "out/inputs/tree10000''''-avl" Print tree10000''''.

    Redirect "out/inputs/tree1'''-avl" Print tree1'''.
    Redirect "out/inputs/tree10'''-avl" Print tree10'''.
    Redirect "out/inputs/tree20'''-avl" Print tree20'''.
    Redirect "out/inputs/tree40'''-avl" Print tree40'''.
    Redirect "out/inputs/tree60'''-avl" Print tree60'''.
    Redirect "out/inputs/tree80'''-avl" Print tree80'''.
    Redirect "out/inputs/tree100'''-avl" Print tree100'''.
    Redirect "out/inputs/tree200'''-avl" Print tree200'''.
    Redirect "out/inputs/tree400'''-avl" Print tree400'''.
    Redirect "out/inputs/tree600'''-avl" Print tree600'''.
    Redirect "out/inputs/tree800'''-avl" Print tree800'''.
    Redirect "out/inputs/tree1000'''-avl" Print tree1000'''.
    Redirect "out/inputs/tree2000'''-avl" Print tree2000'''.
    Redirect "out/inputs/tree4000'''-avl" Print tree4000'''.
    Redirect "out/inputs/tree6000'''-avl" Print tree6000'''.
    Redirect "out/inputs/tree8000'''-avl" Print tree8000'''.
    Redirect "out/inputs/tree10000'''-avl" Print tree10000'''.

    Redirect "out/inputs/tree1''-avl" Print tree1''.
    Redirect "out/inputs/tree10''-avl" Print tree10''.
    Redirect "out/inputs/tree20''-avl" Print tree20''.
    Redirect "out/inputs/tree40''-avl" Print tree40''.
    Redirect "out/inputs/tree60''-avl" Print tree60''.
    Redirect "out/inputs/tree80''-avl" Print tree80''.
    Redirect "out/inputs/tree100''-avl" Print tree100''.
    Redirect "out/inputs/tree200''-avl" Print tree200''.
    Redirect "out/inputs/tree400''-avl" Print tree400''.
    Redirect "out/inputs/tree600''-avl" Print tree600''.
    Redirect "out/inputs/tree800''-avl" Print tree800''.
    Redirect "out/inputs/tree1000''-avl" Print tree1000''.
    Redirect "out/inputs/tree2000''-avl" Print tree2000''.
    Redirect "out/inputs/tree4000''-avl" Print tree4000''.
    Redirect "out/inputs/tree6000''-avl" Print tree6000''.
    Redirect "out/inputs/tree8000''-avl" Print tree8000''.
    Redirect "out/inputs/tree10000''-avl" Print tree10000''.

    Redirect "out/inputs/tree1'-avl" Print tree1'.
    Redirect "out/inputs/tree10'-avl" Print tree10'.
    Redirect "out/inputs/tree20'-avl" Print tree20'.
    Redirect "out/inputs/tree40'-avl" Print tree40'.
    Redirect "out/inputs/tree60'-avl" Print tree60'.
    Redirect "out/inputs/tree80'-avl" Print tree80'.
    Redirect "out/inputs/tree100'-avl" Print tree100'.
    Redirect "out/inputs/tree200'-avl" Print tree200'.
    Redirect "out/inputs/tree400'-avl" Print tree400'.
    Redirect "out/inputs/tree600'-avl" Print tree600'.
    Redirect "out/inputs/tree800'-avl" Print tree800'.
    Redirect "out/inputs/tree1000'-avl" Print tree1000'.
    Redirect "out/inputs/tree2000'-avl" Print tree2000'.
    Redirect "out/inputs/tree4000'-avl" Print tree4000'.
    Redirect "out/inputs/tree6000'-avl" Print tree6000'.
    Redirect "out/inputs/tree8000'-avl" Print tree8000'.
    Redirect "out/inputs/tree10000'-avl" Print tree10000'.

    Redirect "out/inputs/tree1-avl" Print tree1.
    Redirect "out/inputs/tree10-avl" Print tree10.
    Redirect "out/inputs/tree20-avl" Print tree20.
    Redirect "out/inputs/tree40-avl" Print tree40.
    Redirect "out/inputs/tree60-avl" Print tree60.
    Redirect "out/inputs/tree80-avl" Print tree80.
    Redirect "out/inputs/tree100-avl" Print tree100.
    Redirect "out/inputs/tree200-avl" Print tree200.
    Redirect "out/inputs/tree400-avl" Print tree400.
    Redirect "out/inputs/tree600-avl" Print tree600.
    Redirect "out/inputs/tree800-avl" Print tree800.
    Redirect "out/inputs/tree1000-avl" Print tree1000.
    Redirect "out/inputs/tree2000-avl" Print tree2000.
    Redirect "out/inputs/tree4000-avl" Print tree4000.
    Redirect "out/inputs/tree6000-avl" Print tree6000.
    Redirect "out/inputs/tree8000-avl" Print tree8000.
    Redirect "out/inputs/tree10000-avl" Print tree10000.

    (* --- AVL data --- *)
    Redirect "out/preorder/avl1" Time Eval vm_compute in (preorder' _ _ _ _ tree1).
    Redirect "out/preorder/avl10" Time Eval vm_compute in (preorder' _ _ _ _ tree10).
    Redirect "out/preorder/avl100" Time Eval vm_compute in (preorder' _ _ _ _ tree100).
    Redirect "out/preorder/avl1000" Time Eval vm_compute in (preorder' _ _ _ _ tree1000).
    Redirect "out/preorder/avl10000" Time Eval vm_compute in (preorder' _ _ _ _ tree10000).

    Redirect "out/inorder/avl1" Time Eval vm_compute in (inorder' _ _ _ _ tree1).
    Redirect "out/inorder/avl10" Time Eval vm_compute in (inorder' _ _ _ _ tree10).
    Redirect "out/inorder/avl100" Time Eval vm_compute in (inorder' _ _ _ _ tree100).
    Redirect "out/inorder/avl1000" Time Eval vm_compute in (inorder' _ _ _ _ tree1000).
    Redirect "out/inorder/avl10000" Time Eval vm_compute in (inorder' _ _ _ _ tree10000).

    Redirect "out/postorder/avl1" Time Eval vm_compute in (postorder' _ _ _ _ tree1).
    Redirect "out/postorder/avl10" Time Eval vm_compute in (postorder' _ _ _ _ tree10).
    Redirect "out/postorder/avl100" Time Eval vm_compute in (postorder' _ _ _ _ tree100).
    Redirect "out/postorder/avl1000" Time Eval vm_compute in (postorder' _ _ _ _ tree1000).
    Redirect "out/postorder/avl10000" Time Eval vm_compute in (postorder' _ _ _ _ tree10000).

    Redirect "out/search/avl1" Time Eval vm_compute in (search' _ _ _ _ tree1 Elem.x).
    Redirect "out/search/avl10" Time Eval vm_compute in (search' _ _ _ _ tree10 Elem.x).
    Redirect "out/search/avl100" Time Eval vm_compute in (search' _ _ _ _ tree100 Elem.x).
    Redirect "out/search/avl1000" Time Eval vm_compute in (search' _ _ _ _ tree1000 Elem.x).
    Redirect "out/search/avl10000" Time Eval vm_compute in (search' _ _ _ _ tree10000 Elem.x).

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
