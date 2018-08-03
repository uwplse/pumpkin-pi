From UnivalentParametricity Require Import HoTT UR URTactics FP Record MoreInductive.
Require Import PeanoNat list perm lemmas.

Set Universe Polymorphism.

Open Scope bool_scope.
Infix "==>" := implb (at level 40, left associativity) : bool_scope.
Definition is_true (b : bool) := (b = true).
Hint Unfold is_true.
Coercion is_true : bool >-> Sortclass.

Notation "x <= y" := (Nat.leb x y) (at level 70, y at next level, no associativity) : nat_scope.

Notation "x <> y" := (x = y -> False) : type_scope.
Coercion logic_eq_is_eq : Logic.eq >-> eq.
Hint Extern 4 => repeat (match goal with H : Logic.eq _ _ |- _ => apply logic_eq_is_eq in H end).

Notation "'typeof' x" := (let A := _ in let _ : A := x in A) (at level 100).

Add Printing Let sigT. (* for consistency *)

Module Type Comparable.

  Parameter t : Set.
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

  Lemma list_rect_eta {A} (xs : list A) :
    list_rect A (fun _ => list A) nil (fun x _ xs => x :: xs) xs = xs.
  Proof. induction xs; cbn; try rewrite IHxs; reflexivity. Defined.

  Hint Extern 0 (?t ≈ ?t) => reflexivity : typeclass_instances.

  Definition Decidable_eq_elem : forall (x y : Elem.t), (x = y) + (x <> y).
  Proof.
    intros. pose proof (Elem.eqb_dec x y) as H. destruct (Elem.eqb x y); auto.
  Defined.

  Instance elem_Hset : HSet Elem.t := Hedberg Elem.t Decidable_eq_elem.
  Instance UR_elem : UR Elem.t Elem.t := UR_gen Elem.t.
  Instance FP_elem : Elem.t ⋈ Elem.t := URType_Refl_decidable Elem.t Decidable_eq_elem.
  Instance Transportable_elem (P : Elem.t -> Type) : Transportable P :=
    Transportable_decidable P Decidable_eq_elem.

  Definition Decidable_eq_list_elem : forall (xs ys : list Elem.t), (xs = ys) + (xs <> ys).
  Proof.
    induction xs as [|x xs IH]; cbn; intros [|y ys].
    - left. reflexivity.
    - right. inversion 1.
    - right. inversion 1.
    - specialize (IH ys). destruct IH as [E|E].
      + rewrite <- E. clear E. destruct (Decidable_eq_elem x y) as [E|E].
        * rewrite <- E. clear E. left. reflexivity.
        * right. inversion 1. destruct (E H1).
      + right. inversion 1. destruct (E H2).
  Defined.

  Instance list_elem_Hset : HSet (list Elem.t) := Hedberg (list Elem.t) Decidable_eq_list_elem.

  Lemma UR_list_refl {A} (xs : list A) : UR_list (eq A) xs xs.
  Proof. induction xs; econstructor; [reflexivity|assumption]. Defined.

  Lemma UR_list_elem_eq {xs xs' : list Elem.t} (U : xs ≈ xs') : xs = xs'.
  Proof.
    apply (@univalent_transport _ _ (alt_ur_coh _ _ _ xs xs')) in U. revert xs U. cbn.
    rewrite list_rect_eta. auto.
  Defined.

  Instance UR_permutes_elem
           (xs xs' : list Elem.t) (U_xs : xs ≈ xs')
           (ys ys' : list Elem.t) (U_ys : ys ≈ ys') :
    UR (permutes xs ys) (permutes xs' ys').
  Proof. rewrite <- (UR_list_elem_eq U_xs), <- (UR_list_elem_eq U_ys). apply UR_gen. Defined.

  Instance UR_permutes_elem_id
           (xs : list Elem.t) (U_xs : xs ≈ xs)
           (ys : list Elem.t) (U_ys : ys ≈ ys) :
    UR_permutes_elem xs xs U_xs ys ys U_ys = UR_gen (permutes xs ys).
  Proof.
    unfold UR_permutes_elem.
    repeat rewrite (is_hset _ _ (UR_list_elem_eq _) eq_refl). reflexivity.
  Defined.

  Instance Equiv_permutes_elem
           (xs xs' : list Elem.t) (U_xs : xs ≈ xs')
           (ys ys' : list Elem.t) (U_ys : ys ≈ ys') :
    permutes xs ys ≃ permutes xs' ys'.
  Proof.
    rewrite <- (UR_list_elem_eq U_xs), <- (UR_list_elem_eq U_ys).
    eapply Equiv_id.
  Defined.

  Instance Equiv_permutes_elem_id
           (xs : list Elem.t) (U_xs : xs ≈ xs)
           (ys : list Elem.t) (U_ys : ys ≈ ys) :
    Equiv_permutes_elem xs xs U_xs ys ys U_ys = Equiv_id (permutes xs ys).
  Proof.
    unfold Equiv_permutes_elem.
    repeat rewrite (is_hset _ _ (UR_list_elem_eq _) eq_refl). reflexivity.
  Defined.

  Instance FP_permutes_elem
           (xs xs' : list Elem.t) (U_xs : xs ≈ xs')
           (ys ys' : list Elem.t) (U_ys : ys ≈ ys') :
    permutes xs ys ⋈ permutes xs' ys'.
  Proof.
    unshelve esplit; try apply Canonical_eq_gen.
    esplit. intros perm perm'. unfold univalent_transport.
    pose proof (UR_list_elem_eq U_xs) as E_xs.
    pose proof (UR_list_elem_eq U_ys) as E_ys.
    revert U_xs U_ys. rewrite <- E_xs, <- E_ys. intros U_xs U_ys.
    rewrite Equiv_permutes_elem_id, UR_permutes_elem_id. cbn.
    eapply Equiv_id.
  Defined.

  Hint Extern 0 ((fun _ => permutes _ _) ≈ (fun _ => permutes _ _)) => unshelve esplit; intros : typeclass_instances.

  Module Base.

    Inductive tree : Type :=
    | Branch (val : Elem.t) (left right : tree)
    | Leaf (val : Elem.t).

    Definition Decidable_eq_tree : forall (x y : tree), (x = y) + (x <> y).
    Proof.
      Local Ltac discr := let E := fresh in right; intro E; inversion E; auto; discriminate E.
      Local Ltac recur H x := specialize (H x); destruct H as [H|H]; [rewrite <- H|]; try discr.
      intro x. induction x as [x_v x_l IH_l x_r IH_r|x_v]; intros [y_v y_l y_r|y_v];
      try discr; pose (Decidable_eq_elem x_v) as H_v; recur H_v y_v;
      try recur IH_l y_l; try recur IH_r y_r; left; reflexivity.
    Defined.

    Instance tree_Hset : HSet tree := Hedberg tree Decidable_eq_tree.
    Instance UR_tree : UR tree tree := UR_gen tree.
    Instance FP_tree : tree ⋈ tree := URType_Refl_decidable tree Decidable_eq_tree.
    Instance Transportable_tree (P: tree -> Type) : Transportable P :=
      Transportable_decidable P Decidable_eq_tree.

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

    (* 13 LoC in normal form *)
    Definition preorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => [x] ++ ys ++ zs)
        (fun x => [x])
        t.

   (* --- Let Coq warm up on each tree, so that base numbers aren't slower than they should be --- *)
    Redirect "../out/treeUP20" Time Eval vm_compute in tree20.
    Redirect "../out/treeUP40" Time Eval vm_compute in tree40.
    Redirect "../out/treeUP60" Time Eval vm_compute in tree60.
    Redirect "../out/treeUP80" Time Eval vm_compute in tree80.
    Redirect "../out/treeUP100" Time Eval vm_compute in tree100.
    Redirect "../out/treeUP2000" Time Eval vm_compute in tree2000.
    Redirect "../out/treeUP4000" Time Eval vm_compute in tree4000.
    Redirect "../out/treeUP6000" Time Eval vm_compute in tree6000.
    Redirect "../out/treeUP8000" Time Eval vm_compute in tree8000.
    Redirect "../out/treeUP10000" Time Eval vm_compute in tree10000.

    Redirect "../out/preorder/baseUP20" Time Eval vm_compute in (preorder tree20).
    Redirect "../out/preorder/baseUP40" Time Eval vm_compute in (preorder tree40).
    Redirect "../out/preorder/baseUP60" Time Eval vm_compute in (preorder tree60).
    Redirect "../out/preorder/baseUP80" Time Eval vm_compute in (preorder tree80).
    Redirect "../out/preorder/baseUP100" Time Eval vm_compute in (preorder tree100).
    Redirect "../out/preorder/baseUP2000" Time Eval vm_compute in (preorder tree2000).
    Redirect "../out/preorder/baseUP4000" Time Eval vm_compute in (preorder tree4000).
    Redirect "../out/preorder/baseUP6000" Time Eval vm_compute in (preorder tree6000).
    Redirect "../out/preorder/baseUP8000" Time Eval vm_compute in (preorder tree8000).
    Redirect "../out/preorder/baseUP10000" Time Eval vm_compute in (preorder tree10000).

    (* 12 LoC in normal form *)
    Definition inorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ [x] ++ zs)
        (fun x => [x])
        t.
    Redirect "../out/inorder/baseUP20" Time Eval vm_compute in (inorder tree20).
    Redirect "../out/inorder/baseUP40" Time Eval vm_compute in (inorder tree40).
    Redirect "../out/inorder/baseUP00" Time Eval vm_compute in (inorder tree60).
    Redirect "../out/inorder/baseUP80" Time Eval vm_compute in (inorder tree80).
    Redirect "../out/inorder/baseUP100" Time Eval vm_compute in (inorder tree100).
    Redirect "../out/inorder/baseUP2000" Time Eval vm_compute in (inorder tree2000).
    Redirect "../out/inorder/baseUP4000" Time Eval vm_compute in (inorder tree4000).
    Redirect "../out/inorder/baseUP6000" Time Eval vm_compute in (inorder tree6000).
    Redirect "../out/inorder/baseUP8000" Time Eval vm_compute in (inorder tree8000).
    Redirect "../out/inorder/baseUP10000" Time Eval vm_compute in (inorder tree10000).

    (* 12 LoC in normal form *)
    Definition postorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ zs ++ [x])
        (fun x => [x])
        t.
    Redirect "../out/postorder/baseUP20" Time Eval vm_compute in (postorder tree20).
    Redirect "../out/postorder/baseUP40" Time Eval vm_compute in (postorder tree40).
    Redirect "../out/postorder/baseUP60" Time Eval vm_compute in (postorder tree60).
    Redirect "../out/postorder/baseUP80" Time Eval vm_compute in (postorder tree80).
    Redirect "../out/postorder/baseUP100" Time Eval vm_compute in (postorder tree100).
    Redirect "../out/postorder/baseUP2000" Time Eval vm_compute in (postorder tree2000).
    Redirect "../out/postorder/baseUP4000" Time Eval vm_compute in (postorder tree4000).
    Redirect "../out/postorder/baseUP6000" Time Eval vm_compute in (postorder tree6000).
    Redirect "../out/postorder/baseUP8000" Time Eval vm_compute in (postorder tree8000).
    Redirect "../out/postorder/baseUP10000" Time Eval vm_compute in (postorder tree10000).

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

    Instance Equiv_tree (n n' : nat) (E : n = n') : tree n ≃ tree n'.
    Proof. apply can_eq in E; try tc. rewrite <- E. apply Equiv_id. Defined.

    Lemma Equiv_tree_id n : Equiv_tree n n eq_refl = Equiv_id (tree n).
    Proof. unfold Equiv_tree. rewrite can_eq_refl. reflexivity. Defined.

    Instance UR_tree (n n' : nat) (E : n = n') : UR (tree n) (tree n').
    Proof. rewrite <- E. apply UR_gen. Defined.

    Instance Transportable_tree : Transportable tree.
    Proof. esplit. intros h. rewrite Equiv_tree_id. reflexivity. Defined.

    Definition FP_tree : tree ≈ tree.
    Proof.
      cbn. split; try tc. cbn. intros n n' E. apply can_eq in E; try tc.
      rewrite <- E. esplit; try apply Canonical_eq_gen.
      esplit. cbn. intros t t'. unfold univalent_transport.
      rewrite Equiv_tree_id. cbn. tc.
    Defined.

    Fixpoint orn_size_index (t : Base.tree) : nat :=
      match t with
      | Base.Branch _ l r => S (orn_size_index l + orn_size_index r)
      | Base.Leaf _ => 1
      end.

    Fixpoint orn_size (t : Base.tree) : {n:nat & tree n} :=
      match t with
      | Base.Branch v l r =>
        let L := orn_size l in
        let R := orn_size r in
        (_; (Branch L.1 R.1 v L.2 R.2))
      | Base.Leaf v => (_; Leaf v)
      end.

    Fixpoint orn_size_inv' (n : nat) (t : tree n) : Base.tree :=
      match t with
      | Branch n_l n_r v l r =>
        Base.Branch v (orn_size_inv' n_l l) (orn_size_inv' n_r r)
      | Leaf v =>
        Base.Leaf v
      end.

    Definition orn_size_inv (T : {n:nat & tree n}) : Base.tree :=
      orn_size_inv' T.1 T.2.

    Instance IsEquiv_orn_size : IsEquiv orn_size.
    Proof.
      eapply isequiv_adjointify with (g := orn_size_inv); unfold orn_size_inv.
      - intros t. induction t as [v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
      - intros [h t]. cbn. induction t as [n_l n_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
    Defined.

    Instance Equiv_orn_size : Base.tree ≃ {n:nat & tree n} :=
      BuildEquiv _ _ _ IsEquiv_orn_size.

    Instance UR_orn_size : Base.tree ⋈ {n:nat & tree n}.
    Proof.
      cbn. unshelve esplit.
      - esplit. intros t t'. exact (orn_size t = t').
      - esplit. intros t t'. cbn.
        apply (@isequiv_ap _ _ Equiv_orn_size).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Definition orn_size_coh t : orn_size_inv (orn_size t) = t := e_sect orn_size t.

    Definition tree2000 := ↑ Base.tree2000.
    Definition tree4000 := ↑ Base.tree4000.
    Definition tree6000 := ↑ Base.tree6000.
    Definition tree8000 := ↑ Base.tree8000.
    Definition tree10000 := ↑ Base.tree10000.

    (* 38 LoC in normal form *)
    Definition preorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.preorder.
    Definition preorder n t := preorder' (existT _ n t).
    Redirect "../out/preorder/sizedUP2000" Time Eval vm_compute in (preorder' tree2000).
    Redirect "../out/preorder/sizedUP4000" Time Eval vm_compute in (preorder' tree4000).
    Redirect "../out/preorder/sizedUP6000" Time Eval vm_compute in (preorder' tree6000).
    Redirect "../out/preorder/sizedUP8000" Time Eval vm_compute in (preorder' tree8000).
    Redirect "../out/preorder/sizedUP10000" Time Eval vm_compute in (preorder' tree10000).

    (* 37 LoC in normal form *)
    Definition inorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.inorder.
    Definition inorder n t := inorder' (existT _ n t).
    Redirect "../out/inorder/sizedUP2000" Time Eval vm_compute in (inorder' tree2000).
    Redirect "../out/inorder/sizedUP4000" Time Eval vm_compute in (inorder' tree4000).
    Redirect "../out/inorder/sizedUP6000" Time Eval vm_compute in (inorder' tree6000).
    Redirect "../out/inorder/sizedUP8000" Time Eval vm_compute in (inorder' tree8000).
    Redirect "../out/inorder/sizedUP10000" Time Eval vm_compute in (inorder' tree10000).

    (* 43 LoC in normal form *)
    Definition postorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.postorder.
    Definition postorder n t := postorder' (existT _ n t).
    Redirect "../out/postorder/sizedUP2000" Time Eval vm_compute in (postorder' tree2000).
    Redirect "../out/postorder/sizedUP4000" Time Eval vm_compute in (postorder' tree4000).
    Redirect "../out/postorder/sizedUP6000" Time Eval vm_compute in (postorder' tree6000).
    Redirect "../out/postorder/sizedUP8000" Time Eval vm_compute in (postorder' tree8000).
    Redirect "../out/postorder/sizedUP10000" Time Eval vm_compute in (postorder' tree10000).

    Definition mirror' : {n:nat & tree n} -> {n:nat & tree n} := ↑ Base.mirror.
    Definition mirror (n : nat) (t : tree n) : tree n.
      pose (T := (mirror' (existT _ n t))). replace n with (T.1). exact (T.2).
      subst T. induction t as [s_l s_r v t_l IH_l t_r IH_r|v]; [|reflexivity].
      cbn in *. rewrite IH_l, IH_r. rewrite add_comm. reflexivity.
    Defined.

    Lemma FP_preorder : Base.preorder ≈ preorder'.
    Proof.
      intros t t' U. cbn in U. rewrite <- U. unfold preorder'. generalize Base.preorder.
      intros f. cbn. rewrite list_rect_eta, orn_size_coh. eapply UR_list_refl.
    Defined.

    Hint Extern 0 (Base.preorder ?t ≈ preorder' ?t') => unshelve refine (FP_preorder t t' _); intros :  typeclass_instances.

    Lemma FP_inorder : Base.inorder ≈ inorder'.
    Proof.
      intros t t' U. cbn in U. rewrite <- U. unfold inorder'. generalize Base.inorder.
      intros f. cbn. rewrite list_rect_eta, orn_size_coh. eapply UR_list_refl.
    Defined.

    Hint Extern 0 (Base.inorder ?t ≈ inorder' ?t') => unshelve refine (FP_inorder t t' _); intros :  typeclass_instances.

    Lemma FP_postorder : Base.postorder ≈ postorder'.
    Proof.
      intros t t' U. cbn in U. rewrite <- U. unfold postorder'. generalize Base.postorder.
      intros f. cbn. rewrite list_rect_eta, orn_size_coh. eapply UR_list_refl.
    Defined.

    Hint Extern 0 (Base.postorder ?t ≈ postorder' ?t') => unshelve refine (FP_postorder t t' _); intros :  typeclass_instances.

    Definition pre_permutes' : forall (t : {n:nat & tree n}), permutes (preorder' t) (inorder' t) :=
      ↑ Base.pre_permutes.

    (* --- Normalized term sizes --- *)
    Redirect "../out/normalized/preorder-sizedUP" Eval compute in preorder'.
    Redirect "../out/normalized/postorder-sizedUP" Eval compute in postorder'.
    Redirect "../out/normalized/inorder-sizedUP" Eval compute in inorder'.
    (*Redirect "../out/normalized/pre_permutes-sizedUP" Eval compute in pre_permutes'.*)

    (* Auto-generated definitions go here in together case study *)
    Module Comparison.
      (* DEF inorder-sized *)
      (* DEF postorder-sized *)
      (* DEF preorder-sized *)
      (* DEF pre_permutes-sized *)

      (* TIME-BIG inorder-sized *)
      (* TIME-BIG postorder-sized *)
      (* TIME-BIG preorder-sized *)

      (* NORMALIZE inorder-sized *)
      (* NORMALIZE postorder-sized *)
      (* NORMALIZE preorder-sized *)
      (* NORMALIZE pre_permutes-sized *)
    End Comparison.

  End Sized.

  Module Ordered.

    Definition inv (ord_l ord_r : bool) (max_l val min_r : Elem.t) : bool :=
      ord_l && ord_r && Elem.ltb max_l val && Elem.ltb val min_r.

    Inductive bst : Elem.t -> Elem.t -> bool -> Type :=
    | Branch (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
             (val : Elem.t)
             (left : bst min_l max_l ord_l) (right : bst min_r max_r ord_r)
      : bst min_l max_r (inv ord_l ord_r max_l val min_r)
    | Leaf (val : Elem.t) : bst val val true.

    Instance Equiv_bst
             (lo lo' : Elem.t) (E_lo : lo = lo') (hi hi' : Elem.t) (E_hi : hi = hi')
             (ord ord' : bool) (E_ord : ord = ord') :
      bst lo hi ord ≃ bst lo' hi' ord'.
    Proof.
      apply can_eq in E_lo; try tc. apply can_eq in E_hi; try tc. apply can_eq in E_ord; try tc.
      rewrite <- E_lo, <- E_hi, <- E_ord. apply Equiv_id.
    Defined.

    Lemma Equiv_bst_id lo hi ord :
      Equiv_bst lo lo eq_refl hi hi eq_refl ord ord eq_refl = Equiv_id (bst lo hi ord).
    Proof. unfold Equiv_bst. repeat rewrite can_eq_refl. reflexivity. Defined.

    Instance UR_bst
             (lo lo' : Elem.t) (E_lo : lo = lo') (hi hi' : Elem.t) (E_hi : hi = hi')
             (ord ord' : bool) (E_ord : ord = ord') :
      UR (bst lo hi ord) (bst lo' hi' ord').
    Proof. rewrite <- E_lo, <- E_hi, <- E_ord. apply UR_gen. Defined.

    Instance Transportable_bst lo hi : Transportable (bst lo hi).
    Proof. econstructor. intros ord. rewrite Equiv_bst_id. reflexivity. Defined.

    Definition FP_bst : bst ≈ bst.
    Proof.
      cbn. intros lo lo' E_lo hi hi' E_hi. split; try tc. cbn. intros ord ord' E_ord.
      apply can_eq in E_lo; try tc. apply can_eq in E_hi; try tc. apply can_eq in E_ord; try tc.
      rewrite <- E_lo, <- E_hi, <- E_ord. esplit; try apply Canonical_eq_gen.
      econstructor. cbn. intros t t'. unfold univalent_transport. rewrite Equiv_bst_id. cbn. tc.
    Defined.

    Fixpoint orn_order (t : Base.tree) : {lo:Elem.t & {hi:Elem.t & {ord:bool & Ordered.bst lo hi ord}}} :=
      match t with
      | Base.Branch v l r =>
        (_; (_; (_; Branch _ _ _ _ _ _ v (orn_order l).2.2.2 (orn_order r).2.2.2)))
      | Base.Leaf v =>
        (_; (_; (_; Leaf v)))
      end.

    Fixpoint orn_order_inv' {lo hi ord} (t : bst lo hi ord) : Base.tree :=
      match t with
      | Branch _ _ _ _ _ _ v l r =>
        Base.Branch v (orn_order_inv' l) (orn_order_inv' r)
      | Leaf v =>
        Base.Leaf v
      end.

    Definition orn_order_inv (T : {lo:Elem.t & {hi:Elem.t & {ord:bool & bst lo hi ord}}}) : Base.tree :=
      orn_order_inv' T.2.2.2.

    Instance IsEquiv_orn_order : IsEquiv orn_order.
    Proof.
      eapply isequiv_adjointify with (g := orn_order_inv); unfold orn_order_inv; cbn.
      - intros t. induction t as [v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
      - intros [lo [hi [ord t]]]. cbn. induction t as [ord_l ord_r lo_l lo_r hi_l hi_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
    Defined.

    Instance Equiv_orn_order : Base.tree ≃ {lo:Elem.t & {hi:Elem.t & {ord:bool & bst lo hi ord}}} :=
      BuildEquiv _ _ _ IsEquiv_orn_order.

    Instance UR_orn_order : Base.tree ⋈ {lo:Elem.t & {hi:Elem.t & {ord:bool & bst lo hi ord}}}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (orn_order t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ Equiv_orn_order).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Notation bst_sig := {lo:Elem.t & {hi:Elem.t & {ord:bool & bst lo hi ord}}} (only parsing).

    Definition tree20 := ↑ Base.tree20.
    Definition tree40 := ↑ Base.tree40.
    Definition tree60 := ↑ Base.tree60.
    Definition tree80 := ↑ Base.tree80.
    Definition tree100 := ↑ Base.tree100.

    Definition preorder' : bst_sig -> list Elem.t := ↑ Base.preorder.
    Definition preorder {lo hi ord} t := preorder' (lo; (hi; (ord; t))).

    Definition inorder' : bst_sig -> list Elem.t := ↑ Base.inorder.
    Definition inorder {lo hi ord} t := inorder' (lo; (hi; (ord; t))).

    Definition postorder' : bst_sig -> list Elem.t := ↑ Base.postorder.
    Definition postorder {lo hi ord} t := postorder' (lo; (hi; (ord; t))).

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
    Redirect "../out/search/baseUP20" Time Eval vm_compute in (search tree20.2.2.2 Elem.x).
    Redirect "../out/search/baseUP40" Time Eval vm_compute in (search tree40.2.2.2 Elem.x).
    Redirect "../out/search/baseUP60" Time Eval vm_compute in (search tree60.2.2.2 Elem.x).
    Redirect "../out/search/baseUP80" Time Eval vm_compute in (search tree80.2.2.2 Elem.x).
    Redirect "../out/search/baseUP100" Time Eval vm_compute in (search tree100.2.2.2 Elem.x).

  End Ordered.

  Module Balanced.

    Definition inv (bal_l bal_r : bool) (h_l h_r : nat) : bool :=
      bal_l && bal_r && (h_l - h_r <= 1) && (h_r - h_l <= 1).

    Inductive avl : Elem.t -> Elem.t -> bool -> nat -> bool -> Type :=
    | Branch (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
             (val : Elem.t)
             (left : avl min_l max_l ord_l h_l bal_l) (right : avl min_r max_r ord_r h_r bal_r)
      : avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) (S (Nat.max h_l h_r)) (inv bal_l bal_r h_l h_r)
    | Leaf (val : Elem.t) : avl val val true O true.

    Instance Equiv_avl
             (lo lo' : Elem.t) (E_lo : lo = lo') (hi hi' : Elem.t) (E_hi : hi = hi')
             (ord ord' : bool) (E_ord : ord = ord') (h h' : nat) (E_h : h = h')
             (bal bal' : bool) (E_bal : bal = bal') :
      avl lo hi ord h bal ≃ avl lo' hi' ord' h' bal'.
    Proof.
      apply can_eq in E_lo; try tc. apply can_eq in E_hi; try tc. apply can_eq in E_ord; try tc.
      apply can_eq in E_h; try tc. apply can_eq in E_bal; try tc.
      rewrite <- E_lo, <- E_hi, <- E_ord, <- E_h, <- E_bal. apply Equiv_id.
    Defined.

    Lemma Equiv_avl_id lo hi ord h bal :
      Equiv_avl lo lo eq_refl hi hi eq_refl ord ord eq_refl h h eq_refl bal bal eq_refl =
      Equiv_id (avl lo hi ord h bal).
    Proof. unfold Equiv_avl. repeat rewrite can_eq_refl. reflexivity. Defined.

    Instance UR_avl
             (lo lo' : Elem.t) (E_lo : lo = lo') (hi hi' : Elem.t) (E_hi : hi = hi')
             (ord ord' : bool) (E_ord : ord = ord') (h h' : nat) (E_h : h = h')
             (bal bal' : bool) (E_bal : bal = bal') :
      UR (avl lo hi ord h bal) (avl lo' hi' ord' h' bal').
    Proof. rewrite <- E_lo, <- E_hi, <- E_ord, <- E_h, <- E_bal. apply UR_gen. Defined.

    Instance Transportable_avl lo hi ord h : Transportable (avl lo hi ord h).
    Proof. econstructor. intros bal. rewrite Equiv_avl_id. reflexivity. Defined.

    Definition FP_avl : avl ≈ avl.
    Proof.
      cbn. intros lo lo' E_lo hi hi' E_hi ord ord' E_ord h h' E_h. split; try tc. cbn.
      intros bal bal' E_bal. apply can_eq in E_lo; try tc. apply can_eq in E_hi; try tc.
      apply can_eq in E_ord; try tc. apply can_eq in E_h; try tc. apply can_eq in E_bal; try tc.
      rewrite <- E_lo, <- E_hi, <- E_ord, <- E_h, <- E_bal. esplit; try apply Canonical_eq_gen.
      econstructor. cbn. intros t t'. unfold univalent_transport.
      rewrite Equiv_avl_id. cbn. tc.
    Defined.

    Fixpoint orn_balance {lo hi ord} (t : Ordered.bst lo hi ord) : {h:nat & {bal:bool & avl lo hi ord h bal}} :=
      match t with
      | Ordered.Branch _ _ _ _ _ _ v l r =>
        (_; (_; Branch _ _ _ _ _ _ _ _ _ _ v (orn_balance l).2.2 (orn_balance r).2.2))
      | Ordered.Leaf v =>
        (_; (_; Leaf v))
      end.

    Fixpoint orn_balance_inv' {lo hi ord h bal} (t : avl lo hi ord h bal) : Ordered.bst lo hi ord :=
      match t with
      | Branch _ _ _ _ _ _ _ _ _ _ v l r =>
        Ordered.Branch _ _ _ _ _ _ v (orn_balance_inv' l) (orn_balance_inv' r)
      | Leaf v =>
        Ordered.Leaf v
      end.

    Definition orn_balance_inv {lo hi ord} (T : {h:nat & {bal:bool & avl lo hi ord h bal}}) : Ordered.bst lo hi ord :=
      orn_balance_inv' T.2.2.

    Instance IsEquiv_orn_balance (lo hi : Elem.t) (ord : bool) : IsEquiv (@orn_balance lo hi ord).
    Proof.
      eapply isequiv_adjointify with (g := orn_balance_inv); unfold orn_balance_inv; cbn.
      - intros t. induction t as [ord_l ord_r lo_l lo_r hi_l hi_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
      - intros [h [bal t]]. cbn. induction t as [bal_l bal_r h_l h_r ord_l ord_r lo_l lo_r hi_l hi_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
    Defined.

    Instance Equiv_orn_balance (lo hi : Elem.t) (ord : bool) :
      Ordered.bst lo hi ord ≃ {h:nat & {bal:bool & avl lo hi ord h bal}} :=
      BuildEquiv _ _ _ (IsEquiv_orn_balance lo hi ord).

    Instance UR_orn_balance (lo hi : Elem.t) (ord : bool) :
      Ordered.bst lo hi ord ⋈ {h:nat & {bal:bool & avl lo hi ord h bal}}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (orn_balance t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ (Equiv_orn_balance lo hi ord)).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Notation avl_sig := (fun lo hi ord => {h:nat & {bal:bool & avl lo hi ord h bal}}) (only parsing).

    Definition tree20 := ↑ Ordered.tree20.2.2.2.
    Definition tree40 := ↑ Ordered.tree40.2.2.2.
    Definition tree60 := ↑ Ordered.tree60.2.2.2.
    Definition tree80 := ↑ Ordered.tree80.2.2.2.
    Definition tree100 := ↑ Ordered.tree100.2.2.2.

    (* 106 LoC in normal form *)
    Definition preorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.preorder lo hi ord).
    Definition preorder {lo hi ord h bal} t := @preorder' lo hi ord (h; (bal; t)).
    Redirect "../out/preorder/avlUP20" Time Eval vm_compute in (preorder' tree20).
    Redirect "../out/preorder/avlUP40" Time Eval vm_compute in (preorder' tree40).
    Redirect "../out/preorder/avlUP60" Time Eval vm_compute in (preorder' tree60).
    Redirect "../out/preorder/avlUP80" Time Eval vm_compute in (preorder' tree80).
    Redirect "../out/preorder/avlUP100" Time Eval vm_compute in (preorder' tree100).

    (* 105 LoC in normal form *)
    Definition inorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.inorder lo hi ord).
    Definition inorder {lo hi ord h bal} t := @inorder' lo hi ord (h; (bal; t)).
    Redirect "../out/inorder/avlUP20" Time Eval vm_compute in (inorder' tree20).
    Redirect "../out/inorder/avlUP40" Time Eval vm_compute in (inorder' tree40).
    Redirect "../out/inorder/avlUP60" Time Eval vm_compute in (inorder' tree60).
    Redirect "../out/inorder/avlUP80" Time Eval vm_compute in (inorder' tree80).
    Redirect "../out/inorder/avlUP100" Time Eval vm_compute in (inorder' tree100).

    (* 112 LoC in normal form *)
    Definition postorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.postorder lo hi ord).
    Definition postorder {lo hi ord h bal} t := @postorder' lo hi ord (h; (bal; t)).
    Redirect "../out/postorder/avlUP20" Time Eval vm_compute in (postorder' tree20).
    Redirect "../out/postorder/avlUP40" Time Eval vm_compute in (postorder' tree40).
    Redirect "../out/postorder/avlUP60" Time Eval vm_compute in (postorder' tree60).
    Redirect "../out/postorder/avlUP80" Time Eval vm_compute in (postorder' tree80).
    Redirect "../out/postorder/avlUP100" Time Eval vm_compute in (postorder' tree100).

    (* 105 LoC in normal form *)
    Definition search' {lo hi ord} : {h:nat & {bal:bool & avl lo hi ord h bal}} -> Elem.t -> bool :=
      ↑ (@Ordered.search lo hi ord).
    Definition search {lo hi ord h bal} (t : avl lo hi ord h bal) (x : Elem.t) : bool :=
      @search' lo hi ord (h; (bal; t)) x.
    Redirect "../out/search/avlUP20" Time Eval vm_compute in (search' tree20 Elem.x).
    Redirect "../out/search/avlUP40" Time Eval vm_compute in (search' tree40 Elem.x).
    Redirect "../out/search/avlUP60" Time Eval vm_compute in (search' tree60 Elem.x).
    Redirect "../out/search/avlUP80" Time Eval vm_compute in (search' tree80 Elem.x).
    Redirect "../out/search/avlUP100" Time Eval vm_compute in (search' tree100 Elem.x).

    (* --- Normalized term sizes --- *)
    Redirect "../out/normalized/preorder-avlUP" Eval compute in preorder'.
    Redirect "../out/normalized/postorder-avlUP" Eval compute in postorder'.
    Redirect "../out/normalized/inorder-avlUP" Eval compute in inorder'.
    Redirect "../out/normalized/search-avlUP" Eval compute in search'.

    (* Auto-generated definitions go here in together case study *)
    Module Comparison.
      (* DEF inorder-avl *)
      (* DEF postorder-avl *)
      (* DEF preorder-avl *)
      (* DEF search-avl *)

      (* TIME-SMALL inorder-avl *)
      (* TIME-SMALL postorder-avl *)
      (* TIME-SMALL preorder-avl *)
      (* TIME-SMALL search-avl *)

      (* NORMALIZE inorder-avl *)
      (* NORMALIZE postorder-avl *)
      (* NORMALIZE preorder-avl *)
      (* NORMALIZE search-avl *)
    End Comparison.

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

Fixpoint list_eqb {A} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | (x :: xs), (y :: ys) => eqb x y && list_eqb eqb xs ys
  | nil, nil => true
  | _, _ => false
  end.

(** You can use commands like the following to validate the equivalent behavior of liftings and transports: **)
(* Eval vm_compute in (Bool.eqb (Balanced.search' Balanced.tree100 7) (Balanced.search'' Balanced.tree100.2 3)). *)
