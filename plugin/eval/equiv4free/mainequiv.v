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

Definition eq_ind {A : Type} (x : A) (P : A -> Type) (H : P x) (y : A) (Heq : x = y) :=
  eq_rect A x (fun (a : A) (H0 : x = a) => P a) H y Heq. (* for compatibility *)

Definition sigT_rect {A : Type} {P : A -> Type} (P0 : {x : A & P x} -> Set) (H : forall (x : A) (p : P x), P0 (x; p)) :=
  sigT_rect A P P0 H. (* for compatibility *)

Add Printing Let sigT. (* for consistency *)

(* Set a timeout for Coq commands *)
Set Default Timeout 100.

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

  Definition Decidable_eq_elem : DecidableEq Elem.t.
  Proof.
    constructor. intros x y. pose proof (Elem.eqb_dec x y) as H. destruct (Elem.eqb x y); auto.
  Defined.

  Instance elem_Hset : HSet Elem.t := @Hedberg Elem.t Decidable_eq_elem.
  Instance UR_elem : UR Elem.t Elem.t := UR_gen Elem.t.
  Instance FP_elem : Elem.t ⋈ Elem.t := URType_Refl_decidable Elem.t Decidable_eq_elem.
  Instance Transportable_elem (P : Elem.t -> Type) : Transportable P :=
    @Transportable_decidable _ P Decidable_eq_elem.

  Definition Decidable_eq_list_elem : DecidableEq (list Elem.t).
  Proof.
    constructor. induction a as [|x xs IH]; cbn; intros [|y ys].
    - left. reflexivity.
    - right. inversion 1.
    - right. inversion 1.
    - specialize (IH ys). destruct IH as [E|E].
      + rewrite <- E. clear E. pose proof Decidable_eq_elem. destruct H.  
        destruct (dec_paths x y) as [E|E].
        * rewrite <- E. clear E. left. reflexivity.
        * right. inversion 1. destruct (E H1).
      + right. inversion 1. destruct (E H2).
  Defined.

  Instance list_elem_Hset : HSet (list Elem.t) := @Hedberg (list Elem.t) Decidable_eq_list_elem.

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

    Definition Decidable_eq_tree :  DecidableEq tree.
    Proof.
      constructor. Local Ltac discr := let E := fresh in right; intro E; inversion E; auto; discriminate E.
      Local Ltac recur H x := specialize (H x); destruct H as [H|H]; [rewrite <- H|]; try discr.
      intro x. induction x as [x_v x_l IH_l x_r IH_r|x_v]; intros [y_v y_l y_r|y_v];
      try discr; pose Decidable_eq_elem as H_v; destruct H_v; pose (dec_paths x_v) as H_v'; recur H_v' y_v;
      try recur IH_l y_l; try recur IH_r y_r; left; reflexivity.
    Defined.

    Instance tree_Hset : HSet tree := @Hedberg tree Decidable_eq_tree.
    Instance UR_tree : UR tree tree := UR_gen tree.
    Instance FP_tree : tree ⋈ tree := URType_Refl_decidable tree Decidable_eq_tree.
    Instance Transportable_tree (P: tree -> Type) : Transportable P :=
      @Transportable_decidable _ P Decidable_eq_tree.

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

    (* 13 LoC in normal form *)
    Definition preorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => [x] ++ ys ++ zs)
        (fun x => [x])
        t.
    Redirect "../out/preorder/baseEFF1equiv" Time Eval vm_compute in (preorder tree1).
    Redirect "../out/preorder/baseEFF10equiv" Time Eval vm_compute in (preorder tree10).
    Redirect "../out/preorder/baseEFF100equiv" Time Eval vm_compute in (preorder tree100).
    Redirect "../out/preorder/baseEFF1000equiv" Time Eval vm_compute in (preorder tree1000).
    Redirect "../out/preorder/baseEFF10000equiv" Time Eval vm_compute in (preorder tree10000).

    (* 12 LoC in normal form *)
    Definition inorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ [x] ++ zs)
        (fun x => [x])
        t.
    Redirect "../out/inorder/baseEFF1equiv" Time Eval vm_compute in (inorder tree1).
    Redirect "../out/inorder/baseEFF10equiv" Time Eval vm_compute in (inorder tree10).
    Redirect "../out/inorder/baseEFF100equiv" Time Eval vm_compute in (inorder tree100).
    Redirect "../out/inorder/baseEFF1000equiv" Time Eval vm_compute in (inorder tree1000).
    Redirect "../out/inorder/baseEFF10000equiv" Time Eval vm_compute in (inorder tree10000).

    (* 12 LoC in normal form *)
    Definition postorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ zs ++ [x])
        (fun x => [x])
        t.
    Redirect "../out/postorder/baseEFF1equiv" Time Eval vm_compute in (postorder tree1).
    Redirect "../out/postorder/baseEFF10equiv" Time Eval vm_compute in (postorder tree10).
    Redirect "../out/postorder/baseEFF100equiv" Time Eval vm_compute in (postorder tree100).
    Redirect "../out/postorder/baseEFF1000equiv" Time Eval vm_compute in (postorder tree1000).
    Redirect "../out/postorder/baseEFF10000equiv" Time Eval vm_compute in (postorder tree10000).

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

  End Base.

  (* --- Single iteration: from binary trees to sized binary trees --- *)

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
      rewrite Equiv_tree_id. cbn. eapply Equiv_id.
    Defined.

    (* --- Begin auto-generated equivalences from DEVOID --- *)

    (* EQUIV orn_size_index *)
    (* EQUIV orn_size *)
    (* EQUIV orn_size_inv *)
    (* EQUIV orn_size_section *)
    (* EQUIV orn_size_retraction *)
 
    (* --- End auto-generated equivalences from DEVOID --- *)

    Instance IsEquiv_orn_size : IsEquiv orn_size.
    Proof.
      eapply isequiv_adjointify with (g := orn_size_inv).
      - apply orn_size_section.
      - apply orn_size_retraction.
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

    Definition tree1 := ↑ Base.tree1.
    Definition tree10 := ↑ Base.tree10.
    Definition tree100 := ↑ Base.tree100.
    Definition tree1000 := ↑ Base.tree1000.
    Definition tree10000 := ↑ Base.tree10000.

    (* 38 LoC in normal form *)
    Definition preorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.preorder.
    Definition preorder n t := preorder' (existT _ n t).
    Redirect "../out/preorder/sizedEFF1equiv" Time Eval vm_compute in (preorder' tree1).
    Redirect "../out/preorder/sizedEFF10equiv" Time Eval vm_compute in (preorder' tree10).
    Redirect "../out/preorder/sizedEFF100equiv" Time Eval vm_compute in (preorder' tree100).
    Redirect "../out/preorder/sizedEFF1000equiv" Time Eval vm_compute in (preorder' tree1000).
    Redirect "../out/preorder/sizedEFF10000equiv" Time Eval vm_compute in (preorder' tree10000).

    (* 37 LoC in normal form *)
    Definition inorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.inorder.
    Definition inorder n t := inorder' (existT _ n t).
    Redirect "../out/inorder/sizedEFF1equiv" Time Eval vm_compute in (inorder' tree1).
    Redirect "../out/inorder/sizedEFF10equiv" Time Eval vm_compute in (inorder' tree10).
    Redirect "../out/inorder/sizedEFF100equiv" Time Eval vm_compute in (inorder' tree100).
    Redirect "../out/inorder/sizedEFF1000equiv" Time Eval vm_compute in (inorder' tree1000).
    Redirect "../out/inorder/sizedEFF10000equiv" Time Eval vm_compute in (inorder' tree10000).

    (* 43 LoC in normal form *)
    Definition postorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.postorder.
    Definition postorder n t := postorder' (existT _ n t).
    Redirect "../out/postorder/sizedEFF1equiv" Time Eval vm_compute in (postorder' tree1).
    Redirect "../out/postorder/sizedEFF10equiv" Time Eval vm_compute in (postorder' tree10).
    Redirect "../out/postorder/sizedEFF100equiv" Time Eval vm_compute in (postorder' tree100).
    Redirect "../out/postorder/sizedEFF1000equiv" Time Eval vm_compute in (postorder' tree1000).
    Redirect "../out/postorder/sizedEFF10000equiv" Time Eval vm_compute in (postorder' tree10000).

    Lemma FP_preorder : Base.preorder ≈ preorder'.
    Proof.
      intros t t' U. cbn in U. rewrite <- U. unfold preorder'. generalize Base.preorder.
      intros f. cbn. rewrite list_rect_eta. pose proof orn_size_coh. compute in H. compute. rewrite H. 
      eapply UR_list_refl.
    Defined.

    Hint Extern 0 (Base.preorder ?t ≈ preorder' ?t') => unshelve refine (FP_preorder t t' _); intros :  typeclass_instances.

    Lemma FP_inorder : Base.inorder ≈ inorder'.
    Proof.
      intros t t' U. cbn in U. rewrite <- U. unfold inorder'. generalize Base.inorder.
      intros f. cbn. rewrite list_rect_eta. pose proof orn_size_coh. compute in H. compute. rewrite H. 
      eapply UR_list_refl.
    Defined.

    Hint Extern 0 (Base.inorder ?t ≈ inorder' ?t') => unshelve refine (FP_inorder t t' _); intros :  typeclass_instances.

    Lemma FP_postorder : Base.postorder ≈ postorder'.
    Proof.
      intros t t' U. cbn in U. rewrite <- U. unfold postorder'. generalize Base.postorder.
      intros f. cbn. rewrite list_rect_eta. pose proof orn_size_coh. compute in H. compute. rewrite H. 
      eapply UR_list_refl.
    Defined.

    Hint Extern 0 (Base.postorder ?t ≈ postorder' ?t') => unshelve refine (FP_postorder t t' _); intros :  typeclass_instances.

    Definition pre_permutes' : forall (t : {n:nat & tree n}), permutes (preorder' t) (inorder' t) :=
      ↑ Base.pre_permutes.

    (* --- Normalized term sizes --- *)
    Redirect "../out/normalized/preorder-sizedEFFequiv" Eval compute in preorder'.
    Redirect "../out/normalized/postorder-sizedEFFequiv" Eval compute in postorder'.
    Redirect "../out/normalized/inorder-sizedEFFequiv" Eval compute in inorder'.
    (*Redirect "../out/normalized/pre_permutes-sizedEFFequiv" Eval compute in pre_permutes'.*)

    (* Auto-generated definitions go here in together case study *)
    Module Comparison.
      (* DEF inorder-sized *)
      (* DEF postorder-sized *)
      (* DEF preorder-sized *)
      (* DEF pre_permutes-sized *)

      (* TIME-SIZED inorder-sized *)
      (* TIME-SIZED postorder-sized *)
      (* TIME-SIZED preorder-sized *)

      (* NORMALIZE inorder-sized *)
      (* NORMALIZE postorder-sized *)
      (* NORMALIZE preorder-sized *)
      (* NORMALIZE pre_permutes-sized *)
    End Comparison.

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
      econstructor. cbn. intros t t'. unfold univalent_transport. rewrite Equiv_bst_id. cbn. eapply Equiv_id.
    Defined.

    (* --- Begin auto-generated equivalences from DEVOID --- *)

    (* EQUIV __orn_order_index *)
    (* EQUIV __orn_order *)
    (* EQUIV __orn_order_inv *)
    (* EQUIV __orn_order_section *)
    (* EQUIV __orn_order_retraction *)
    (* EQUIV _orn_order_index *)
    (* EQUIV _orn_order *)
    (* EQUIV _orn_order_inv *)
    (* EQUIV _orn_order_section *)
    (* EQUIV _orn_order_retraction *)
    (* EQUIV orn_order_index *)
    (* EQUIV orn_order *)
    (* EQUIV orn_order_inv *)
    (* EQUIV orn_order_section *)
    (* EQUIV orn_order_retraction *)
 
    (* --- End auto-generated equivalences from DEVOID --- *)
 
   Instance IsEquiv___orn_order : IsEquiv __orn_order.
    Proof.
      intros. eapply isequiv_adjointify with (g := __orn_order_inv).
      - apply __orn_order_section.
      - apply __orn_order_retraction.
    Defined.

    Instance IsEquiv__orn_order : forall t, IsEquiv (_orn_order t).
    Proof.
      intros. eapply isequiv_adjointify with (g := _orn_order_inv t).
      - apply _orn_order_section.
      - apply _orn_order_retraction.
    Defined. 

    Instance IsEquiv_orn_order : forall t t0, IsEquiv (orn_order t t0).
    Proof.
      intros. eapply isequiv_adjointify with (g := orn_order_inv t t0).
      - apply orn_order_section.
      - apply orn_order_retraction.
    Defined. 

    Instance Equiv___orn_order : Base.tree ≃ {lo:Elem.t & __bst lo} :=
      BuildEquiv _ _ _ IsEquiv___orn_order.

    Instance Equiv__orn_order : forall (lo : Elem.t), __bst lo ≃ {hi:Elem.t & _bst lo hi} :=
      fun lo => BuildEquiv _ _ _ (IsEquiv__orn_order lo).

    Instance Equiv_orn_order : forall (lo hi : Elem.t), _bst lo hi ≃ {ord : bool & bst lo hi ord} :=
      fun lo hi => BuildEquiv _ _ _ (IsEquiv_orn_order lo hi).

    Instance UR___orn_order : Base.tree ⋈ {lo:Elem.t & __bst lo}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (__orn_order t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ Equiv___orn_order).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Instance UR__orn_order : forall (lo : Elem.t), __bst lo ⋈ {hi:Elem.t & _bst lo hi}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (_orn_order lo t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ (Equiv__orn_order lo)).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Instance UR_orn_order : forall (lo hi : Elem.t), _bst lo hi ⋈ {ord:bool & bst lo hi ord}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (orn_order lo hi t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ (Equiv_orn_order lo hi)).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Definition __tree1 := ↑ Base.tree1.
    Definition _tree1 := ↑ (__tree1 .2).
    Definition tree1 := (↑ (_tree1 .2)).2.
    Definition __tree10 := ↑ Base.tree10.
    Definition _tree10 := ↑ (__tree10 .2).
    Definition tree10 := (↑ (_tree10 .2)).2.
    Definition __tree100 := ↑ Base.tree100.
    Definition _tree100 := ↑ (__tree100 .2).
    Definition tree100 := (↑ (_tree100 .2)).2.
    Definition __tree1000 := ↑ Base.tree1000.
    Definition _tree1000 := ↑ (__tree1000 .2).
    Definition tree1000 := (↑ (_tree1000 .2)).2.
    Definition __tree10000 := ↑ Base.tree10000.
    Definition _tree10000 := ↑ (__tree10000 .2).
    Definition tree10000 := (↑ (_tree10000 .2)).2.

    (* For consistency, follow the same process *)
    Definition __preorder'  : {lo:Elem.t & __bst lo} -> list Elem.t := ↑ Base.preorder.
    Definition __preorder lo t := __preorder' (lo; t).
    Definition _preorder' lo : {hi:Elem.t & _bst lo hi} -> list Elem.t := ↑ (__preorder lo).
    Definition _preorder lo hi t := _preorder' lo (hi; t).
    Definition preorder' lo hi : {ord : bool & bst lo hi ord} -> list Elem.t := ↑ (_preorder lo hi).
    Definition preorder {lo hi ord} t := preorder' lo hi (ord; t).

    Definition __inorder'  : {lo:Elem.t & __bst lo} -> list Elem.t := ↑ Base.inorder.
    Definition __inorder lo t := __inorder' (lo; t).
    Definition _inorder' lo : {hi:Elem.t & _bst lo hi} -> list Elem.t := ↑ (__inorder lo).
    Definition _inorder lo hi t := _inorder' lo (hi; t).
    Definition inorder' lo hi : {ord : bool & bst lo hi ord} -> list Elem.t := ↑ (_inorder lo hi).
    Definition inorder {lo hi ord} t := inorder' lo hi (ord; t).

    Definition __postorder'  : {lo:Elem.t & __bst lo} -> list Elem.t := ↑ Base.postorder.
    Definition __postorder lo t := __postorder' (lo; t).
    Definition _postorder' lo : {hi:Elem.t & _bst lo hi} -> list Elem.t := ↑ (__postorder lo).
    Definition _postorder lo hi t := _postorder' lo (hi; t).
    Definition postorder' lo hi : {ord : bool & bst lo hi ord} -> list Elem.t := ↑ (_postorder lo hi).
    Definition postorder {lo hi ord} t := postorder' lo hi (ord; t).

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

    (* --- Base search data --- *)
    Redirect "../out/search/baseEFF1equiv" Time Eval vm_compute in (search tree1 Elem.x).
    Redirect "../out/search/baseEFF10equiv" Time Eval vm_compute in (search tree10 Elem.x).
    Redirect "../out/search/baseEFF100equiv" Time Eval vm_compute in (search tree100 Elem.x).
    Redirect "../out/search/baseEFF1000equiv" Time Eval vm_compute in (search tree1000 Elem.x).
    Redirect "../out/search/baseEFF10000equiv" Time Eval vm_compute in (search tree10000 Elem.x).


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
      rewrite Equiv_avl_id. cbn. eapply Equiv_id.
    Defined.

    (* --- Begin auto-generated equivalences from DEVOID --- *)

    (* EQUIV _orn_balance_index *)
    (* EQUIV _orn_balance *)
    (* EQUIV _orn_balance_inv *)
    (* EQUIV _orn_balance_section *)
    (* EQUIV _orn_balance_retraction *)
    (* EQUIV orn_balance_index *)
    (* EQUIV orn_balance *)
    (* EQUIV orn_balance_inv *)
    (* EQUIV orn_balance_section *)
    (* EQUIV orn_balance_retraction *)
 
    (* --- End auto-generated equivalences from DEVOID --- *)

    Instance IsEquiv__orn_balance (lo hi : Elem.t) (ord : bool) : IsEquiv (_orn_balance lo hi ord).
    Proof.
      eapply isequiv_adjointify with (g := _orn_balance_inv lo hi ord).
      - apply _orn_balance_section.
      - apply _orn_balance_retraction.
    Defined.

   Instance IsEquiv_orn_balance (lo hi : Elem.t) (ord : bool) (n : nat) : IsEquiv (orn_balance lo hi ord n).
    Proof.
      eapply isequiv_adjointify with (g := orn_balance_inv lo hi ord n).
      - apply orn_balance_section.
      - apply orn_balance_retraction.
    Defined.

    Instance Equiv__orn_balance (lo hi : Elem.t) (ord : bool) :
      Ordered.bst lo hi ord ≃ {n : nat & _avl lo hi ord n} :=
      BuildEquiv _ _ _ (IsEquiv__orn_balance lo hi ord).

    Instance Equiv_orn_balance (lo hi : Elem.t) (ord : bool) (n : nat) :
      _avl lo hi ord n ≃ {bal : bool & avl lo hi ord n bal} :=
      BuildEquiv _ _ _ (IsEquiv_orn_balance lo hi ord n).

    Instance UR__orn_balance (lo hi : Elem.t) (ord : bool) :
      Ordered.bst lo hi ord ⋈ {n : nat & _avl lo hi ord n}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (_orn_balance lo hi ord t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ (Equiv__orn_balance lo hi ord)).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Instance UR_orn_balance (lo hi : Elem.t) (ord : bool) (n : nat) :
      _avl lo hi ord n ⋈ {bal : bool & avl lo hi ord n bal}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (orn_balance lo hi ord n t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ (Equiv_orn_balance lo hi ord n)).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Definition _tree1 := ↑ Ordered.tree1.
    Definition tree1 := ↑ _tree1.2.
    Definition _tree10 := ↑ Ordered.tree10.
    Definition tree10 := ↑ _tree10.2.
    Definition _tree100 := ↑ Ordered.tree100.
    Definition tree100 := ↑ _tree100.2.
    Definition _tree1000 := ↑ Ordered.tree1000.
    Definition tree1000 := ↑ _tree1000.2.
    Definition _tree10000 := ↑ Ordered.tree10000.
    Definition tree10000 := ↑ _tree10000.2.

    Definition _preorder' lo hi ord : {n : nat & _avl lo hi ord n} -> list Elem.t :=
      ↑ (@Ordered.preorder lo hi ord).
    Definition _preorder lo hi ord n t := _preorder' lo hi ord (n; t).
    Definition preorder' {lo hi ord n} : {bal : bool & avl lo hi ord n bal} -> list Elem.t := 
      ↑ (_preorder lo hi ord n).
    Definition preorder {lo hi ord n bal} t := @preorder' lo hi ord n (bal; t).
    Redirect "../out/preorder/avlEFF1equiv" Time Eval vm_compute in (preorder' tree1).
    Redirect "../out/preorder/avlEFF10equiv" Time Eval vm_compute in (preorder' tree10).
    Redirect "../out/preorder/avlEFF100equiv" Time Eval vm_compute in (preorder' tree100).
    Redirect "../out/preorder/avlEFF1000equiv" Time Eval vm_compute in (preorder' tree1000).
    Redirect "../out/preorder/avlEFF10000equiv" Time Eval vm_compute in (preorder' tree10000).

   (* 105 LoC in normal form *)
    Definition _inorder' lo hi ord : {n : nat & _avl lo hi ord n} -> list Elem.t :=
      ↑ (@Ordered.inorder lo hi ord).
    Definition _inorder lo hi ord n t := _inorder' lo hi ord (n; t).
    Definition inorder' {lo hi ord n} : {bal : bool & avl lo hi ord n bal} -> list Elem.t := 
      ↑ (_inorder lo hi ord n).
    Definition inorder {lo hi ord n bal} t := @inorder' lo hi ord n (bal; t).
    Redirect "../out/inorder/avlEFF1equiv" Time Eval vm_compute in (inorder' tree1).
    Redirect "../out/inorder/avlEFF10equiv" Time Eval vm_compute in (inorder' tree10).
    Redirect "../out/inorder/avlEFF100equiv" Time Eval vm_compute in (inorder' tree100).
    Redirect "../out/inorder/avlEFF1000equiv" Time Eval vm_compute in (inorder' tree1000).
    Redirect "../out/inorder/avlEFF10000equiv" Time Eval vm_compute in (inorder' tree10000).

    (* 112 LoC in normal form *)
    Definition _postorder' lo hi ord : {n : nat & _avl lo hi ord n} -> list Elem.t :=
      ↑ (@Ordered.postorder lo hi ord).
    Definition _postorder lo hi ord n t := _postorder' lo hi ord (n; t).
    Definition postorder' {lo hi ord n} : {bal : bool & avl lo hi ord n bal} -> list Elem.t := 
      ↑ (_postorder lo hi ord n).
    Definition postorder {lo hi ord n bal} t := @postorder' lo hi ord n (bal; t).
    Redirect "../out/postorder/avlEFF1equiv" Time Eval vm_compute in (postorder' tree1).
    Redirect "../out/postorder/avlEFF10equiv" Time Eval vm_compute in (postorder' tree10).
    Redirect "../out/postorder/avlEFF100equiv" Time Eval vm_compute in (postorder' tree100).
    Redirect "../out/postorder/avlEFF1000equiv" Time Eval vm_compute in (postorder' tree1000).
    Redirect "../out/postorder/avlEFF10000equiv" Time Eval vm_compute in (postorder' tree10000).

    (* 105 LoC in normal form *)
    Definition _search' lo hi ord : {n : nat & _avl lo hi ord n} -> Elem.t -> bool :=
      ↑ (@Ordered.search lo hi ord).
    Definition _search lo hi ord n t x := _search' lo hi ord (n; t) x.
    Definition search' {lo hi ord n} : {bal : bool & avl lo hi ord n bal} -> Elem.t -> bool := 
      ↑ (_search lo hi ord n).
    Definition search {lo hi ord n bal} t x := @search' lo hi ord n (bal; t) x.
    Redirect "../out/search/avlEFF1equiv" Time Eval vm_compute in (search' tree1 Elem.x).
    Redirect "../out/search/avlEFF10equiv" Time Eval vm_compute in (search' tree10 Elem.x).
    Redirect "../out/search/avlEFF100equiv" Time Eval vm_compute in (search' tree100 Elem.x).
    Redirect "../out/search/avlEFF1000equiv" Time Eval vm_compute in (search' tree1000 Elem.x).
    Redirect "../out/search/avlEFF10000equiv" Time Eval vm_compute in (search' tree10000 Elem.x).

    (* --- Normalized term sizes --- *)
    Redirect "../out/normalized/preorder-avlEFFequiv" Eval compute in preorder'.
    Redirect "../out/normalized/postorder-avlEFFequiv" Eval compute in postorder'.
    Redirect "../out/normalized/inorder-avlEFFequiv" Eval compute in inorder'.
    Redirect "../out/normalized/search-avlEFFequiv" Eval compute in search'.

    (* Auto-generated definitions go here in together case study *)
    Module Comparison.
      (* DEF inorder-avl *)
      (* DEF postorder-avl *)
      (* DEF preorder-avl *)
      (* DEF search-avl *)

      (* TIME-AVL inorder-avl *)
      (* TIME-AVL postorder-avl *)
      (* TIME-AVL preorder-avl *)
      (* TIME-SEARCH search-avl *)

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
