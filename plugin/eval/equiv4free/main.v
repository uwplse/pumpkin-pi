From UnivalentParametricity Require Import HoTT UR URTactics FP Record MoreInductive.
Require Import PeanoNat list perm lemmas.

(* TODO run these to make sure results the same still *)
(* TODO copy old version to a file; include both *)

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
    Redirect "out/treeEFF20" Time Eval vm_compute in tree20.
    Redirect "out/treeEFF40" Time Eval vm_compute in tree40.
    Redirect "out/treeEFF60" Time Eval vm_compute in tree60.
    Redirect "out/treeEFF80" Time Eval vm_compute in tree80.
    Redirect "out/treeEFF100" Time Eval vm_compute in tree100.
    Redirect "out/treeEFF200" Time Eval vm_compute in tree200.
    Redirect "out/treeEFF400" Time Eval vm_compute in tree400.
    Redirect "out/treeEFF600" Time Eval vm_compute in tree600.
    Redirect "out/treeEFF800" Time Eval vm_compute in tree800.
    Redirect "out/treeEFF1000" Time Eval vm_compute in tree1000.
    Redirect "out/treeEFF2000" Time Eval vm_compute in tree2000.
    Redirect "out/treeEFF4000" Time Eval vm_compute in tree4000.
    Redirect "out/treeEFF6000" Time Eval vm_compute in tree6000.
    Redirect "out/treeEFF8000" Time Eval vm_compute in tree8000.
    Redirect "out/treeEFF10000" Time Eval vm_compute in tree10000.

    Redirect "../out/preorder/baseEFF20" Time Eval vm_compute in (preorder tree20).
    Redirect "../out/preorder/baseEFF40" Time Eval vm_compute in (preorder tree40).
    Redirect "../out/preorder/baseEFF60" Time Eval vm_compute in (preorder tree60).
    Redirect "../out/preorder/baseEFF80" Time Eval vm_compute in (preorder tree80).
    Redirect "../out/preorder/baseEFF100" Time Eval vm_compute in (preorder tree100).
    Redirect "../out/preorder/baseEFF200" Time Eval vm_compute in (preorder tree200).
    Redirect "../out/preorder/baseEFF400" Time Eval vm_compute in (preorder tree400).
    Redirect "../out/preorder/baseEFF600" Time Eval vm_compute in (preorder tree600).
    Redirect "../out/preorder/baseEFF800" Time Eval vm_compute in (preorder tree800).
    Redirect "../out/preorder/baseEFF1000" Time Eval vm_compute in (preorder tree1000).
    Redirect "../out/preorder/baseEFF2000" Time Eval vm_compute in (preorder tree2000).
    Redirect "../out/preorder/baseEFF4000" Time Eval vm_compute in (preorder tree4000).
    Redirect "../out/preorder/baseEFF6000" Time Eval vm_compute in (preorder tree6000).
    Redirect "../out/preorder/baseEFF8000" Time Eval vm_compute in (preorder tree8000).
    Redirect "../out/preorder/baseEFF10000" Time Eval vm_compute in (preorder tree10000).

    (* 12 LoC in normal form *)
    Definition inorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ [x] ++ zs)
        (fun x => [x])
        t.
    Redirect "../out/inorder/baseEFF20" Time Eval vm_compute in (inorder tree20).
    Redirect "../out/inorder/baseEFF40" Time Eval vm_compute in (inorder tree40).
    Redirect "../out/inorder/baseEFF60" Time Eval vm_compute in (inorder tree60).
    Redirect "../out/inorder/baseEFF80" Time Eval vm_compute in (inorder tree80).
    Redirect "../out/inorder/baseEFF100" Time Eval vm_compute in (inorder tree100).
    Redirect "../out/inorder/baseEFF200" Time Eval vm_compute in (inorder tree200).
    Redirect "../out/inorder/baseEFF400" Time Eval vm_compute in (inorder tree400).
    Redirect "../out/inorder/baseEFF600" Time Eval vm_compute in (inorder tree600).
    Redirect "../out/inorder/baseEFF800" Time Eval vm_compute in (inorder tree800).
    Redirect "../out/inorder/baseEFF1000" Time Eval vm_compute in (inorder tree1000).
    Redirect "../out/inorder/baseEFF2000" Time Eval vm_compute in (inorder tree2000).
    Redirect "../out/inorder/baseEFF4000" Time Eval vm_compute in (inorder tree4000).
    Redirect "../out/inorder/baseEFF6000" Time Eval vm_compute in (inorder tree6000).
    Redirect "../out/inorder/baseEFF8000" Time Eval vm_compute in (inorder tree8000).
    Redirect "../out/inorder/baseEFF10000" Time Eval vm_compute in (inorder tree10000).

    (* 12 LoC in normal form *)
    Definition postorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ zs ++ [x])
        (fun x => [x])
        t.
    Redirect "../out/postorder/baseEFF20" Time Eval vm_compute in (postorder tree20).
    Redirect "../out/postorder/baseEFF40" Time Eval vm_compute in (postorder tree40).
    Redirect "../out/postorder/baseEFF60" Time Eval vm_compute in (postorder tree60).
    Redirect "../out/postorder/baseEFF80" Time Eval vm_compute in (postorder tree80).
    Redirect "../out/postorder/baseEFF100" Time Eval vm_compute in (postorder tree100).
    Redirect "../out/postorder/baseEFF200" Time Eval vm_compute in (postorder tree200).
    Redirect "../out/postorder/baseEFF400" Time Eval vm_compute in (postorder tree400).
    Redirect "../out/postorder/baseEFF600" Time Eval vm_compute in (postorder tree600).
    Redirect "../out/postorder/baseEFF800" Time Eval vm_compute in (postorder tree800).
    Redirect "../out/postorder/baseEFF1000" Time Eval vm_compute in (postorder tree1000).
    Redirect "../out/postorder/baseEFF2000" Time Eval vm_compute in (postorder tree2000).
    Redirect "../out/postorder/baseEFF4000" Time Eval vm_compute in (postorder tree4000).
    Redirect "../out/postorder/baseEFF6000" Time Eval vm_compute in (postorder tree6000).
    Redirect "../out/postorder/baseEFF8000" Time Eval vm_compute in (postorder tree8000).
    Redirect "../out/postorder/baseEFF10000" Time Eval vm_compute in (postorder tree10000).

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

    (* --- Begin automatically generated terms from DEVOID --- *)
    (* TODO copy these in automatically *)

    Definition orn_size_index := 
fun t : Base.tree =>
Base.tree_rect (fun _ : Base.tree => nat)
  (fun (_ : Elem.t) (left : Base.tree) (H : (fun _ : Base.tree => nat) left)
     (right : Base.tree) (H0 : (fun _ : Base.tree => nat) right) =>
   S (H + H0)) (fun _ : Elem.t => 1) t.

   Definition orn_size := 
fun t : Base.tree =>
existT (fun H : nat => tree H) (orn_size_index t)
  (Base.tree_rect (fun t0 : Base.tree => tree (orn_size_index t0))
     (fun (val : Elem.t) (left : Base.tree)
        (H : (fun (_ : nat) (t0 : Base.tree) => tree (orn_size_index t0))
               (orn_size_index left) left) (right : Base.tree)
        (H0 : (fun (_ : nat) (t0 : Base.tree) => tree (orn_size_index t0))
                (orn_size_index right) right) =>
      Branch (orn_size_index left) (orn_size_index right) val H H0)
     (fun val : Elem.t => Leaf val) t).

   Definition orn_size_inv := 
fun t : {H : nat & tree H} =>
tree_rect (fun (n : nat) (_ : tree n) => Base.tree)
  (fun (n_l n_r : nat) (val : Elem.t) (_ : tree n_l) 
     (H : Base.tree) (_ : tree n_r) (H0 : Base.tree) => 
   Base.Branch val H H0) (fun val : Elem.t => Base.Leaf val) 
  t .1 t .2.

  Definition orn_size_section := 
fun t : Base.tree =>
eq_sym
  (Base.tree_rect (fun t0 : Base.tree => t0 = orn_size_inv (orn_size t0))
     (fun (val : Elem.t) (left : Base.tree)
        (H : left = orn_size_inv (orn_size left)) 
        (right : Base.tree) (H0 : right = orn_size_inv (orn_size right)) =>
      eq_ind left
        (fun H1 : Base.tree =>
          Base.Branch val left right =
          Base.Branch val H1 (orn_size_inv (orn_size right)))
        (eq_ind right
           (fun H1 : Base.tree =>
            Base.Branch val left right = Base.Branch val left H1) eq_refl
           (orn_size_inv (orn_size right)) H0) (orn_size_inv (orn_size left))
        H) (fun val : Elem.t => eq_refl) t).

Definition orn_size_retraction := 
fun t : {H : nat & tree H} =>
sigT_rect (fun t0 : {H : nat & tree H} => orn_size (orn_size_inv t0) = t0)
  (fun (H : nat) (H0 : (fun H0 : nat => tree H0) H) =>
   eq_sym
     (tree_rect
        (fun (n : nat) (t0 : tree n) =>
         existT (fun H1 : nat => tree H1) n t0 =
         orn_size (orn_size_inv (existT (fun H1 : nat => tree H1) n t0)))
        (fun (n_l n_r : nat) (val : Elem.t) (left : tree n_l)
           (H1 : existT (fun H1 : nat => tree H1) n_l left =
                 orn_size
                   (orn_size_inv (existT (fun H1 : nat => tree H1) n_l left)))
           (right : tree n_r)
           (H2 : existT (fun H2 : nat => tree H2) n_r right =
                 orn_size
                   (orn_size_inv (existT (fun H2 : nat => tree H2) n_r right)))
         =>
         eq_ind (existT (fun H3 : nat => tree H3) n_l left)
           (fun H3 : {H3 : nat & tree H3} =>
            existT (fun H4 : nat => tree H4) (S (n_l + n_r))
              (Branch n_l n_r val left right) =
            existT (fun H4 : nat => tree H4)
              (S
                 (H3 .1 +
                  (orn_size
                     (orn_size_inv
                        (existT (fun H4 : nat => tree H4) n_r right))) .1))
              (Branch H3 .1
                 (orn_size
                    (orn_size_inv
                       (existT (fun H4 : nat => tree H4) n_r right))) .1 val
                 H3 .2
                 (orn_size
                    (orn_size_inv
                       (existT (fun H4 : nat => tree H4) n_r right))) .2))
           (eq_ind (existT (fun H3 : nat => tree H3) n_r right)
              (fun H3 : {H3 : nat & tree H3} =>
               existT (fun H4 : nat => tree H4) (S (n_l + n_r))
                 (Branch n_l n_r val left right) =
               existT (fun H4 : nat => tree H4) (S (n_l + H3 .1))
                 (Branch n_l H3 .1 val left H3 .2)) eq_refl
              (existT (fun H3 : nat => tree H3)
                 (orn_size
                    (orn_size_inv
                       (existT (fun H3 : nat => tree H3) n_r right))) .1
                 (orn_size
                    (orn_size_inv
                       (existT (fun H3 : nat => tree H3) n_r right))) .2) H2)
           (existT (fun H3 : nat => tree H3)
              (orn_size
                 (orn_size_inv (existT (fun H3 : nat => tree H3) n_l left)))
              .1
              (orn_size
                 (orn_size_inv (existT (fun H3 : nat => tree H3) n_l left)))
              .2) H1) (fun val : Elem.t => eq_refl) H H0)) t.

    (* --- End automatically generated terms from DEVOID --- *)

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

    Definition tree2000 := ↑ Base.tree2000.
    Definition tree4000 := ↑ Base.tree4000.
    Definition tree6000 := ↑ Base.tree6000.
    Definition tree8000 := ↑ Base.tree8000.
    Definition tree10000 := ↑ Base.tree10000.

    (* 38 LoC in normal form *)
    Definition preorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.preorder.
    Definition preorder n t := preorder' (existT _ n t).
    Redirect "../out/preorder/sizedEFF2000" Time Eval vm_compute in (preorder' tree2000).
    Redirect "../out/preorder/sizedEFF4000" Time Eval vm_compute in (preorder' tree4000).
    Redirect "../out/preorder/sizedEFF6000" Time Eval vm_compute in (preorder' tree6000).
    Redirect "../out/preorder/sizedEFF8000" Time Eval vm_compute in (preorder' tree8000).
    Redirect "../out/preorder/sizedEFF10000" Time Eval vm_compute in (preorder' tree10000).

    (* 37 LoC in normal form *)
    Definition inorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.inorder.
    Definition inorder n t := inorder' (existT _ n t).
    Redirect "../out/inorder/sizedEFF2000" Time Eval vm_compute in (inorder' tree2000).
    Redirect "../out/inorder/sizedEFF4000" Time Eval vm_compute in (inorder' tree4000).
    Redirect "../out/inorder/sizedEFF6000" Time Eval vm_compute in (inorder' tree6000).
    Redirect "../out/inorder/sizedEFF8000" Time Eval vm_compute in (inorder' tree8000).
    Redirect "../out/inorder/sizedEFF10000" Time Eval vm_compute in (inorder' tree10000).

    (* 43 LoC in normal form *)
    Definition postorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.postorder.
    Definition postorder n t := postorder' (existT _ n t).
    Redirect "../out/postorder/sizedEFF2000" Time Eval vm_compute in (postorder' tree2000).
    Redirect "../out/postorder/sizedEFF4000" Time Eval vm_compute in (postorder' tree4000).
    Redirect "../out/postorder/sizedEFF6000" Time Eval vm_compute in (postorder' tree6000).
    Redirect "../out/postorder/sizedEFF8000" Time Eval vm_compute in (postorder' tree8000).
    Redirect "../out/postorder/sizedEFF10000" Time Eval vm_compute in (postorder' tree10000).

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
    Redirect "../out/normalized/preorder-sizedEFF" Eval compute in preorder'.
    Redirect "../out/normalized/postorder-sizedEFF" Eval compute in postorder'.
    Redirect "../out/normalized/inorder-sizedEFF" Eval compute in inorder'.
    (* Redirect "../out/normalized/pre_permutes-sizedEFF" Eval compute in pre_permutes'. *)

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

   (* --- Begin automatically generated terms from DEVOID --- *)
   (* TODO paste in automatically *)

   Definition __orn_order_index :=
fun t : Base.tree =>
Base.tree_rect (fun _ : Base.tree => Elem.t)
  (fun (_ : Elem.t) (left : Base.tree)
     (H : (fun _ : Base.tree => Elem.t) left) (right : Base.tree)
     (_ : (fun _ : Base.tree => Elem.t) right) => H)
  (fun val : Elem.t => val) t.

  Definition __orn_order :=
fun t : Base.tree =>
existT (fun H : Elem.t => __bst H) (__orn_order_index t)
  (Base.tree_rect (fun t0 : Base.tree => __bst (__orn_order_index t0))
     (fun (val : Elem.t) (left : Base.tree)
        (H : (fun (_ : Elem.t) (t1 : Base.tree) =>
              __bst (__orn_order_index t1)) (__orn_order_index left) left)
        (right : Base.tree)
        (H0 : (fun (_ : Elem.t) (t1 : Base.tree) =>
               __bst (__orn_order_index t1)) (__orn_order_index right) right)
      => __Branch (__orn_order_index left) (__orn_order_index right) val H H0)
     (fun val : Elem.t => __Leaf val) t).

  Definition __orn_order_inv := 
fun __b : {H : Elem.t & __bst H} =>
__bst_rect (fun (t : Elem.t) (_ : __bst t) => Base.tree)
  (fun (min_l min_r val : Elem.t) (_ : __bst min_l) 
     (H : Base.tree) (_ : __bst min_r) (H0 : Base.tree) =>
   Base.Branch val H H0) (fun val : Elem.t => Base.Leaf val) 
  __b .1 __b .2.

  Definition __orn_order_section := 
fun t : Base.tree =>
eq_sym
  (Base.tree_rect
     (fun t0 : Base.tree => t0 = __orn_order_inv (__orn_order t0))
     (fun (val : Elem.t) (left : Base.tree)
        (H : left = __orn_order_inv (__orn_order left)) 
        (right : Base.tree)
        (H0 : right = __orn_order_inv (__orn_order right)) =>
      eq_ind left
        (fun H1 : Base.tree =>
         Base.Branch val left right =
         Base.Branch val H1 (__orn_order_inv (__orn_order right)))
        (eq_ind right
           (fun H1 : Base.tree =>
            Base.Branch val left right = Base.Branch val left H1) eq_refl
           (__orn_order_inv (__orn_order right)) H0)
        (__orn_order_inv (__orn_order left)) H) (fun val : Elem.t => eq_refl)
     t).

  Definition __orn_order_retraction := 
fun __b : {H : Elem.t & __bst H} =>
sigT_rect
  (fun __b0 : {H : Elem.t & __bst H} =>
   __orn_order (__orn_order_inv __b0) = __b0)
  (fun (H : Elem.t) (H0 : (fun H0 : Elem.t => __bst H0) H) =>
   eq_sym
     (__bst_rect
        (fun (t : Elem.t) (__b0 : __bst t) =>
         existT (fun H1 : Elem.t => __bst H1) t __b0 =
         __orn_order
           (__orn_order_inv (existT (fun H1 : Elem.t => __bst H1) t __b0)))
        (fun (min_l min_r val : Elem.t) (left : __bst min_l)
           (H1 : existT (fun H1 : Elem.t => __bst H1) min_l left =
                 __orn_order
                   (__orn_order_inv
                      (existT (fun H1 : Elem.t => __bst H1) min_l left)))
           (right : __bst min_r)
           (H2 : existT (fun H2 : Elem.t => __bst H2) min_r right =
                 __orn_order
                   (__orn_order_inv
                      (existT (fun H2 : Elem.t => __bst H2) min_r right))) =>
         eq_ind (existT (fun H3 : Elem.t => __bst H3) min_l left)
           (fun H3 : {H3 : Elem.t & __bst H3} =>
            existT (fun H4 : Elem.t => __bst H4) min_l
              (__Branch min_l min_r val left right) =
            existT (fun H4 : Elem.t => __bst H4) H3 .1
              (__Branch H3 .1
                 (__orn_order
                    (__orn_order_inv
                       (existT (fun H4 : Elem.t => __bst H4) min_r right)))
                 .1 val H3 .2
                 (__orn_order
                    (__orn_order_inv
                       (existT (fun H4 : Elem.t => __bst H4) min_r right)))
                 .2))
           (eq_ind (existT (fun H3 : Elem.t => __bst H3) min_r right)
              (fun H3 : {H3 : Elem.t & __bst H3} =>
               existT (fun H4 : Elem.t => __bst H4) min_l
                 (__Branch min_l min_r val left right) =
               existT (fun H4 : Elem.t => __bst H4) min_l
                 (__Branch min_l H3 .1 val left H3 .2)) eq_refl
              (existT (fun H3 : Elem.t => __bst H3)
                 (__orn_order
                    (__orn_order_inv
                       (existT (fun H3 : Elem.t => __bst H3) min_r right)))
                 .1
                 (__orn_order
                    (__orn_order_inv
                       (existT (fun H3 : Elem.t => __bst H3) min_r right)))
                 .2) H2)
           (existT (fun H3 : Elem.t => __bst H3)
              (__orn_order
                 (__orn_order_inv
                    (existT (fun H3 : Elem.t => __bst H3) min_l left))) .1
              (__orn_order
                 (__orn_order_inv
                    (existT (fun H3 : Elem.t => __bst H3) min_l left))) .2)
           H1) (fun val : Elem.t => eq_refl) H H0)) __b.

  Definition _orn_order_index := 
fun (t : Elem.t) (__b : __bst t) =>
__bst_rect (fun (t0 : Elem.t) (_ : __bst t0) => Elem.t)
  (fun (min_l min_r _ : Elem.t) (left : __bst min_l)
     (_ : (fun (t0 : Elem.t) (_ : __bst t0) => Elem.t) min_l left)
     (right : __bst min_r)
     (H : (fun (t0 : Elem.t) (_ : __bst t0) => Elem.t) min_r right) => H)
  (fun val : Elem.t => val) t __b.

  Definition _orn_order := 
fun (t : Elem.t) (__b : __bst t) =>
existT (fun H : Elem.t => _bst t H) (_orn_order_index t __b)
  (__bst_rect
     (fun (t0 : Elem.t) (__b0 : __bst t0) =>
      _bst t0 (_orn_order_index t0 __b0))
     (fun (min_l min_r val : Elem.t) (left : __bst min_l)
        (H : (fun (t0 _ : Elem.t) (__b0 : __bst t0) =>
              _bst t0 (_orn_order_index t0 __b0)) min_l
               (_orn_order_index min_l left) left) 
        (right : __bst min_r)
        (H0 : (fun (t0 _ : Elem.t) (__b0 : __bst t0) =>
               _bst t0 (_orn_order_index t0 __b0)) min_r
                (_orn_order_index min_r right) right) =>
      _Branch min_l min_r (_orn_order_index min_l left)
        (_orn_order_index min_r right) val H H0)
     (fun val : Elem.t => _Leaf val) t __b).

Definition _orn_order_inv := 
fun (t : Elem.t) (_b : {H : Elem.t & _bst t H}) =>
_bst_rect (fun (t0 t1 : Elem.t) (_ : _bst t0 t1) => __bst t0)
  (fun (min_l min_r max_l max_r val : Elem.t) (_ : _bst min_l max_l)
     (H : __bst min_l) (_ : _bst min_r max_r) (H0 : __bst min_r) =>
   __Branch min_l min_r val H H0) (fun val : Elem.t => __Leaf val) t 
  _b .1 _b .2.

Definition _orn_order_section := 
fun (t : Elem.t) (__b : __bst t) =>
eq_sym
  (__bst_rect
     (fun (t0 : Elem.t) (__b0 : __bst t0) =>
      __b0 = _orn_order_inv t0 (_orn_order t0 __b0))
     (fun (min_l min_r val : Elem.t) (left : __bst min_l)
        (H : left = _orn_order_inv min_l (_orn_order min_l left))
        (right : __bst min_r)
        (H0 : right = _orn_order_inv min_r (_orn_order min_r right)) =>
      eq_ind left
        (fun H1 : __bst min_l =>
         __Branch min_l min_r val left right =
         __Branch min_l min_r val H1
           (_orn_order_inv min_r (_orn_order min_r right)))
        (eq_ind right
           (fun H1 : __bst min_r =>
            __Branch min_l min_r val left right =
            __Branch min_l min_r val left H1) eq_refl
           (_orn_order_inv min_r (_orn_order min_r right)) H0)
        (_orn_order_inv min_l (_orn_order min_l left)) H)
     (fun val : Elem.t => eq_refl) t __b).

Definition _orn_order_retraction := 
fun (t : Elem.t) (_b : {H : Elem.t & _bst t H}) =>
sigT_rect
  (fun _b0 : {H : Elem.t & _bst t H} =>
   _orn_order t (_orn_order_inv t _b0) = _b0)
  (fun (H : Elem.t) (H0 : (fun H0 : Elem.t => _bst t H0) H) =>
   eq_sym
     (_bst_rect
        (fun (t0 t1 : Elem.t) (_b0 : _bst t0 t1) =>
         existT (fun H1 : Elem.t => _bst t0 H1) t1 _b0 =
         _orn_order t0
           (_orn_order_inv t0 (existT (fun H1 : Elem.t => _bst t0 H1) t1 _b0)))
        (fun (min_l min_r max_l max_r val : Elem.t) 
           (left : _bst min_l max_l)
           (H1 : existT (fun H1 : Elem.t => _bst min_l H1) max_l left =
                 _orn_order min_l
                   (_orn_order_inv min_l
                      (existT (fun H1 : Elem.t => _bst min_l H1) max_l left)))
           (right : _bst min_r max_r)
           (H2 : existT (fun H2 : Elem.t => _bst min_r H2) max_r right =
                 _orn_order min_r
                   (_orn_order_inv min_r
                      (existT (fun H2 : Elem.t => _bst min_r H2) max_r right)))
         =>
         eq_ind (existT (fun H3 : Elem.t => _bst min_l H3) max_l left)
           (fun H3 : {H3 : Elem.t & _bst min_l H3} =>
            existT (fun H4 : Elem.t => _bst min_l H4) max_r
              (_Branch min_l min_r max_l max_r val left right) =
            existT (fun H4 : Elem.t => _bst min_l H4)
              (_orn_order min_r
                 (_orn_order_inv min_r
                    (existT (fun H4 : Elem.t => _bst min_r H4) max_r right)))
              .1
              (_Branch min_l min_r H3 .1
                 (_orn_order min_r
                    (_orn_order_inv min_r
                       (existT (fun H4 : Elem.t => _bst min_r H4) max_r right)))
                 .1 val H3 .2
                 (_orn_order min_r
                    (_orn_order_inv min_r
                       (existT (fun H4 : Elem.t => _bst min_r H4) max_r right)))
                 .2))
           (eq_ind (existT (fun H3 : Elem.t => _bst min_r H3) max_r right)
              (fun H3 : {H3 : Elem.t & _bst min_r H3} =>
               existT (fun H4 : Elem.t => _bst min_l H4) max_r
                 (_Branch min_l min_r max_l max_r val left right) =
               existT (fun H4 : Elem.t => _bst min_l H4) 
                 H3 .1 (_Branch min_l min_r max_l H3 .1 val left H3 .2))
              eq_refl
              (existT (fun H3 : Elem.t => _bst min_r H3)
                 (_orn_order min_r
                    (_orn_order_inv min_r
                       (existT (fun H3 : Elem.t => _bst min_r H3) max_r right)))
                 .1
                 (_orn_order min_r
                    (_orn_order_inv min_r
                       (existT (fun H3 : Elem.t => _bst min_r H3) max_r right)))
                 .2) H2)
           (existT (fun H3 : Elem.t => _bst min_l H3)
              (_orn_order min_l
                 (_orn_order_inv min_l
                    (existT (fun H3 : Elem.t => _bst min_l H3) max_l left)))
              .1
              (_orn_order min_l
                 (_orn_order_inv min_l
                    (existT (fun H3 : Elem.t => _bst min_l H3) max_l left)))
              .2) H1) (fun val : Elem.t => eq_refl) t H H0)) _b.

Definition orn_order_index := 
fun (t t0 : Elem.t) (_b : _bst t t0) =>
_bst_rect (fun (t1 t2 : Elem.t) (_ : _bst t1 t2) => bool)
  (fun (min_l min_r max_l max_r val : Elem.t) (left : _bst min_l max_l)
     (H : (fun (t1 t2 : Elem.t) (_ : _bst t1 t2) => bool) min_l max_l left)
     (right : _bst min_r max_r)
     (H0 : (fun (t1 t2 : Elem.t) (_ : _bst t1 t2) => bool) min_r max_r right)
   => inv H H0 max_l val min_r) (fun _ : Elem.t => true) t t0 _b.

Definition orn_order := 
fun (t t0 : Elem.t) (_b : _bst t t0) =>
existT (fun H : bool => bst t t0 H) (orn_order_index t t0 _b)
  (_bst_rect
     (fun (t1 t2 : Elem.t) (_b0 : _bst t1 t2) =>
      bst t1 t2 (orn_order_index t1 t2 _b0))
     (fun (min_l min_r max_l max_r val : Elem.t) (left : _bst min_l max_l)
        (H : (fun (t1 t2 : Elem.t) (_ : bool) (_b0 : _bst t1 t2) =>
              bst t1 t2 (orn_order_index t1 t2 _b0)) min_l max_l
               (orn_order_index min_l max_l left) left)
        (right : _bst min_r max_r)
        (H0 : (fun (t1 t2 : Elem.t) (_ : bool) (_b0 : _bst t1 t2) =>
               bst t1 t2 (orn_order_index t1 t2 _b0)) min_r max_r
                (orn_order_index min_r max_r right) right) =>
      Branch (orn_order_index min_l max_l left)
        (orn_order_index min_r max_r right) min_l min_r max_l max_r val H H0)
     (fun val : Elem.t => Leaf val) t t0 _b).

Definition orn_order_inv := 
fun (t t0 : Elem.t) (b : {H : bool & bst t t0 H}) =>
bst_rect (fun (t1 t2 : Elem.t) (b0 : bool) (_ : bst t1 t2 b0) => _bst t1 t2)
  (fun (ord_l ord_r : bool) (min_l min_r max_l max_r val : Elem.t)
     (_ : bst min_l max_l ord_l) (H : _bst min_l max_l)
     (_ : bst min_r max_r ord_r) (H0 : _bst min_r max_r) =>
   _Branch min_l min_r max_l max_r val H H0) (fun val : Elem.t => _Leaf val)
  t t0 b .1 b .2.

Definition orn_order_section := 
fun (t t0 : Elem.t) (_b : _bst t t0) =>
eq_sym
  (_bst_rect
     (fun (t1 t2 : Elem.t) (_b0 : _bst t1 t2) =>
      _b0 = orn_order_inv t1 t2 (orn_order t1 t2 _b0))
     (fun (min_l min_r max_l max_r val : Elem.t) (left : _bst min_l max_l)
        (H : left = orn_order_inv min_l max_l (orn_order min_l max_l left))
        (right : _bst min_r max_r)
        (H0 : right = orn_order_inv min_r max_r (orn_order min_r max_r right))
      =>
      eq_ind left
        (fun H1 : _bst min_l max_l =>
         _Branch min_l min_r max_l max_r val left right =
         _Branch min_l min_r max_l max_r val H1
           (orn_order_inv min_r max_r (orn_order min_r max_r right)))
        (eq_ind right
           (fun H1 : _bst min_r max_r =>
            _Branch min_l min_r max_l max_r val left right =
            _Branch min_l min_r max_l max_r val left H1) eq_refl
           (orn_order_inv min_r max_r (orn_order min_r max_r right)) H0)
        (orn_order_inv min_l max_l (orn_order min_l max_l left)) H)
     (fun val : Elem.t => eq_refl) t t0 _b).

Definition orn_order_retraction := 
fun (t t0 : Elem.t) (b : {H : bool & bst t t0 H}) =>
sigT_rect
  (fun b0 : {H : bool & bst t t0 H} =>
   orn_order t t0 (orn_order_inv t t0 b0) = b0)
  (fun (H : bool) (H0 : (fun H0 : bool => bst t t0 H0) H) =>
   eq_sym
     (bst_rect
        (fun (t1 t2 : Elem.t) (b0 : bool) (b1 : bst t1 t2 b0) =>
         existT (fun H1 : bool => bst t1 t2 H1) b0 b1 =
         orn_order t1 t2
           (orn_order_inv t1 t2
              (existT (fun H1 : bool => bst t1 t2 H1) b0 b1)))
        (fun (ord_l ord_r : bool) (min_l min_r max_l max_r val : Elem.t)
           (left : bst min_l max_l ord_l)
           (H1 : existT (fun H1 : bool => bst min_l max_l H1) ord_l left =
                 orn_order min_l max_l
                   (orn_order_inv min_l max_l
                      (existT (fun H1 : bool => bst min_l max_l H1) ord_l
                         left))) (right : bst min_r max_r ord_r)
           (H2 : existT (fun H2 : bool => bst min_r max_r H2) ord_r right =
                 orn_order min_r max_r
                   (orn_order_inv min_r max_r
                      (existT (fun H2 : bool => bst min_r max_r H2) ord_r
                         right))) =>
         eq_ind (existT (fun H3 : bool => bst min_l max_l H3) ord_l left)
           (fun H3 : {H3 : bool & bst min_l max_l H3} =>
            existT (fun H4 : bool => bst min_l max_r H4)
              (inv ord_l ord_r max_l val min_r)
              (Branch ord_l ord_r min_l min_r max_l max_r val left right) =
            existT (fun H4 : bool => bst min_l max_r H4)
              (inv H3 .1
                 (orn_order min_r max_r
                    (orn_order_inv min_r max_r
                       (existT (fun H4 : bool => bst min_r max_r H4) ord_r
                          right))) .1 max_l val min_r)
              (Branch H3 .1
                 (orn_order min_r max_r
                    (orn_order_inv min_r max_r
                       (existT (fun H4 : bool => bst min_r max_r H4) ord_r
                          right))) .1 min_l min_r max_l max_r val 
                 H3 .2
                 (orn_order min_r max_r
                    (orn_order_inv min_r max_r
                       (existT (fun H4 : bool => bst min_r max_r H4) ord_r
                          right))) .2))
           (eq_ind (existT (fun H3 : bool => bst min_r max_r H3) ord_r right)
              (fun H3 : {H3 : bool & bst min_r max_r H3} =>
               existT (fun H4 : bool => bst min_l max_r H4)
                 (inv ord_l ord_r max_l val min_r)
                 (Branch ord_l ord_r min_l min_r max_l max_r val left right) =
               existT (fun H4 : bool => bst min_l max_r H4)
                 (inv ord_l H3 .1 max_l val min_r)
                 (Branch ord_l H3 .1 min_l min_r max_l max_r val left H3 .2))
              eq_refl
              (existT (fun H3 : bool => bst min_r max_r H3)
                 (orn_order min_r max_r
                    (orn_order_inv min_r max_r
                       (existT (fun H3 : bool => bst min_r max_r H3) ord_r
                          right))) .1
                 (orn_order min_r max_r
                    (orn_order_inv min_r max_r
                       (existT (fun H3 : bool => bst min_r max_r H3) ord_r
                          right))) .2) H2)
           (existT (fun H3 : bool => bst min_l max_l H3)
              (orn_order min_l max_l
                 (orn_order_inv min_l max_l
                    (existT (fun H3 : bool => bst min_l max_l H3) ord_l left)))
              .1
              (orn_order min_l max_l
                 (orn_order_inv min_l max_l
                    (existT (fun H3 : bool => bst min_l max_l H3) ord_l left)))
              .2) H1) (fun val : Elem.t => eq_refl) t t0 H H0)) b.

   (* --- End automatically generated terms from DEVOID --- *)
 
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

    Definition __tree20 := ↑ Base.tree20.
    Definition _tree20 := ↑ (__tree20. .2).
    Definition tree20 := (↑ (_tree20 .2)).2.
    Definition __tree40 := ↑ Base.tree40.
    Definition _tree40 := ↑ (__tree40 .2).
    Definition tree40 := (↑ (_tree40 .2)).2.
    Definition __tree60 := ↑ Base.tree60.
    Definition _tree60 := ↑ (__tree60 .2).
    Definition tree60 := (↑ (_tree60 .2)).2.
    Definition __tree80 := ↑ Base.tree80.
    Definition _tree80 := ↑ (__tree80 .2).
    Definition tree80 := (↑ (_tree80 .2)).2.
    Definition __tree100 := ↑ Base.tree100.
    Definition _tree100 := ↑ (__tree100 .2).
    Definition tree100 := (↑ (_tree100 .2)).2.
    Definition __tree200 := ↑ Base.tree200.
    Definition _tree200 := ↑ (__tree200. .2).
    Definition tree200 := (↑ (_tree200 .2)).2.
    Definition __tree400 := ↑ Base.tree400.
    Definition _tree400 := ↑ (__tree400 .2).
    Definition tree400 := (↑ (_tree400 .2)).2.
    Definition __tree600 := ↑ Base.tree600.
    Definition _tree600 := ↑ (__tree600 .2).
    Definition tree600 := (↑ (_tree600 .2)).2.
    Definition __tree800 := ↑ Base.tree800.
    Definition _tree800 := ↑ (__tree800 .2).
    Definition tree800 := (↑ (_tree800 .2)).2.
    Definition __tree1000 := ↑ Base.tree1000.
    Definition _tree1000 := ↑ (__tree1000 .2).
    Definition tree1000 := (↑ (_tree1000 .2)).2.

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

    (* --- Let Coq warm up on each tree, so that base numbers aren't slower than they should be --- *)
    Redirect "../out/treeEFF20" Time Eval vm_compute in tree20.
    Redirect "../out/treeEFF40" Time Eval vm_compute in tree40.
    Redirect "../out/treeEFF60" Time Eval vm_compute in tree60.
    Redirect "../out/treeEFF80" Time Eval vm_compute in tree80.
    Redirect "../out/treeEFF100" Time Eval vm_compute in tree100.
    Redirect "../out/treeEFF200" Time Eval vm_compute in tree200.
    Redirect "../out/treeEFF400" Time Eval vm_compute in tree400.
    Redirect "../out/treeEFF600" Time Eval vm_compute in tree600.
    Redirect "../out/treeEFF800" Time Eval vm_compute in tree800.
    Redirect "../out/treeEFF1000" Time Eval vm_compute in tree1000.

    (* --- Base search data --- *)
    Redirect "../out/search/baseEFF20" Time Eval vm_compute in (search tree20 Elem.x).
    Redirect "../out/search/baseEFF40" Time Eval vm_compute in (search tree40 Elem.x).
    Redirect "../out/search/baseEFF60" Time Eval vm_compute in (search tree60 Elem.x).
    Redirect "../out/search/baseEFF80" Time Eval vm_compute in (search tree80 Elem.x).
    Redirect "../out/search/baseEFF100" Time Eval vm_compute in (search tree100 Elem.x).
    Redirect "../out/search/baseEFF200" Time Eval vm_compute in (search tree200 Elem.x).
    Redirect "../out/search/baseEFF400" Time Eval vm_compute in (search tree400 Elem.x).
    Redirect "../out/search/baseEFF600" Time Eval vm_compute in (search tree600 Elem.x).
    Redirect "../out/search/baseEFF800" Time Eval vm_compute in (search tree800 Elem.x).
    Redirect "../out/search/baseEFF1000" Time Eval vm_compute in (search tree1000 Elem.x).


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

    (* --- Begin automatically generated terms from DEVOID --- *)
    (* TODO copy in automatically *)

Definition _orn_balance_index := 
fun (t t0 : Elem.t) (b : bool) (b0 : Ordered.bst t t0 b) =>
Ordered.bst_rect
  (fun (t1 t2 : Elem.t) (b1 : bool) (_ : Ordered.bst t1 t2 b1) => nat)
  (fun (ord_l ord_r : bool) (min_l min_r max_l max_r _ : Elem.t)
     (left : Ordered.bst min_l max_l ord_l)
     (H : (fun (t1 t2 : Elem.t) (b1 : bool) (_ : Ordered.bst t1 t2 b1) => nat)
            min_l max_l ord_l left) (right : Ordered.bst min_r max_r ord_r)
     (H0 : (fun (t1 t2 : Elem.t) (b1 : bool) (_ : Ordered.bst t1 t2 b1) =>
            nat) min_r max_r ord_r right) => S (Nat.max H H0))
  (fun _ : Elem.t => 0) t t0 b b0.

Definition _orn_balance := 
fun (t t0 : Elem.t) (b : bool) (b0 : Ordered.bst t t0 b) =>
existT (fun H : nat => _avl t t0 b H) (_orn_balance_index t t0 b b0)
  (Ordered.bst_rect
     (fun (t1 t2 : Elem.t) (b1 : bool) (b2 : Ordered.bst t1 t2 b1) =>
      _avl t1 t2 b1 (_orn_balance_index t1 t2 b1 b2))
     (fun (ord_l ord_r : bool) (min_l min_r max_l max_r val : Elem.t)
        (left : Ordered.bst min_l max_l ord_l)
        (H : (fun (t1 t2 : Elem.t) (b1 : bool) (_ : nat)
                (b2 : Ordered.bst t1 t2 b1) =>
              _avl t1 t2 b1 (_orn_balance_index t1 t2 b1 b2)) min_l max_l
               ord_l (_orn_balance_index min_l max_l ord_l left) left)
        (right : Ordered.bst min_r max_r ord_r)
        (H0 : (fun (t1 t2 : Elem.t) (b1 : bool) (_ : nat)
                 (b2 : Ordered.bst t1 t2 b1) =>
               _avl t1 t2 b1 (_orn_balance_index t1 t2 b1 b2)) min_r max_r
                ord_r (_orn_balance_index min_r max_r ord_r right) right) =>
      _Branch (_orn_balance_index min_l max_l ord_l left)
        (_orn_balance_index min_r max_r ord_r right) ord_l ord_r min_l min_r
        max_l max_r val H H0) (fun val : Elem.t => _Leaf val) t t0 b b0).

Definition _orn_balance_inv := 
fun (t t0 : Elem.t) (b : bool) (_a : {H : nat & _avl t t0 b H}) =>
_avl_rect
  (fun (t1 t2 : Elem.t) (b0 : bool) (n : nat) (_ : _avl t1 t2 b0 n) =>
   Ordered.bst t1 t2 b0)
  (fun (h_l h_r : nat) (ord_l ord_r : bool)
     (min_l min_r max_l max_r val : Elem.t) (_ : _avl min_l max_l ord_l h_l)
     (H : Ordered.bst min_l max_l ord_l) (_ : _avl min_r max_r ord_r h_r)
     (H0 : Ordered.bst min_r max_r ord_r) =>
   Ordered.Branch ord_l ord_r min_l min_r max_l max_r val H H0)
  (fun val : Elem.t => Ordered.Leaf val) t t0 b _a .1 
  _a .2.

Definition _orn_balance_section := 
fun (t t0 : Elem.t) (b : bool) (b0 : Ordered.bst t t0 b) =>
eq_sym
  (Ordered.bst_rect
     (fun (t1 t2 : Elem.t) (b1 : bool) (b2 : Ordered.bst t1 t2 b1) =>
      b2 = _orn_balance_inv t1 t2 b1 (_orn_balance t1 t2 b1 b2))
     (fun (ord_l ord_r : bool) (min_l min_r max_l max_r val : Elem.t)
        (left : Ordered.bst min_l max_l ord_l)
        (H : left =
             _orn_balance_inv min_l max_l ord_l
               (_orn_balance min_l max_l ord_l left))
        (right : Ordered.bst min_r max_r ord_r)
        (H0 : right =
              _orn_balance_inv min_r max_r ord_r
                (_orn_balance min_r max_r ord_r right)) =>
      eq_ind left
        (fun H1 : Ordered.bst min_l max_l ord_l =>
         Ordered.Branch ord_l ord_r min_l min_r max_l max_r val left right =
         Ordered.Branch ord_l ord_r min_l min_r max_l max_r val H1
           (_orn_balance_inv min_r max_r ord_r
              (_orn_balance min_r max_r ord_r right)))
        (eq_ind right
           (fun H1 : Ordered.bst min_r max_r ord_r =>
            Ordered.Branch ord_l ord_r min_l min_r max_l max_r val left right =
            Ordered.Branch ord_l ord_r min_l min_r max_l max_r val left H1)
           eq_refl
           (_orn_balance_inv min_r max_r ord_r
              (_orn_balance min_r max_r ord_r right)) H0)
        (_orn_balance_inv min_l max_l ord_l
           (_orn_balance min_l max_l ord_l left)) H)
     (fun val : Elem.t => eq_refl) t t0 b b0).

Definition _orn_balance_retraction := 
fun (t t0 : Elem.t) (b : bool) (_a : {H : nat & _avl t t0 b H}) =>
sigT_rect
  (fun _a0 : {H : nat & _avl t t0 b H} =>
   _orn_balance t t0 b (_orn_balance_inv t t0 b _a0) = _a0)
  (fun (H : nat) (H0 : (fun H0 : nat => _avl t t0 b H0) H) =>
   eq_sym
     (_avl_rect
        (fun (t1 t2 : Elem.t) (b0 : bool) (n : nat) (_a0 : _avl t1 t2 b0 n)
         =>
         existT (fun H1 : nat => _avl t1 t2 b0 H1) n _a0 =
         _orn_balance t1 t2 b0
           (_orn_balance_inv t1 t2 b0
              (existT (fun H1 : nat => _avl t1 t2 b0 H1) n _a0)))
        (fun (h_l h_r : nat) (ord_l ord_r : bool)
           (min_l min_r max_l max_r val : Elem.t)
           (left : _avl min_l max_l ord_l h_l)
           (H1 : existT (fun H1 : nat => _avl min_l max_l ord_l H1) h_l left =
                 _orn_balance min_l max_l ord_l
                   (_orn_balance_inv min_l max_l ord_l
                      (existT (fun H1 : nat => _avl min_l max_l ord_l H1) h_l
                         left))) (right : _avl min_r max_r ord_r h_r)
           (H2 : existT (fun H2 : nat => _avl min_r max_r ord_r H2) h_r right =
                 _orn_balance min_r max_r ord_r
                   (_orn_balance_inv min_r max_r ord_r
                      (existT (fun H2 : nat => _avl min_r max_r ord_r H2) h_r
                         right))) =>
         eq_ind (existT (fun H3 : nat => _avl min_l max_l ord_l H3) h_l left)
           (fun H3 : {H3 : nat & _avl min_l max_l ord_l H3} =>
            existT
              (fun H4 : nat =>
               _avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) H4)
              (S (Nat.max h_l h_r))
              (_Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val left
                 right) =
            existT
              (fun H4 : nat =>
               _avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) H4)
              (S
                 (Nat.max H3 .1
                    (_orn_balance min_r max_r ord_r
                       (_orn_balance_inv min_r max_r ord_r
                          (existT (fun H4 : nat => _avl min_r max_r ord_r H4)
                             h_r right))) .1))
              (_Branch H3 .1
                 (_orn_balance min_r max_r ord_r
                    (_orn_balance_inv min_r max_r ord_r
                       (existT (fun H4 : nat => _avl min_r max_r ord_r H4)
                          h_r right))) .1 ord_l ord_r min_l min_r max_l max_r
                 val H3 .2
                 (_orn_balance min_r max_r ord_r
                    (_orn_balance_inv min_r max_r ord_r
                       (existT (fun H4 : nat => _avl min_r max_r ord_r H4)
                          h_r right))) .2))
           (eq_ind
              (existT (fun H3 : nat => _avl min_r max_r ord_r H3) h_r right)
              (fun H3 : {H3 : nat & _avl min_r max_r ord_r H3} =>
               existT
                 (fun H4 : nat =>
                  _avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r)
                    H4) (S (Nat.max h_l h_r))
                 (_Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val
                    left right) =
               existT
                 (fun H4 : nat =>
                  _avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r)
                    H4) (S (Nat.max h_l H3 .1))
                 (_Branch h_l H3 .1 ord_l ord_r min_l min_r max_l max_r val
                    left H3 .2)) eq_refl
              (existT (fun H3 : nat => _avl min_r max_r ord_r H3)
                 (_orn_balance min_r max_r ord_r
                    (_orn_balance_inv min_r max_r ord_r
                       (existT (fun H3 : nat => _avl min_r max_r ord_r H3)
                          h_r right))) .1
                 (_orn_balance min_r max_r ord_r
                    (_orn_balance_inv min_r max_r ord_r
                       (existT (fun H3 : nat => _avl min_r max_r ord_r H3)
                          h_r right))) .2) H2)
           (existT (fun H3 : nat => _avl min_l max_l ord_l H3)
              (_orn_balance min_l max_l ord_l
                 (_orn_balance_inv min_l max_l ord_l
                    (existT (fun H3 : nat => _avl min_l max_l ord_l H3) h_l
                       left))) .1
              (_orn_balance min_l max_l ord_l
                 (_orn_balance_inv min_l max_l ord_l
                    (existT (fun H3 : nat => _avl min_l max_l ord_l H3) h_l
                       left))) .2) H1) (fun val : Elem.t => eq_refl) t t0 b H
        H0)) _a.

Definition orn_balance_index := 
fun (t t0 : Elem.t) (b : bool) (n : nat) (_a : _avl t t0 b n) =>
_avl_rect
  (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) (_ : _avl t1 t2 b0 n0) => bool)
  (fun (h_l h_r : nat) (ord_l ord_r : bool)
     (min_l min_r max_l max_r _ : Elem.t) (left : _avl min_l max_l ord_l h_l)
     (H : (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) (_ : _avl t1 t2 b0 n0)
           => bool) min_l max_l ord_l h_l left)
     (right : _avl min_r max_r ord_r h_r)
     (H0 : (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat)
              (_ : _avl t1 t2 b0 n0) => bool) min_r max_r ord_r h_r right) =>
   inv H H0 h_l h_r) (fun _ : Elem.t => true) t t0 b n _a.

Definition orn_balance := 
fun (t t0 : Elem.t) (b : bool) (n : nat) (_a : _avl t t0 b n) =>
existT (fun H : bool => avl t t0 b n H) (orn_balance_index t t0 b n _a)
  (_avl_rect
     (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) (_a0 : _avl t1 t2 b0 n0) =>
      avl t1 t2 b0 n0 (orn_balance_index t1 t2 b0 n0 _a0))
     (fun (h_l h_r : nat) (ord_l ord_r : bool)
        (min_l min_r max_l max_r val : Elem.t)
        (left : _avl min_l max_l ord_l h_l)
        (H : (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) 
                (_ : bool) (_a0 : _avl t1 t2 b0 n0) =>
              avl t1 t2 b0 n0 (orn_balance_index t1 t2 b0 n0 _a0)) min_l
               max_l ord_l h_l (orn_balance_index min_l max_l ord_l h_l left)
               left) (right : _avl min_r max_r ord_r h_r)
        (H0 : (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) 
                 (_ : bool) (_a0 : _avl t1 t2 b0 n0) =>
               avl t1 t2 b0 n0 (orn_balance_index t1 t2 b0 n0 _a0)) min_r
                max_r ord_r h_r
                (orn_balance_index min_r max_r ord_r h_r right) right) =>
      Branch (orn_balance_index min_l max_l ord_l h_l left)
        (orn_balance_index min_r max_r ord_r h_r right) h_l h_r ord_l ord_r
        min_l min_r max_l max_r val H H0) (fun val : Elem.t => Leaf val) t t0
     b n _a).

Definition orn_balance_inv := 
fun (t t0 : Elem.t) (b : bool) (n : nat) (a : {H : bool & avl t t0 b n H}) =>
avl_rect
  (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) (b1 : bool)
     (_ : avl t1 t2 b0 n0 b1) => _avl t1 t2 b0 n0)
  (fun (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool)
     (min_l min_r max_l max_r val : Elem.t)
     (_ : avl min_l max_l ord_l h_l bal_l) (H : _avl min_l max_l ord_l h_l)
     (_ : avl min_r max_r ord_r h_r bal_r) (H0 : _avl min_r max_r ord_r h_r)
   => _Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val H H0)
  (fun val : Elem.t => _Leaf val) t t0 b n a .1 a .2.

Definition orn_balance_section := 
fun (t t0 : Elem.t) (b : bool) (n : nat) (_a : _avl t t0 b n) =>
eq_sym
  (_avl_rect
     (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) (_a0 : _avl t1 t2 b0 n0) =>
      _a0 = orn_balance_inv t1 t2 b0 n0 (orn_balance t1 t2 b0 n0 _a0))
     (fun (h_l h_r : nat) (ord_l ord_r : bool)
        (min_l min_r max_l max_r val : Elem.t)
        (left : _avl min_l max_l ord_l h_l)
        (H : left =
             orn_balance_inv min_l max_l ord_l h_l
               (orn_balance min_l max_l ord_l h_l left))
        (right : _avl min_r max_r ord_r h_r)
        (H0 : right =
              orn_balance_inv min_r max_r ord_r h_r
                (orn_balance min_r max_r ord_r h_r right)) =>
      eq_ind left
        (fun H1 : _avl min_l max_l ord_l h_l =>
         _Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val left right =
         _Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val H1
           (orn_balance_inv min_r max_r ord_r h_r
              (orn_balance min_r max_r ord_r h_r right)))
        (eq_ind right
           (fun H1 : _avl min_r max_r ord_r h_r =>
            _Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val left
              right =
            _Branch h_l h_r ord_l ord_r min_l min_r max_l max_r val left H1)
           eq_refl
           (orn_balance_inv min_r max_r ord_r h_r
              (orn_balance min_r max_r ord_r h_r right)) H0)
        (orn_balance_inv min_l max_l ord_l h_l
           (orn_balance min_l max_l ord_l h_l left)) H)
     (fun val : Elem.t => eq_refl) t t0 b n _a).

Definition orn_balance_retraction := 
fun (t t0 : Elem.t) (b : bool) (n : nat) (a : {H : bool & avl t t0 b n H}) =>
sigT_rect
  (fun a0 : {H : bool & avl t t0 b n H} =>
   orn_balance t t0 b n (orn_balance_inv t t0 b n a0) = a0)
  (fun (H : bool) (H0 : (fun H0 : bool => avl t t0 b n H0) H) =>
   eq_sym
     (avl_rect
        (fun (t1 t2 : Elem.t) (b0 : bool) (n0 : nat) 
           (b1 : bool) (a0 : avl t1 t2 b0 n0 b1) =>
         existT (fun H1 : bool => avl t1 t2 b0 n0 H1) b1 a0 =
         orn_balance t1 t2 b0 n0
           (orn_balance_inv t1 t2 b0 n0
              (existT (fun H1 : bool => avl t1 t2 b0 n0 H1) b1 a0)))
        (fun (bal_l bal_r : bool) (h_l h_r : nat) 
           (ord_l ord_r : bool) (min_l min_r max_l max_r val : Elem.t)
           (left : avl min_l max_l ord_l h_l bal_l)
           (H1 : existT (fun H1 : bool => avl min_l max_l ord_l h_l H1) bal_l
                   left =
                 orn_balance min_l max_l ord_l h_l
                   (orn_balance_inv min_l max_l ord_l h_l
                      (existT (fun H1 : bool => avl min_l max_l ord_l h_l H1)
                         bal_l left)))
           (right : avl min_r max_r ord_r h_r bal_r)
           (H2 : existT (fun H2 : bool => avl min_r max_r ord_r h_r H2) bal_r
                   right =
                 orn_balance min_r max_r ord_r h_r
                   (orn_balance_inv min_r max_r ord_r h_r
                      (existT (fun H2 : bool => avl min_r max_r ord_r h_r H2)
                         bal_r right))) =>
         eq_ind
           (existT (fun H3 : bool => avl min_l max_l ord_l h_l H3) bal_l left)
           (fun H3 : {H3 : bool & avl min_l max_l ord_l h_l H3} =>
            existT
              (fun H4 : bool =>
               avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r)
                 (S (Nat.max h_l h_r)) H4) (inv bal_l bal_r h_l h_r)
              (Branch bal_l bal_r h_l h_r ord_l ord_r min_l min_r max_l max_r
                 val left right) =
            existT
              (fun H4 : bool =>
               avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r)
                 (S (Nat.max h_l h_r)) H4)
              (inv H3 .1
                 (orn_balance min_r max_r ord_r h_r
                    (orn_balance_inv min_r max_r ord_r h_r
                       (existT
                          (fun H4 : bool => avl min_r max_r ord_r h_r H4)
                          bal_r right))) .1 h_l h_r)
              (Branch H3 .1
                 (orn_balance min_r max_r ord_r h_r
                    (orn_balance_inv min_r max_r ord_r h_r
                       (existT
                          (fun H4 : bool => avl min_r max_r ord_r h_r H4)
                          bal_r right))) .1 h_l h_r ord_l ord_r min_l min_r
                 max_l max_r val H3 .2
                 (orn_balance min_r max_r ord_r h_r
                    (orn_balance_inv min_r max_r ord_r h_r
                       (existT
                          (fun H4 : bool => avl min_r max_r ord_r h_r H4)
                          bal_r right))) .2))
           (eq_ind
              (existT (fun H3 : bool => avl min_r max_r ord_r h_r H3) bal_r
                 right)
              (fun H3 : {H3 : bool & avl min_r max_r ord_r h_r H3} =>
               existT
                 (fun H4 : bool =>
                  avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r)
                    (S (Nat.max h_l h_r)) H4) (inv bal_l bal_r h_l h_r)
                 (Branch bal_l bal_r h_l h_r ord_l ord_r min_l min_r max_l
                    max_r val left right) =
               existT
                 (fun H4 : bool =>
                  avl min_l max_r (Ordered.inv ord_l ord_r max_l val min_r)
                    (S (Nat.max h_l h_r)) H4) (inv bal_l H3 .1 h_l h_r)
                 (Branch bal_l H3 .1 h_l h_r ord_l ord_r min_l min_r max_l
                    max_r val left H3 .2)) eq_refl
              (existT (fun H3 : bool => avl min_r max_r ord_r h_r H3)
                 (orn_balance min_r max_r ord_r h_r
                    (orn_balance_inv min_r max_r ord_r h_r
                       (existT
                          (fun H3 : bool => avl min_r max_r ord_r h_r H3)
                          bal_r right))) .1
                 (orn_balance min_r max_r ord_r h_r
                    (orn_balance_inv min_r max_r ord_r h_r
                       (existT
                          (fun H3 : bool => avl min_r max_r ord_r h_r H3)
                          bal_r right))) .2) H2)
           (existT (fun H3 : bool => avl min_l max_l ord_l h_l H3)
              (orn_balance min_l max_l ord_l h_l
                 (orn_balance_inv min_l max_l ord_l h_l
                    (existT (fun H3 : bool => avl min_l max_l ord_l h_l H3)
                       bal_l left))) .1
              (orn_balance min_l max_l ord_l h_l
                 (orn_balance_inv min_l max_l ord_l h_l
                    (existT (fun H3 : bool => avl min_l max_l ord_l h_l H3)
                       bal_l left))) .2) H1) (fun val : Elem.t => eq_refl) t
        t0 b n H H0)) a.

    (* --- End automatically generated terms from DEVOID --- *)

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

    Definition _tree20 := ↑ Ordered.tree20.
    Definition tree20 := ↑ _tree20.2.
    Definition _tree40 := ↑ Ordered.tree40.
    Definition tree40 := ↑ _tree40.2.
    Definition _tree60 := ↑ Ordered.tree60.
    Definition tree60 := ↑ _tree60.2.
    Definition _tree80 := ↑ Ordered.tree80.
    Definition tree80 := ↑ _tree80.2.
    Definition _tree100 := ↑ Ordered.tree100.
    Definition tree100 := ↑ _tree100.2.
    Definition _tree200 := ↑ Ordered.tree200.
    Definition tree200 := ↑ _tree200.2.
    Definition _tree400 := ↑ Ordered.tree400.
    Definition tree400 := ↑ _tree400.2.
    Definition _tree600 := ↑ Ordered.tree600.
    Definition tree600 := ↑ _tree600.2.
    Definition _tree800 := ↑ Ordered.tree800.
    Definition tree800 := ↑ _tree800.2.
    Definition _tree1000 := ↑ Ordered.tree1000.
    Definition tree1000 := ↑ _tree1000.2.  

    Definition _preorder' lo hi ord : {n : nat & _avl lo hi ord n} -> list Elem.t :=
      ↑ (@Ordered.preorder lo hi ord).
    Definition _preorder lo hi ord n t := _preorder' lo hi ord (n; t).
    Definition preorder' {lo hi ord n} : {bal : bool & avl lo hi ord n bal} -> list Elem.t := 
      ↑ (_preorder lo hi ord n).
    Definition preorder {lo hi ord n bal} t := @preorder' lo hi ord n (bal; t).

    Redirect "../out/preorder/avlEFF20" Time Eval vm_compute in (preorder' tree20).
    Redirect "../out/preorder/avlEFF40" Time Eval vm_compute in (preorder' tree40).
    Redirect "../out/preorder/avlEFF60" Time Eval vm_compute in (preorder' tree60).
    Redirect "../out/preorder/avlEFF80" Time Eval vm_compute in (preorder' tree80).
    Redirect "../out/preorder/avlEFF100" Time Eval vm_compute in (preorder' tree100).
    Redirect "../out/preorder/avlEFF200" Time Eval vm_compute in (preorder' tree200).
    Redirect "../out/preorder/avlEFF400" Time Eval vm_compute in (preorder' tree400).
    Redirect "../out/preorder/avlEFF600" Time Eval vm_compute in (preorder' tree600).
    Redirect "../out/preorder/avlEFF800" Time Eval vm_compute in (preorder' tree800).
    Redirect "../out/preorder/avlEFF1000" Time Eval vm_compute in (preorder' tree1000).

    (* 105 LoC in normal form *)
    Definition inorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.inorder lo hi ord).
    Definition inorder {lo hi ord h bal} t := @inorder' lo hi ord (h; (bal; t)).
    Redirect "../out/inorder/avlEFF20" Time Eval vm_compute in (inorder' tree20).
    Redirect "../out/inorder/avlEFF40" Time Eval vm_compute in (inorder' tree40).
    Redirect "../out/inorder/avlEFF60" Time Eval vm_compute in (inorder' tree60).
    Redirect "../out/inorder/avlEFF80" Time Eval vm_compute in (inorder' tree80).
    Redirect "../out/inorder/avlEFF100" Time Eval vm_compute in (inorder' tree100).
    Redirect "../out/inorder/avlEFF200" Time Eval vm_compute in (inorder' tree200).
    Redirect "../out/inorder/avlEFF400" Time Eval vm_compute in (inorder' tree400).
    Redirect "../out/inorder/avlEFF600" Time Eval vm_compute in (inorder' tree600).
    Redirect "../out/inorder/avlEFF800" Time Eval vm_compute in (inorder' tree800).
    Redirect "../out/inorder/avlEFF1000" Time Eval vm_compute in (inorder' tree1000).

    (* 112 LoC in normal form *)
    Definition postorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.postorder lo hi ord).
    Definition postorder {lo hi ord h bal} t := @postorder' lo hi ord (h; (bal; t)).
    Redirect "../out/postorder/avlEFF20" Time Eval vm_compute in (postorder' tree20).
    Redirect "../out/postorder/avlEFF40" Time Eval vm_compute in (postorder' tree40).
    Redirect "../out/postorder/avlEFF60" Time Eval vm_compute in (postorder' tree60).
    Redirect "../out/postorder/avlEFF80" Time Eval vm_compute in (postorder' tree80).
    Redirect "../out/postorder/avlEFF100" Time Eval vm_compute in (postorder' tree100).
    Redirect "../out/postorder/avlEFF200" Time Eval vm_compute in (postorder' tree200).
    Redirect "../out/postorder/avlEFF400" Time Eval vm_compute in (postorder' tree400).
    Redirect "../out/postorder/avlEFF600" Time Eval vm_compute in (postorder' tree600).
    Redirect "../out/postorder/avlEFF800" Time Eval vm_compute in (postorder' tree800).
    Redirect "../out/postorder/avlEFF1000" Time Eval vm_compute in (postorder' tree1000).

    (* 105 LoC in normal form *)
    Definition search' {lo hi ord} : {h:nat & {bal:bool & avl lo hi ord h bal}} -> Elem.t -> bool :=
      ↑ (@Ordered.search lo hi ord).
    Definition search {lo hi ord h bal} (t : avl lo hi ord h bal) (x : Elem.t) : bool :=
      @search' lo hi ord (h; (bal; t)) x.
    Redirect "../out/search/avlEFF20" Time Eval vm_compute in (search' tree20 Elem.x).
    Redirect "../out/search/avlEFF40" Time Eval vm_compute in (search' tree40 Elem.x).
    Redirect "../out/search/avlEFF60" Time Eval vm_compute in (search' tree60 Elem.x).
    Redirect "../out/search/avlEFF80" Time Eval vm_compute in (search' tree80 Elem.x).
    Redirect "../out/search/avlEFF100" Time Eval vm_compute in (search' tree100 Elem.x).
    Redirect "../out/search/avlEFF200" Time Eval vm_compute in (search' tree200 Elem.x).
    Redirect "../out/search/avlEFF400" Time Eval vm_compute in (search' tree400 Elem.x).
    Redirect "../out/search/avlEFF600" Time Eval vm_compute in (search' tree600 Elem.x).
    Redirect "../out/search/avlEFF800" Time Eval vm_compute in (search' tree800 Elem.x).
    Redirect "../out/search/avlEFF1000" Time Eval vm_compute in (search' tree1000 Elem.x).

    (* --- Normalized term sizes --- *)
    Redirect "../out/normalized/preorder-avlEFF" Eval compute in preorder'.
    Redirect "../out/normalized/postorder-avlEFF" Eval compute in postorder'.
    Redirect "../out/normalized/inorder-avlEFF" Eval compute in inorder'.
    Redirect "../out/normalized/search-avlEFF" Eval compute in search'.

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

      (* TIME-MEDIUM inorder-avl *)
      (* TIME-MEDIUM postorder-avl *)
      (* TIME-MEDIUM preorder-avl *)
      (* TIME-MEDIUM search-avl *)

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
