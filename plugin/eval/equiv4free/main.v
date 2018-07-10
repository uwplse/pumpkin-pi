Require Import HoTT Tactics UR URTactics FP Record MoreInductive.
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

(** To get ten measurements of a function's run-time, process a sequence of Vernacular commands
    like the example below and then use the following shell command to get the list of
    corresponding millisecond (wall-clock) times:
    $ tail -n 2 tmp*.out | grep -o -e '[0-9.]* secs' | sed -f times.sed
 **)

(* Redirect "tmp0" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp1" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp2" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp3" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp4" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp5" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp6" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp7" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp8" Time Eval vm_compute in preorder tree10000. *)
(* Redirect "tmp9" Time Eval vm_compute in preorder tree10000. *)


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

    Section Inputs.
      Local Coercion Leaf : Elem.t >-> tree.
      Local Notation x := Elem.x.
      Local Notation y := Elem.y.
      Local Notation z := Elem.z.

      (* 21 nodes, to be exact *)
      Definition tree20 :=
        Branch x
               (Branch y (Branch z (Branch x y z) (Branch x y z)) (Branch x y z))
               (Branch z (Branch x y z) (Branch x y (Branch x y z))).

      (* 43 nodes, to be exact *)
      Definition tree40 :=
        Branch z tree20 tree20.

      (* 65 nodes, to be exact *)
      Definition tree60 :=
        Branch y tree20 tree40.

      (* 87 nodes, to be exact *)
      Definition tree80 :=
        Branch x tree40 tree40.

      (* 109 nodes, to be exact *)
      Definition tree100 :=
        Branch y tree40 tree60.

      (* 219 nodes, to be exact *)
      Definition tree200 :=
        Branch x tree100 tree100.

      (* 439 nodes, to be exact *)
      Definition tree400 :=
        Branch y tree200 tree200.

      (* 659 nodes, to be exact *)
      Definition tree600 :=
        Branch x tree200 tree400.

      (* 879 nodes, to be exact *)
      Definition tree800 :=
        Branch z tree200 tree600.

      (* 1099 nodes, to be exact *)
      Definition tree1000 :=
        Branch x tree400 tree600.

      (* 2101 nodes, to be exact *)
      Definition tree2000 :=
        Branch y (Branch z tree200 tree800) tree1000.

      (* 4203 nodes, to be exact *)
      Definition tree4000 :=
        Branch x tree2000 tree2000.

      (* 6305 nodes, to be exact *)
      Definition tree6000 :=
        Branch z tree2000 tree4000.

      (* 8407 nodes, to be exact *)
      Definition tree8000 :=
        Branch z tree4000 tree4000.

      (* 10509 nodes, to be exact *)
      Definition tree10000 :=
        Branch z tree2000 tree8000.
    End Inputs.

    (* 13 LoC in normal form *)
    Definition preorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => [x] ++ ys ++ zs)
        (fun x => [x])
        t.
    Time Eval vm_compute in (preorder tree2000).
    (* 15ms 16ms 32ms 15ms 18ms 16ms 13ms 19ms 15ms 14ms *)
    Time Eval vm_compute in (preorder tree4000).
    (* 47ms 35ms 46ms 34ms 37ms 37ms 34ms 34ms 41ms 35ms *)
    Time Eval vm_compute in (preorder tree6000).
    (* 50ms 67ms 57ms 72ms 54ms 71ms 55ms 62ms 56ms 71ms *)
    Time Eval vm_compute in (preorder tree8000).
    (* 72ms 81ms 71ms 97ms 81ms 70ms 100ms 72ms 88ms 70ms *)
    Time Eval vm_compute in (preorder tree10000).
    (* 96ms 107ms 91ms 98ms 97ms 96ms 110ms 86ms 86ms 87ms *)

    (* 12 LoC in normal form *)
    Definition inorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ [x] ++ zs)
        (fun x => [x])
        t.
    Time Eval vm_compute in (inorder tree2000).
    (* 15ms 16ms 15ms 15ms 15ms 15ms 15ms 24ms 15ms 14ms *)
    Time Eval vm_compute in (inorder tree4000).
    (* 38ms 31ms 36ms 34ms 33ms 38ms 34ms 33ms 38ms 33ms *)
    Time Eval vm_compute in (inorder tree6000).
    (* 50ms 49ms 52ms 58ms 52ms 58ms 53ms 58ms 52ms 59ms *)
    Time Eval vm_compute in (inorder tree8000).
    (* 76ms 63ms 69ms 70ms 62ms 66ms 59ms 62ms 70ms 62ms *)
    Time Eval vm_compute in (inorder tree10000).
    (* 93ms 77ms 87ms 80ms 86ms 84ms 92ms 97ms 97ms 85ms *)

    (* 12 LoC in normal form *)
    Definition postorder (t : tree) : list Elem.t :=
      tree_rect
        (fun _ => list Elem.t)
        (fun x _ ys _ zs => ys ++ zs ++ [x])
        (fun x => [x])
        t.
    Time Eval vm_compute in (postorder tree2000).
    (* 15ms 26ms 15ms 15ms 19ms 20ms 17ms 20ms 15ms 15ms *)
    Time Eval vm_compute in (postorder tree4000).
    (* 31ms 34ms 34ms 34ms 33ms 35ms 34ms 41ms 34ms 34ms *)
    Time Eval vm_compute in (postorder tree6000).
    (* 55ms 59ms 59ms 57ms 54ms 57ms 57ms 54ms 69ms 53ms *)
    Time Eval vm_compute in (postorder tree8000).
    (* 69ms 72ms 80ms 68ms 75ms 81ms 86ms 70ms 94ms 69ms *)
    Time Eval vm_compute in (postorder tree10000).
    (* 98ms 107ms 95ms 96ms 100ms 92ms 84ms 93ms 78ms 84ms *)

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
    Time Eval vm_compute in (preorder' tree2000).
    (* 30ms 31ms 32ms 26ms 27ms 29ms 37ms 27ms 28ms 27ms *)
    Time Eval vm_compute in (preorder' tree4000).
    (* 72ms 62ms 61ms 61ms 69ms 62ms 64ms 62ms 64ms 64ms *)
    Time Eval vm_compute in (preorder' tree6000).
    (* 102ms 87ms 81ms 86ms 82ms 87ms 79ms 87ms 82ms 83ms *)
    Time Eval vm_compute in (preorder' tree8000).
    (* 124ms 110ms 111ms 116ms 110ms 114ms 113ms 129ms 120ms 102ms *)
    Time Eval vm_compute in (preorder' tree10000).
    (* 152ms 146ms 143ms 141ms 158ms 152ms 143ms 137ms 151ms 150ms *)

    (* 37 LoC in normal form *)
    Definition inorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.inorder.
    Definition inorder n t := inorder' (existT _ n t).
    Time Eval vm_compute in (inorder' tree2000).
    (* 28ms 28ms 34ms 30ms 31ms 28ms 27ms 23ms 30ms 30ms *)
    Time Eval vm_compute in (inorder' tree4000).
    (* 55ms 64ms 61ms 62ms 68ms 62ms 68ms 62ms 71ms 62ms *)
    Time Eval vm_compute in (inorder' tree6000).
    (* 84ms 86ms 88ms 88ms 96ms 94ms 86ms 91ms 96ms 85ms *)
    Time Eval vm_compute in (inorder' tree8000).
    (* 115ms 115ms 120ms 116ms 134ms 110ms 115ms 121ms 142ms 123ms *)
    Time Eval vm_compute in (inorder' tree10000).
    (* 152ms 152ms 144ms 143ms 200ms 149ms 139ms 141ms 152ms 149ms *)

    (* 43 LoC in normal form *)
    Definition postorder' : {n:nat & tree n} -> list Elem.t := ↑ Base.postorder.
    Definition postorder n t := postorder' (existT _ n t).
    Time Eval vm_compute in (postorder' tree2000).
    (* 32ms 28ms 30ms 30ms 25ms 30ms 28ms 31ms 31ms 31ms *)
    Time Eval vm_compute in (postorder' tree4000).
    (* 68ms 67ms 65ms 74ms 70ms 70ms 68ms 68ms 66ms 70ms *)
    Time Eval vm_compute in (postorder' tree6000).
    (* 85ms 93ms 93ms 105ms 99ms 97ms 96ms 92ms 91ms 103ms *)
    Time Eval vm_compute in (postorder' tree8000).
    (* 115ms 117ms 123ms 116ms 118ms 124ms 112ms 112ms 123ms 123ms *)
    Time Eval vm_compute in (postorder' tree10000).
    (* 139ms 142ms 158ms 144ms 169ms 156ms 147ms 145ms 147ms 147ms *)

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

    Section Comparison.
      (* 25 LoC in normal form *)
      Definition preorder'' : forall t : {H : nat & tree H},
        (fun (n : nat) (_ : tree n) => list Elem.t) (t .1) (t .2) :=
        fun t : {H : nat & tree H} =>
          tree_rect (fun (n : nat) (_ : tree n) => list Elem.t)
                    (fun (n_l n_r : nat) (val : Elem.t) (_ : tree n_l)
                         (H : list Elem.t) (_ : tree n_r) (H0 : list Elem.t) =>
                       [val] ++ H ++ H0) (fun val : Elem.t => [val])
                    (t .1) (t .2).
      Time Eval vm_compute in (preorder'' tree2000).
      (* 15ms 16ms 16ms 14ms 14ms 19ms 14ms 14ms 14ms 18ms *)
      Time Eval vm_compute in (preorder'' tree4000).
      (* 40ms 32ms 35ms 34ms 37ms 34ms 38ms 35ms 30ms 46ms *)
      Time Eval vm_compute in (preorder'' tree6000).
      (* 45ms 45ms 68ms 57ms 76ms 55ms 65ms 55ms 68ms 55ms *)
      Time Eval vm_compute in (preorder'' tree8000).
      (* 69ms 69ms 79ms 82ms 69ms 90ms 89ms 71ms 104ms 84ms *)
      Time Eval vm_compute in (preorder'' tree10000).
      (* 89ms 97ms 90ms 98ms 84ms 87ms 89ms 99ms 102ms 98ms *)

      (* 24 LoC in normal form *)
      Definition inorder'' : forall t : {H : nat & tree H},
          (fun (n : nat) (_ : tree n) => list Elem.t) (t .1) (t .2) :=
        fun t : {H : nat & tree H} =>
          tree_rect (fun (n : nat) (_ : tree n) => list Elem.t)
                    (fun (n_l n_r : nat) (val : Elem.t) (_ : tree n_l)
                         (H : list Elem.t) (_ : tree n_r) (H0 : list Elem.t) =>
                       H ++ [val] ++ H0) (fun val : Elem.t => [val])
                    (t .1) (t .2).
      Time Eval vm_compute in (inorder'' tree2000).
      (* 15ms 15ms 14ms 15ms 15ms 13ms 14ms 14ms 14ms 22ms *)
      Time Eval vm_compute in (inorder'' tree4000).
      (* 30ms 29ms 30ms 35ms 35ms 34ms 31ms 34ms 36ms 36ms *)
      Time Eval vm_compute in (inorder'' tree6000).
      (* 58ms 44ms 57ms 55ms 52ms 62ms 53ms 59ms 53ms 60ms *)
      Time Eval vm_compute in (inorder'' tree8000).
      (* 65ms 63ms 71ms 79ms 74ms 69ms 56ms 69ms 68ms 75ms *)
      Time Eval vm_compute in (inorder'' tree10000).
      (* 85ms 79ms 98ms 86ms 101ms 91ms 98ms 82ms 91ms 92ms *)

      (* 31 LoC in normal form *)
      Definition postorder'' : forall t : {H : nat & tree H},
          (fun (n : nat) (_ : tree n) => list Elem.t) (t .1) (t .2) :=
        fun t : {H : nat & tree H} =>
          tree_rect (fun (n : nat) (_ : tree n) => list Elem.t)
                    (fun (n_l n_r : nat) (val : Elem.t) (_ : tree n_l)
                         (H : list Elem.t) (_ : tree n_r) (H0 : list Elem.t) =>
                       H ++ H0 ++ [val]) (fun val : Elem.t => [val])
                    (t .1) (t .2).
      Time Eval vm_compute in (postorder'' tree2000).
      (* 14ms 15ms 21ms 14ms 15ms 13ms 15ms 15ms 18ms 15ms *)
      Time Eval vm_compute in (postorder'' tree4000).
      (* 28ms 31ms 36ms 33ms 34ms 40ms 37ms 35ms 38ms 30ms *)
      Time Eval vm_compute in (postorder'' tree6000).
      (* 53ms 66ms 56ms 62ms 53ms 61ms 54ms 61ms 53ms 56ms *)
      Time Eval vm_compute in (postorder'' tree8000).
      (* 64ms 66ms 68ms 75ms 72ms 75ms 68ms 75ms 81ms 69ms *)
      Time Eval vm_compute in (postorder'' tree10000).
      (* 83ms 86ms 84ms 90ms 100ms 99ms 107ms 100ms 116ms 84ms *)
    End Comparison.

  End Sized.

  Module Measured.

    Inductive tree : nat -> Type :=
    | Branch (h_l h_r : nat)
             (val : Elem.t)
             (left : tree h_l) (right : tree h_r)
      : tree (S (Nat.max h_l h_r))
    | Leaf (val : Elem.t) : tree O.

    Instance Equiv_tree (h h' : nat) (E : h = h') : tree h ≃ tree h'.
    Proof. apply can_eq in E; try tc. rewrite <- E. apply Equiv_id. Defined.

    Lemma Equiv_tree_id h : Equiv_tree h h eq_refl = Equiv_id (tree h).
    Proof. unfold Equiv_tree. rewrite can_eq_refl. reflexivity. Defined.

    Instance UR_tree (h h' : nat) (E : h = h') : UR (tree h) (tree h').
    Proof. rewrite <- E. apply UR_gen. Defined.

    Instance Transportable_tree : Transportable tree.
    Proof. econstructor. intros h. rewrite Equiv_tree_id. reflexivity. Defined.

    Definition FP_tree : tree ≈ tree.
    Proof.
      cbn. split; try tc. cbn. intros h h' E. apply can_eq in E; try tc.
      rewrite <- E. esplit; try apply Canonical_eq_gen.
      econstructor. cbn. intros t t'. unfold univalent_transport.
      rewrite Equiv_tree_id. cbn. tc.
    Defined.

    Fixpoint orn_height (t : Base.tree) : sigT (fun h => tree h) :=
      match t with
      | Base.Branch v l r =>
        let L := orn_height l in
        let R := orn_height r in
        (_; (Branch L.1 R.1 v L.2 R.2))
      | Base.Leaf v => (_; Leaf v)
      end.

    Fixpoint orn_height_inv' (h : nat) (t : tree h) : Base.tree :=
      match t with
        | Branch h_l h_r v l r =>
          Base.Branch v (orn_height_inv' h_l l) (orn_height_inv' h_r r)
        | Leaf v => Base.Leaf v
      end.

    Definition orn_height_inv (T : {h : nat & tree h}) : Base.tree :=
      orn_height_inv' T.1 T.2.

    Instance IsEquiv_orn_height : IsEquiv orn_height.
    Proof.
      eapply isequiv_adjointify with (g := orn_height_inv); unfold orn_height_inv.
      - intros t. induction t as [v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
      - intros [h t]. cbn. induction t as [h_l h_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
    Defined.

    Instance Equiv_orn_height : Base.tree ≃ {h:nat & tree h} :=
      BuildEquiv _ _ _ IsEquiv_orn_height.

    Instance UR_orn_height : Base.tree ⋈ {h:nat & tree h}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (orn_height t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ Equiv_orn_height).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Definition tree20 := ↑ Base.tree20.
    Definition tree40 := ↑ Base.tree40.
    Definition tree60 := ↑ Base.tree60.
    Definition tree80 := ↑ Base.tree80.
    Definition tree100 := ↑ Base.tree100.

    Definition preorder' : {h:nat & tree h} -> list Elem.t := ↑ Base.preorder.
    Definition preorder h t := preorder' (existT _ h t).

    Definition inorder' : {h:nat & tree h} -> list Elem.t := ↑ Base.inorder.
    Definition inorder h t := inorder' (existT _ h t).

    Definition postorder' : {h:nat & tree h} -> list Elem.t := ↑ Base.postorder.
    Definition postorder h t := postorder' (existT _ h t).

    Definition mirror' : {h:nat & tree h} -> {h:nat & tree h} := ↑ Base.mirror.
    Definition mirror (h : nat) (t : tree h) : tree h.
      set (T := (mirror' (existT _ h t))). replace h with (T.1). exact (T.2).
      subst T. induction t as [h_l h_r v t_l IH_l t_r IH_r|v]; [|reflexivity].
      cbn in *. rewrite IH_l, IH_r. rewrite max_comm. reflexivity.
    Defined.

  End Measured.

  Module Heaped.

    Definition inv h_l h_r min_l min_r inv_l inv_r val : bool :=
      inv_l && inv_r && Nat.eqb h_l h_r && Elem.ltb min_l val && Elem.ltb min_r val.

    Inductive minheap : nat -> Elem.t -> bool -> Type :=
    | Branch (inv_l inv_r : bool) (min_l min_r : Elem.t) (h_l h_r : nat)
             (val : Elem.t)
             (left : minheap h_l min_l inv_l) (right : minheap h_r min_r inv_r)
      : minheap (S (Nat.max h_l h_r)) val (inv h_l h_r min_l min_r inv_l inv_r val)
    | Leaf (val : Elem.t) : minheap O val true.

    Instance Equiv_minheap (h h' : nat) (E_h : h = h') (x x' : Elem.t) (E_x : x = x') (b b' : bool) (E_b : b = b') :
      minheap h x b ≃ minheap h' x' b'.
    Proof.
      apply can_eq in E_h; try tc. apply can_eq in E_x; try tc. apply can_eq in E_b; try tc.
      rewrite <- E_h, <- E_x, <- E_b. apply Equiv_id.
    Defined.

    Lemma Equiv_minheap_id h x b : Equiv_minheap h h eq_refl x x eq_refl b b eq_refl = Equiv_id (minheap h x b).
    Proof. unfold Equiv_minheap. repeat rewrite can_eq_refl. reflexivity. Defined.

    Instance UR_minheap (h h' : nat) (E_h : h = h') (x x' : Elem.t) (E_x : x = x') (b b' : bool) (E_b : b = b') :
      UR (minheap h x b) (minheap h' x' b').
    Proof. rewrite <- E_h, <- E_x, <- E_b. apply UR_gen. Defined.

    Instance Transportable_minheap h x : Transportable (minheap h x).
    Proof. econstructor. intros b. rewrite Equiv_minheap_id. reflexivity. Defined.

    Definition FP_minheap : minheap ≈ minheap.
    Proof.
      cbn. intros h h' E_h x x' E_x. split; try tc. cbn. intros b b' E_b.
      apply can_eq in E_h; try tc. apply can_eq in E_x; try tc. apply can_eq in E_b; try tc.
      rewrite <- E_h, <- E_x, <- E_b. esplit; try apply Canonical_eq_gen.
      econstructor. cbn. intros t t'. unfold univalent_transport.
      rewrite Equiv_minheap_id. cbn. tc.
    Defined.

    Fixpoint orn_heap {h : nat} (t : Measured.tree h) : {min:Elem.t & {inv:bool & minheap h min inv}} :=
      match t with
      | Measured.Branch h_l h_r v l r =>
        (_; (_; Branch _ _ _ _ h_l h_r v (orn_heap l).2.2 (orn_heap r).2.2))
      | Measured.Leaf v =>
        (_; (_; Leaf v))
      end.

    Fixpoint orn_heap_inv' {h : nat} {min : Elem.t} {inv : bool} (t : minheap h min inv) : Measured.tree h :=
      match t with
      | Branch _ _ _ _ _ _ v l r =>
        Measured.Branch _ _ v (orn_heap_inv' l) (orn_heap_inv' r)
      | Leaf v =>
        Measured.Leaf v
      end.

    Definition orn_heap_inv {h : nat} (T : {min:Elem.t & {inv:bool & minheap h min inv}}) : Measured.tree h :=
      orn_heap_inv' T.2.2.

    Instance IsEquiv_orn_heap (h : nat) : IsEquiv (@orn_heap h).
    Proof.
      eapply isequiv_adjointify with (g := orn_heap_inv); unfold orn_heap_inv; cbn.
      - intros t. induction t as [h_l h_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
      - intros [min [inv t]]. cbn. induction t as [inv_l inv_r min_l min_r h_l h_r v l IH_l r IH_r|v]; cbn.
        + rewrite IH_l, IH_r. reflexivity.
        + reflexivity.
    Defined.

    Instance Equiv_orn_heap (h : nat) : Measured.tree h ≃ {min:Elem.t & {inv:bool & minheap h min inv}} :=
      BuildEquiv _ _ _ (IsEquiv_orn_heap h).

    Instance UR_orn_heap (h : nat) : Measured.tree h ⋈ {min:Elem.t & {inv:bool & minheap h min inv}}.
    Proof.
      cbn. unshelve esplit.
      - econstructor. intros t t'. exact (orn_heap t = t').
      - econstructor. intros t t'. cbn.
        apply (@isequiv_ap _ _ (Equiv_orn_heap h)).
      - apply Canonical_eq_gen.
      - apply Canonical_eq_gen.
    Defined.

    Definition tree20 := ↑ Measured.tree20.
    Definition tree40 := ↑ Measured.tree40.
    Definition tree60 := ↑ Measured.tree60.
    Definition tree80 := ↑ Measured.tree80.
    Definition tree100 := ↑ Measured.tree100.

    (* 92 LoC in normal form *)
    Definition preorder' (h : nat) : {min:Elem.t & {inv:bool & minheap h min inv}} -> list Elem.t := ↑ (Measured.preorder h).
    Definition preorder h min inv t := preorder' h (min; (inv; t)).

    (* 91 LoC in normal form *)
    Definition inorder' (h : nat) : {min:Elem.t & {inv:bool & minheap h min inv}} -> list Elem.t := ↑ (Measured.inorder h).
    Definition inorder h min inv t := inorder' h (min; (inv; t)).

    (* 98 LoC in normal form *)
    Definition postorder' (h : nat) : {min:Elem.t & {inv:bool & minheap h min inv}} -> list Elem.t := ↑ (Measured.postorder h).
    Definition postorder h min inv t := postorder' h (min; (inv; t)).

    Section Comparison.
      Definition preorder'' : forall (h : nat) (min : Elem.t)
                                    (t : {inv:bool & minheap h min inv}), list Elem.t :=
        fun (h : nat) (min : Elem.t) (t : {H : bool & minheap h min H}) =>
          minheap_rect
            (fun (n : nat) (t0 : Elem.t) (b : bool) (_ : minheap n t0 b) =>
               list Elem.t)
            (fun (inv_l inv_r : bool) (min_l min_r : Elem.t)
                 (h_l h_r : nat) (val : Elem.t) (_ : minheap h_l min_l inv_l)
                 (H : list Elem.t) (_ : minheap h_r min_r inv_r)
                 (H0 : list Elem.t) => [val] ++ H ++ H0)
            (fun val : Elem.t => [val]) h min (t .1) (t .2).

      Definition inorder'' : forall (h : nat) (min : Elem.t)
                                   (t : {inv:bool & minheap h min inv}), list Elem.t :=
        fun (h : nat) (min : Elem.t) (t : {H : bool & minheap h min H}) =>
          minheap_rect
            (fun (n : nat) (t0 : Elem.t) (b : bool) (_ : minheap n t0 b) =>
               list Elem.t)
            (fun (inv_l inv_r : bool) (min_l min_r : Elem.t)
                 (h_l h_r : nat) (val : Elem.t) (_ : minheap h_l min_l inv_l)
                 (H : list Elem.t) (_ : minheap h_r min_r inv_r)
                 (H0 : list Elem.t) => H ++ [val] ++ H0)
            (fun val : Elem.t => [val]) h min (t .1) (t .2).

      Definition postorder'' : forall (h : nat) (min : Elem.t)
                                     (t : {inv:bool & minheap h min inv}), list Elem.t :=
        fun (h : nat) (min : Elem.t) (t : {H : bool & minheap h min H}) =>
          minheap_rect
            (fun (n : nat) (t0 : Elem.t) (b : bool) (_ : minheap n t0 b) =>
               list Elem.t)
            (fun (inv_l inv_r : bool) (min_l min_r : Elem.t)
                 (h_l h_r : nat) (val : Elem.t) (_ : minheap h_l min_l inv_l)
                 (H : list Elem.t) (_ : minheap h_r min_r inv_r)
                 (H0 : list Elem.t) => H ++ H0 ++ [val])
            (fun val : Elem.t => [val]) h min (t .1) (t .2).
    End Comparison.
  End Heaped.

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
    Time Eval vm_compute in (search tree20.2.2.2 Elem.x).
    (* 9ms 7ms 6ms 8ms 6ms 7ms 4ms 4ms 4ms 6ms *)
    Time Eval vm_compute in (search tree40.2.2.2 Elem.x).
    (* 33ms 34ms 7ms 9ms 9ms 8ms 8ms 5ms 5ms 6ms *)
    Time Eval vm_compute in (search tree60.2.2.2 Elem.x).
    (* 204ms 197ms 7ms 7ms 8ms 7ms 10ms 7ms 10ms 7ms *)
    Time Eval vm_compute in (search tree80.2.2.2 Elem.x).
    (* 353ms 337ms 11ms 11ms 12ms 8ms 10ms 11ms 10ms 11ms *)
    Time Eval vm_compute in (search tree100.2.2.2 Elem.x).
    (* 1419ms 1452ms 12ms 14ms 10ms 16ms 16ms 12ms 11ms 15ms *)

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
    Time Eval vm_compute in (preorder' tree20).
    (* 53ms 67ms 45ms 44ms 40ms 43ms 47ms 45ms 44ms 41ms *)
    Time Eval vm_compute in (preorder' tree40).
    (* 445ms 457ms 432ms 430ms 417ms 429ms 403ms 427ms 427ms 413ms *)
    Time Eval vm_compute in (preorder' tree60).
    (* 3069ms 3062ms 2846ms 2811ms 2860ms 2848ms 2820ms 2815ms 2868ms 2907ms *)
    Time Eval vm_compute in (preorder' tree80).
    (* 5650ms 5674ms 5184ms 5678ms 5212ms 5240ms 5185ms 5206ms 5164ms 5253ms *)
    Time Eval vm_compute in (preorder' tree100).
    (* 23739ms 22200ms 21091ms 22529ms 22256ms 21026ms 22323ms 22664ms 21666ms 21270ms *)

    (* 105 LoC in normal form *)
    Definition inorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.inorder lo hi ord).
    Definition inorder {lo hi ord h bal} t := @inorder' lo hi ord (h; (bal; t)).
    Time Eval vm_compute in (inorder' tree20).
    (* 41ms 37ms 37ms 38ms 37ms 45ms 36ms 46ms 41ms 36ms *)
    Time Eval vm_compute in (inorder' tree40).
    (* 403ms 412ms 424ms 411ms 417ms 413ms 414ms 427ms 420ms 411ms *)
    Time Eval vm_compute in (inorder' tree60).
    (* 2875ms 2766ms 2913ms 2866ms 2839ms 2779ms 2919ms 2872ms 2912ms 2898ms *)
    Time Eval vm_compute in (inorder' tree80).
    (* 5500ms 5243ms 5139ms 6225ms 5391ms 5343ms 5946ms 5655ms 5775ms 5154ms *)
    Time Eval vm_compute in (inorder' tree100).
    (* 21461ms 22779ms 23054ms 21085ms 24090ms 24499ms 22729ms 21036ms 24405ms 23986ms *)

    (* 112 LoC in normal form *)
    Definition postorder' {lo hi ord} : avl_sig lo hi ord -> list Elem.t :=
      ↑ (@Ordered.postorder lo hi ord).
    Definition postorder {lo hi ord h bal} t := @postorder' lo hi ord (h; (bal; t)).
    Time Eval vm_compute in (postorder' tree20).
    (* 36ms 37ms 36ms 35ms 38ms 36ms 36ms 36ms 37ms 34ms *)
    Time Eval vm_compute in (postorder' tree40).
    (* 407ms 400ms 398ms 399ms 500ms 477ms 477ms 462ms 398ms 396ms *)
    Time Eval vm_compute in (postorder' tree60).
    (* 3090ms 2803ms 3184ms 3113ms 3103ms 3081ms 3209ms 3104ms 3065ms 3097ms *)
    Time Eval vm_compute in (postorder' tree80).
    (* 5229ms 5267ms 5281ms 5213ms 5825ms 5214ms 5121ms 5674ms 5614ms 5685ms *)
    Time Eval vm_compute in (postorder' tree100).
    (* 21669ms 23444ms 22625ms 22099ms 22461ms 23224ms 22970ms 23721ms 23467ms 23003ms *)

    (* 105 LoC in normal form *)
    Definition search' {lo hi ord} : {h:nat & {bal:bool & avl lo hi ord h bal}} -> Elem.t -> bool :=
      ↑ (@Ordered.search lo hi ord).
    Definition search {lo hi ord h bal} (t : avl lo hi ord h bal) (x : Elem.t) : bool :=
      @search' lo hi ord (h; (bal; t)) x.
    Time Eval vm_compute in (search' tree20 Elem.x).
    (* 16ms 17ms 15ms 16ms 16ms 16ms 15ms 15ms 15ms 16ms *)
    Time Eval vm_compute in (search' tree40 Elem.x).
    (* 131ms 130ms 125ms 121ms 128ms 126ms 131ms 134ms 128ms *)
    Time Eval vm_compute in (search' tree60 Elem.x).
    (* 803ms 752ms 749ms 735ms 732ms 731ms 746ms 744ms 735ms 741ms *)
    Time Eval vm_compute in (search' tree80 Elem.x).
    (* 1431ms 1455ms 1353ms 1360ms 1440ms 1349ms 1347ms 1365ms 1381ms 1350ms *)
    Time Eval vm_compute in (search' tree100 Elem.x).
    (* 5444ms 5358ms 5246ms 5721ms 6077ms 5901ms 5959ms 5460ms 5404ms 5446ms *)

    Section Comparison.
      Definition preorder'' {min max : Elem.t} {ord : bool} {height : nat}
                 (tree : {bal:bool & avl min max ord height bal}) : list Elem.t :=
          avl_rect
            (fun (t t0 : Elem.t) (b : bool) (n : nat) (b0 : bool)
                 (_ : avl t t0 b n b0) => list Elem.t)
            (fun (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool)
                 (min_l min_r max_l max_r val : Elem.t)
                 (_ : avl min_l max_l ord_l h_l bal_l)
                 (H : list Elem.t) (_ : avl min_r max_r ord_r h_r bal_r)
                 (H0 : list Elem.t) => [val] ++ H ++ H0)
            (fun val : Elem.t => [val]) min max ord height
            (tree .1) (tree .2).

      Time Eval vm_compute in (preorder'' tree20.2).
      (* 2ms 2ms 1ms 2ms 2ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (preorder'' tree40.2).
      (* 2ms 2ms 1ms 2ms 2ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (preorder'' tree60.2).
      (* 2ms 2ms 1ms 2ms 3ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (preorder'' tree80.2).
      (* 2ms 2ms 2ms 2ms 3ms 3ms 4ms 3ms 2ms 2ms *)
      Time Eval vm_compute in (preorder'' tree100.2).
      (* 2ms 2ms 2ms 4ms 4ms 3ms 2ms 3ms 3ms 3ms *)

      Definition inorder'' {min max : Elem.t} {ord : bool} {height : nat}
                 (tree : {bal:bool & avl min max ord height bal}) : list Elem.t :=
          avl_rect
            (fun (t t0 : Elem.t) (b : bool) (n : nat) (b0 : bool)
                 (_ : avl t t0 b n b0) => list Elem.t)
            (fun (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool)
                 (min_l min_r max_l max_r val : Elem.t)
                 (_ : avl min_l max_l ord_l h_l bal_l)
                 (H : list Elem.t) (_ : avl min_r max_r ord_r h_r bal_r)
                 (H0 : list Elem.t) => H ++ [val] ++ H0)
            (fun val : Elem.t => [val]) min max ord height
            (tree .1) (tree .2).
      Time Eval vm_compute in (inorder'' tree20.2).
      (* 2ms 2ms 1ms 2ms 2ms 2ms 2ms 2ms 2ms 1ms *)
      Time Eval vm_compute in (inorder'' tree40.2).
      (* 2ms 1ms 1ms 2ms 2ms 4ms 3ms 2ms 2ms 4ms *)
      Time Eval vm_compute in (inorder'' tree60.2).
      (* 2ms 2ms 1ms 2ms 2ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (inorder'' tree80.2).
      (* 2ms 5ms 1ms 12ms 2ms 2ms 2ms 3ms 2ms 2ms *)
      Time Eval vm_compute in (inorder'' tree100.2).
      (* 2ms 3ms 5ms 3ms 2ms 3ms 4ms 3ms 2ms 2ms *)

      Definition postorder'' {min max : Elem.t} {ord : bool} {height : nat}
                 (tree : {bal:bool & avl min max ord height bal}) : list Elem.t :=
          avl_rect
            (fun (t t0 : Elem.t) (b : bool) (n : nat) (b0 : bool)
                 (_ : avl t t0 b n b0) => list Elem.t)
            (fun (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool)
                 (min_l min_r max_l max_r val : Elem.t)
                 (_ : avl min_l max_l ord_l h_l bal_l)
                 (H : list Elem.t) (_ : avl min_r max_r ord_r h_r bal_r)
                 (H0 : list Elem.t) => H ++ H0 ++ [val])
            (fun val : Elem.t => [val]) min max ord height
            (tree .1) (tree .2).
      Time Eval vm_compute in (postorder'' tree20.2).
      (* 2ms 2ms 1ms 2ms 2ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (postorder'' tree40.2).
      (* 2ms 2ms 1ms 2ms 3ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (postorder'' tree60.2).
      (* 2ms 2ms 6ms 4ms 2ms 2ms 2ms 2ms 2ms 2ms *)
      Time Eval vm_compute in (postorder'' tree80.2).
      (* 2ms 4ms 1ms 3ms 3ms 2ms 2ms 2ms 3ms 3ms *)
      Time Eval vm_compute in (postorder'' tree100.2).
      (* 2ms 2ms 2ms 3ms 2ms 2ms 3ms 2ms 3ms 2ms *)

      (* 60 LoC in normal form *)
      Definition search'' {min max : Elem.t} {ord : bool} {height : nat}
                 (tree : {bal : bool & avl min max ord height bal}) (value : Elem.t) : bool :=
          avl_rect
            (fun (t t0 : Elem.t) (b : bool) (n : nat) (b0 : bool)
                 (_ : avl t t0 b n b0) => bool)
            (fun (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool)
                 (min_l min_r max_l max_r val : Elem.t)
                 (_ : avl min_l max_l ord_l h_l bal_l)
                 (H : bool) (_ : avl min_r max_r ord_r h_r bal_r)
                 (H0 : bool) =>
               Elem.leb min_l value && Elem.leb value max_r && Elem.eqb value val
               || Elem.leb value max_l ==> H || Elem.leb min_r value ==> H0)
            (fun val : Elem.t => Elem.eqb value val) min max ord height
            (tree .1) (tree .2).
      Time Eval vm_compute in (search'' tree20.2 Elem.x).
      (* 3ms 3ms 6ms 3ms 4ms 3ms 4ms 3ms 9ms 3ms *)
      Time Eval vm_compute in (search'' tree40.2 Elem.x).
      (* 4ms 4ms 3ms 5ms 6ms 4ms 4ms 6ms 5ms 6ms *)
      Time Eval vm_compute in (search'' tree60.2 Elem.x).
      (* 8ms 6ms 11ms 7ms 7ms 8ms 6ms 8ms 8ms 8ms *)
      Time Eval vm_compute in (search'' tree80.2 Elem.x).
      (* 9ms 9ms 8ms 9ms 12ms 9ms 8ms 9ms 9ms 9ms *)
      Time Eval vm_compute in (search'' tree100.2 Elem.x).
      (* 11ms 11ms 10ms 12ms 11ms 10ms 11ms 11ms 11ms 11ms *)
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
