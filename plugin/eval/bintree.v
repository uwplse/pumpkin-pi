Require Import Ornamental.Ornaments.
Require Import Nat List Sorting.Permutation.
Require Import lemmas.
Import ListNotations.

Open Scope bool_scope.

Infix "==" := Nat.eqb (at level 70, right associativity) : nat_scope.
Notation "x <= y" := (Nat.leb x y) (at level 70, y at next level, right associativity) : nat_scope.
Notation "p '.1'" := (projT1 p) (at level 8, left associativity).
Notation "p '.2'" := (projT2 p) (at level 8, left associativity).
Notation "(| x , y |)" := (existT _ x y).

Definition is_true (b : bool) : Prop := b = true.
Coercion is_true : bool >-> Sortclass.


Module Type Comparable.

Parameter t : Type.
Parameter leb : t -> t -> bool.
Parameter trans : forall x y z, leb x y -> leb y z -> leb x z.
Parameter total : forall x y, {leb x y} + {leb y x}.
Parameter antisym : forall x y, leb x y -> leb y x -> x = y.

Definition eqb x y := leb x y && leb y x.
Definition ltb x y := leb x y && negb (leb y x).

End Comparable.


Module CaseStudy (Elem : Comparable).

Module Base.

Inductive bintree : Type :=
| Branch (val : Elem.t) (left right : bintree)
| Leaf (val : Elem.t).

Definition preorder (t : bintree) : list Elem.t :=
  bintree_rect
    (fun _ => list Elem.t)
    (fun x _ ys _ zs => [x] ++ ys ++ zs)
    (fun x => [x])
    t.

Definition inorder (t : bintree) : list Elem.t :=
  bintree_rect
    (fun _ => list Elem.t)
    (fun x _ ys _ zs => ys ++ [x] ++ zs)
    (fun x => [x])
    t.

Definition postorder (t : bintree) : list Elem.t :=
  bintree_rect
    (fun _ => list Elem.t)
    (fun x _ ys _ zs => ys ++ zs ++ [x])
    (fun x => [x])
    t.

Definition mirror (t : bintree) : bintree :=
  bintree_rect
    (fun _ => bintree)
    (fun v _ l _ r => Branch v r l)
    (fun v => Leaf v)
    t.

Lemma pre_permutes : forall t : bintree,
    permutes (preorder t) (inorder t).
Proof.
  induction t; simpl.
  - apply perm_cons_app. apply perm_app; assumption.
  - apply perm_skip. apply perm_nil.
Defined.

Lemma post_permutes : forall t : bintree,
    permutes (postorder t) (inorder t).
Proof.
  induction t; simpl.
  - apply perm_app. assumption. apply perm_sym. apply perm_cons_app.
    rewrite app_nil_r. apply perm_sym. assumption.
  - apply perm_skip. apply perm_nil.
Defined.

Lemma pre_post_permutes : forall t : bintree,
    permutes (preorder t) (postorder t).
Proof.
  intro t. eapply perm_trans. apply pre_permutes.
  apply perm_sym, post_permutes.
Defined.

Lemma mirror_permutes : forall t : bintree,
    permutes (inorder t) (inorder (mirror t)).
Proof.
  induction t; simpl.
  - apply perm_sym. eapply perm_trans. apply perm_app_comm. simpl.
    apply perm_cons_app. apply perm_sym. apply perm_app; assumption.
  - apply perm_skip. apply perm_nil.
Defined.

Lemma mirror_inv : forall t : bintree,
    mirror (mirror t) = t.
Proof.
  induction t; simpl; [rewrite IHt1, IHt2|]; reflexivity.
Defined.

End Base.


Module Measured.

Inductive bintree : nat -> Type :=
| Branch (h_l h_r : nat)
         (val : Elem.t)
         (left : bintree h_l) (right : bintree h_r)
  : bintree (S (Nat.max h_l h_r))
| Leaf (val : Elem.t) : bintree O.

Ornament orn_height from Base.bintree to bintree.

Ornamental Definition preorder' from Base.preorder using orn_height orn_height_inv.
Definition preorder h t := preorder' (existT _ h t).

Ornamental Definition inorder' from Base.inorder using orn_height orn_height_inv.
Definition inorder h t := inorder' (existT _ h t).

Ornamental Definition postorder' from Base.postorder using orn_height orn_height_inv.
Definition postorder h t := postorder' (existT _ h t).


Ornamental Definition mirror' from Base.mirror using orn_height orn_height_inv.

Lemma mirror_height (h : nat) (t : bintree h) :
    (mirror' (existT _ h t)).1 = h.
Proof.
  induction t; try reflexivity.
  unfold mirror', projT1 in *. simpl in *.
  rewrite IHt1, IHt2, max_comm. reflexivity.
Defined.

Definition mirror (h : nat) (t : bintree h) : bintree h.
  destruct (mirror' (existT _ h t)) eqn:E.
  apply (f_equal (@projT1 nat bintree)) in E. simpl in E.
  rewrite mirror_height in E. rewrite E. exact b.
Defined.

Ornamental Definition pre_permutes' from Base.pre_permutes using orn_height orn_height_inv.
Lemma pre_permutes (h : nat) : forall (t : bintree h),
    permutes (preorder h t) (inorder h t).
Proof.
  intro t. unfold preorder, inorder. set (t' := (|h, t|)). apply pre_permutes'.
Defined.

Ornamental Definition post_permutes' from Base.post_permutes using orn_height orn_height_inv.
Lemma post_permutes (h : nat) : forall (t : bintree h),
    permutes (postorder h t) (inorder h t).
Proof.
  intro t. unfold postorder, inorder. set (t' := (|h, t|)). apply post_permutes'.
Defined.

Ornamental Modularization pre_post_permutes' from Base.pre_post_permutes using orn_height orn_height_inv.
Lemma pre_post_permutes (h : nat) : forall (t : bintree h),
    permutes (preorder h t) (postorder h t).
Proof.
  intro t. unfold preorder, postorder. set (t' := (|h, t|)). apply pre_post_permutes'.
Defined.

Ornamental Definition mirror_permutes' from Base.mirror_permutes using orn_height orn_height_inv.
(* NOTE: Not worth trying to prove the nice dependent typing for the above lemma. *)

(* XXX: Illegal application (bug in ornamental modularization) *)
(* Ornamental Definition mirror_inv' from Base.mirror_inv using orn_height orn_height_inv. *)

End Measured.

Module Sized.

Inductive bintree : nat -> Type :=
| Branch (size_l size_r : nat)
         (val : Elem.t)
         (left : bintree size_l) (right : bintree size_r)
  : bintree (S (size_l + size_r))
| Leaf (val : Elem.t) : bintree (S O).

Ornament orn_size from Base.bintree to bintree.

Ornamental Definition preorder' from Base.preorder using orn_size orn_size_inv.
Definition preorder s t := preorder' (existT _ s t).

Ornamental Definition inorder' from Base.inorder using orn_size orn_size_inv.
Definition inorder s t := inorder' (existT _ s t).

Ornamental Definition postorder' from Base.postorder using orn_size orn_size_inv.
Definition postorder s t := postorder' (existT _ s t).

Ornamental Definition mirror' from Base.mirror using orn_size orn_size_inv.

Lemma mirror_size (s : nat) (t : bintree s) :
    (mirror' (existT _ s t)).1 = s.
Proof.
  induction t; try reflexivity.
  unfold mirror', projT1 in *. simpl in *.
  rewrite IHt1, IHt2, add_comm, add_comm. reflexivity.
Defined.

Definition mirror (s : nat) (t : bintree s) : bintree s.
  destruct (mirror' (existT _ s t)) eqn:E.
  apply (f_equal (@projT1 nat bintree)) in E. simpl in E.
  rewrite mirror_size in E. rewrite <- E in b. exact b.
Defined.

Ornamental Definition pre_permutes' from Base.pre_permutes using orn_size orn_size_inv.
Lemma pre_permutes (s : nat) : forall (t : bintree s),
    permutes (preorder s t) (inorder s t).
Proof.
  intro t. unfold preorder, inorder. set (t' := (|s, t|)). apply pre_permutes'.
Defined.

Ornamental Definition post_permutes' from Base.post_permutes using orn_size orn_size_inv.
Lemma post_permutes (s : nat) : forall (t : bintree s),
    permutes (postorder s t) (inorder s t).
Proof.
  intro t. unfold postorder, inorder. set (t' := (|s, t|)). apply post_permutes'.
Defined.

Ornamental Modularization pre_post_permutes' from Base.pre_post_permutes using orn_size orn_size_inv.
Lemma pre_post_permutes (s : nat) : forall (t : bintree s),
    permutes (preorder s t) (postorder s t).
Proof.
  intro t. unfold preorder, postorder. set (t' := (|s, t|)). apply pre_post_permutes'.
Defined.

Ornamental Definition mirror_permutes' from Base.mirror_permutes using orn_size orn_size_inv.
(* NOTE: Not worth trying to prove the nice dependent typing for the above lemma. *)

(* XXX: Illegal pattern-match *)
(*
Error: A term of inductive type Base.bintree
was given to a pattern-matching expression on the inductive type
sigT.
 *)
(* Ornamental Definition mirror_inv' from Base.mirror_inv using orn_size orn_size_inv. *)

End Sized.

Module Ordered.

Inductive __ordtree : Elem.t -> Type :=
| __Branch (min_l min_r : Elem.t)
           (val : Elem.t)
           (left : __ordtree min_l) (right : __ordtree min_r)
  : __ordtree min_l
| __Leaf (val : Elem.t) : __ordtree val.

Inductive _ordtree : Elem.t -> Elem.t -> Type :=
| _Branch (min_l min_r : Elem.t) (max_l max_r : Elem.t)
          (val : Elem.t)
          (left : _ordtree min_l max_l) (right : _ordtree min_r max_r)
  : _ordtree min_l max_r
| _Leaf (val : Elem.t) : _ordtree val val.

Definition inv (ord_l ord_r : bool) (max_l val min_r : Elem.t) : bool :=
  ord_l && ord_r && Elem.ltb max_l val && Elem.ltb val min_r.

Inductive ordtree : Elem.t -> Elem.t -> bool -> Type :=
| Branch (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
         (val : Elem.t)
         (left : ordtree min_l max_l ord_l) (right : ordtree min_r max_r ord_r)
  : ordtree min_l max_r (inv ord_l ord_r max_l val min_r)
| Leaf (val : Elem.t) : ordtree val val true.

Ornament __orn_ordtree from Base.bintree to __ordtree.
Ornament _orn_ordtree from __ordtree to _ordtree.
Ornament orn_ordtree from _ordtree to ordtree.

Ornamental Definition __preorder' from Base.preorder using __orn_ordtree __orn_ordtree_inv.
Definition __preorder min (tree : __ordtree min) := __preorder' (existT _ min tree).
Ornamental Definition _preorder' from __preorder using _orn_ordtree _orn_ordtree_inv.
Definition _preorder min max (tree : _ordtree min max) := _preorder' min (existT _ max tree).
Ornamental Definition preorder' from _preorder using orn_ordtree orn_ordtree_inv.
Definition preorder min max ord (tree : ordtree min max ord) := preorder' min max (existT _ ord tree).

Ornamental Definition __inorder' from Base.inorder using __orn_ordtree __orn_ordtree_inv.
Definition __inorder min (tree : __ordtree min) := __inorder' (existT _ min tree).
Ornamental Definition _inorder' from __inorder using _orn_ordtree _orn_ordtree_inv.
Definition _inorder min max (tree : _ordtree min max) := _inorder' min (existT _ max tree).
Ornamental Definition inorder' from _inorder using orn_ordtree orn_ordtree_inv.
Definition inorder min max ord (tree : ordtree min max ord) := inorder' min max (existT _ ord tree).

Ornamental Definition __postorder' from Base.postorder using __orn_ordtree __orn_ordtree_inv.
Definition __postorder min (tree : __ordtree min) := __postorder' (existT _ min tree).
Ornamental Definition _postorder' from __postorder using _orn_ordtree _orn_ordtree_inv.
Definition _postorder min max (tree : _ordtree min max) := _postorder' min (existT _ max tree).
Ornamental Definition postorder' from _postorder using orn_ordtree orn_ordtree_inv.
Definition postorder min max ord (tree : ordtree min max ord) := postorder' min max (existT _ ord tree).

Ornamental Definition __mirror' from Base.mirror using __orn_ordtree __orn_ordtree_inv.
Definition __mirror min (tree : __ordtree min) := __mirror' (existT _ min tree).
(* XXX: Anomaly "Uncaught exception Failure("tl")." *)
(* Ornamental Definition _mirror' from __mirror using _orn_ordtree _orn_ordtree_inv. *)

(* XXX: Illegal application *)
(*
The term "__ordtree_rect" of type
 "forall P : forall t : Elem.t, __ordtree t -> Type,
  (forall (min_l min_r val : Elem.t) (left : __ordtree min_l),
   P min_l left ->
   forall right : __ordtree min_r,
   P min_r right -> P min_l (__Branch min_l min_r val left right)) ->
  (forall val : Elem.t, P val (__Leaf val)) ->
  forall (t : Elem.t) (__o : __ordtree t), P t __o"
cannot be applied to the terms
 "fun (t : Elem.t) (__o : __ordtree t) =>
  permutes (Base.preorder (__orn_ordtree_inv (|t, __o|)))
    (Base.inorder (__orn_ordtree_inv (|t, __o|)))"
   : "forall t : Elem.t, __ordtree t -> Prop"
 "fun (min_l min_r val : Elem.t) (left : __ordtree min_l)
    (H : permutes (Base.preorder (__orn_ordtree_inv (|min_l, left|)))
           (Base.inorder (__orn_ordtree_inv (|min_l, left|))))
    (right : __ordtree min_r)
    (H0 : permutes (Base.preorder (__orn_ordtree_inv (|min_r, right|)))
            (Base.inorder (__orn_ordtree_inv (|min_r, right|)))) =>
  perm_cons_app (Base.inorder (__orn_ordtree_inv (|min_l, left|)))
    (Base.inorder (__orn_ordtree_inv (|min_r, right|))) val
    (perm_app H H0)"
   : "forall (min_l min_r val : Elem.t) (left : __ordtree min_l),
      permutes (Base.preorder (__orn_ordtree_inv (|min_l, left|)))
        (Base.inorder (__orn_ordtree_inv (|min_l, left|))) ->
      forall right : __ordtree min_r,
      permutes (Base.preorder (__orn_ordtree_inv (|min_r, right|)))
        (Base.inorder (__orn_ordtree_inv (|min_r, right|))) ->
      permutes
        (val
         :: Base.preorder (__orn_ordtree_inv (|min_l, left|)) ++
            Base.preorder (__orn_ordtree_inv (|min_r, right|)))
        (Base.inorder (__orn_ordtree_inv (|min_l, left|)) ++
         val :: Base.inorder (__orn_ordtree_inv (|min_r, right|)))"
 "fun val : Elem.t => perm_skip val (perm_nil Elem.t)"
   : "forall val : Elem.t, permutes [val] [val]"
 "t .1" : "Elem.t"
 "t .2" : "__ordtree t .1"
The 2nd term has type
 "forall (min_l min_r val : Elem.t) (left : __ordtree min_l),
  permutes (Base.preorder (__orn_ordtree_inv (|min_l, left|)))
    (Base.inorder (__orn_ordtree_inv (|min_l, left|))) ->
  forall right : __ordtree min_r,
  permutes (Base.preorder (__orn_ordtree_inv (|min_r, right|)))
    (Base.inorder (__orn_ordtree_inv (|min_r, right|))) ->
  permutes
    (val
     :: Base.preorder (__orn_ordtree_inv (|min_l, left|)) ++
        Base.preorder (__orn_ordtree_inv (|min_r, right|)))
    (Base.inorder (__orn_ordtree_inv (|min_l, left|)) ++
     val :: Base.inorder (__orn_ordtree_inv (|min_r, right|)))"
which should be coercible to
 "forall (min_l min_r val : Elem.t) (left : __ordtree min_l),
  (fun (t : Elem.t) (__o : __ordtree t) =>
   permutes (Base.preorder (__orn_ordtree_inv (|t, __o|)))
     (Base.inorder (__orn_ordtree_inv (|t, __o|)))) min_l left ->
  forall right : __ordtree min_r,
  (fun (t : Elem.t) (__o : __ordtree t) =>
   permutes (Base.preorder (__orn_ordtree_inv (|t, __o|)))
     (Base.inorder (__orn_ordtree_inv (|t, __o|)))) min_r right ->
  (fun (t : Elem.t) (__o : __ordtree t) =>
   permutes (Base.preorder (__orn_ordtree_inv (|t, __o|)))
     (Base.inorder (__orn_ordtree_inv (|t, __o|)))) min_l
    (__Branch min_l min_r val left right)".
 *)
(* In this case, the intermediate term observed after meta-reduction is
 * ill-typed because necessary definitional equalities are blocked by explicit
 * ornamental conversions. One would think that delta/iota-reduction should
 * push through the ornamental conversions and reduce to corresponding to
 * corresponding normal forms, and even if that's not the case, ornamental
 * modularization should substitute in the lifted version of each base function.
 *
 * FIXME: This kind of bug cannot be ignored.
 *)
(* Ornamental Definition __pre_permutes' from Base.pre_permutes using __orn_ordtree __orn_ordtree_inv. *)

End Ordered.

Module Balanced.

Inductive _avltree : Elem.t -> Elem.t -> bool -> nat -> Type :=
| _Branch (h_l h_r : nat) (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
          (val : Elem.t)
          (left : _avltree min_l max_l ord_l h_l) (right : _avltree min_r max_r ord_r h_r)
  : _avltree min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) (S (Nat.max h_l h_r))
| _Leaf (val : Elem.t) : _avltree val val true O.

Definition inv (bal_l bal_r : bool) (h_l h_r : nat) : bool :=
  bal_l && bal_r && (h_l - h_r <= 1) && (h_r - h_l <= 1).

Inductive avltree : Elem.t -> Elem.t -> bool -> nat -> bool -> Type :=
| Branch (bal_l bal_r : bool) (h_l h_r : nat) (ord_l ord_r : bool) (min_l min_r : Elem.t) (max_l max_r : Elem.t)
         (val : Elem.t)
         (left : avltree min_l max_l ord_l h_l bal_l) (right : avltree min_r max_r ord_r h_r bal_r)
  : avltree min_l max_r (Ordered.inv ord_l ord_r max_l val min_r) (S (Nat.max h_l h_r)) (inv bal_l bal_r h_l h_r)
| Leaf (val : Elem.t) : avltree val val true O true.

Ornament _orn_avltree from Ordered.ordtree to _avltree.
Ornament orn_avltree from _avltree to avltree.

Ornamental Definition _preorder' from Ordered.preorder using _orn_avltree _orn_avltree_inv.
Definition _preorder min max ord h (t : _avltree min max ord h) := _preorder' min max ord (existT _ h t).
Ornamental Definition preorder' from _preorder using orn_avltree orn_avltree_inv.
Definition preorder min max ord h bal (t : avltree min max ord h bal) := preorder' min max ord h (existT _ bal t).

Ornamental Definition _inorder' from Ordered.inorder using _orn_avltree _orn_avltree_inv.
Definition _inorder min max ord h (t : _avltree min max ord h) := _inorder' min max ord (existT _ h t).
Ornamental Definition inorder' from _inorder using orn_avltree orn_avltree_inv.
Definition inorder min max ord h bal (t : avltree min max ord h bal) := inorder' min max ord h (existT _ bal t).

Ornamental Definition _postorder' from Ordered.postorder using _orn_avltree _orn_avltree_inv.
Definition _postorder min max ord h (t : _avltree min max ord h) := _postorder' min max ord (existT _ h t).
Ornamental Definition postorder' from _postorder using orn_avltree orn_avltree_inv.
Definition postorder min max ord h bal (t : avltree min max ord h bal) := postorder' min max ord h (existT _ bal t).

End Balanced.

Module Heaped.

Inductive _binheap : nat -> Elem.t -> Type :=
| Branch_ (min_l min_r : Elem.t) (h_l h_r : nat) (val : Elem.t)
          (left : _binheap h_l min_l) (right : _binheap h_r min_r)
  : _binheap (S (Nat.max h_l h_r)) val
| Leaf_ (val : Elem.t) : _binheap O val.

Definition inv h_l h_r min_l min_r inv_l inv_r val : bool :=
  inv_l && inv_r && (h_l == h_r) && Elem.ltb min_l val && Elem.ltb min_r val.

Inductive binheap : nat -> Elem.t -> bool -> Type :=
| Branch (inv_l inv_r : bool) (min_l min_r : Elem.t) (h_l h_r : nat)
         (val : Elem.t)
         (left : binheap h_l min_l inv_l) (right : binheap h_r min_r inv_r)
  : binheap (S (Nat.max h_l h_r)) val (inv h_l h_r min_l min_r inv_l inv_r val)
| Leaf (val : Elem.t) : binheap O val true.

Ornament _orn_binheap from Measured.bintree to _binheap.
Ornament orn_binheap from _binheap to binheap.

Ornamental Definition _preorder' from Measured.preorder using _orn_binheap _orn_binheap_inv.
Definition _preorder h min (t : _binheap h min) := _preorder' h (existT _ min t).
Ornamental Definition preorder' from _preorder using orn_binheap orn_binheap_inv.
Definition preorder h min ord (t : binheap h min ord) := preorder' h min (existT _ ord t).

Ornamental Definition _inorder' from Measured.inorder using _orn_binheap _orn_binheap_inv.
Definition _inorder h min (t : _binheap h min) := _inorder' h (existT _ min t).
Ornamental Definition inorder' from _inorder using orn_binheap orn_binheap_inv.
Definition inorder h min ord (t : binheap h min ord) := inorder' h min (existT _ ord t).

Ornamental Definition _postorder' from Measured.postorder using _orn_binheap _orn_binheap_inv.
Definition _postorder h min (t : _binheap h min) := _postorder' h (existT _ min t).
Ornamental Definition postorder' from _postorder using orn_binheap orn_binheap_inv.
Definition postorder h min ord (t : binheap h min ord) := postorder' h min (existT _ ord t).

(* XXX: Anomaly "Uncaught exception Failure("tl")." *)
(* Ornamental Definition _mirror' from Measured.mirror using _orn_binheap _orn_binheap_inv. *)

(* XXX: Anomaly "Uncaught exception Failure("tl")." *)
(* Ornamental Definition _pre_permutes'' from Measured.pre_permutes' using _orn_binheap _orn_binheap_inv. *)

(* XXX: Illegal application *)
(*
The term "Measured.preorder'" of type
 "forall t : {H : nat & Measured.bintree H},
  (fun (n : nat) (_ : Measured.bintree n) => list Elem.t) t .1 t .2"
cannot be applied to the term
 "(|n, (|t0, _b|)|)" : "{H : nat & {H0 : Elem.t & _binheap H H0}}"
This term has type "{H : nat & {H0 : Elem.t & _binheap H H0}}"
which should be coercible to
 "{H : nat & Measured.bintree H}".
 *)
(* Ornamental Definition _pre_permutes' from Measured.pre_permutes using _orn_binheap _orn_binheap_inv. *)
(* Lemma pre_permutes (s : nat) : forall (t : bintree s), *)
(*     permutes (preorder s t) (inorder s t). *)
(* Proof. *)
(*   intro t. unfold preorder, inorder. set (t' := (|s, t|)). apply pre_permutes'. *)
(* Defined. *)

(* Operations go here *)

End Heaped.

End CaseStudy.
