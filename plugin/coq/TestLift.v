Add LoadPath "coq".
Require Import List.
Require Import Ornamental.Ornaments.
Require Import Test.
Require Import Infrastructure.

(*
 * Test lifting directly
 *)

Set DEVOID search smart eliminators.

Configure Lift list vector { opaque f_equal }.
Configure Lift vector list { opaque f_equal }.

(* --- Simple constructor tests ---- *)

Definition nil' := @nil.

Lift list vector in nil' as nil'_c.
Theorem testNil:
  forall A, nil'_c A = existT (vector A) 0 (nilV A).
Proof.
  intros. reflexivity.
Qed.

Definition nilV' (A : Type) :=
  existT (vector A) 0 (nilV A).

Lift vector list in nilV' as nilV'_c.
Theorem testNilV:
  forall A, nilV'_c A = @nil A.
Proof.
  intros. reflexivity.
Qed.

Definition cons' := @cons.

Lift list vector in cons' as cons'_c.
Theorem testCons:
  forall A a pv,
    cons'_c A a pv =
    existT (vector A) (S (projT1 pv)) (consV A (projT1 pv) a (projT2 pv)).
Proof.
  intros. reflexivity.
Qed.

Lift vector list in cons'_c as consV'_c.
Theorem testConsV:
  forall A a l,
    consV'_c A a l = @cons A a l.
Proof.
  intros. reflexivity.
Qed.

(* --- Simple projection tests ---- *)

Lift list vector in orn_list_vector_index as ltv_indexer_lifted.

Theorem testProj:
  forall A pv, ltv_indexer_lifted A pv = projT1 pv.
Proof.
  intros. unfold ltv_indexer_lifted. test_exact_equality.
Qed.

Definition proj_index (A : Type) (pv : sigT (vector A)) :=
  projT1 pv.

Lift vector list in proj_index as proj_index_lifted.

Theorem testIndex:
  forall A l, proj_index_lifted A l = list_to_vector_index A l.
Proof.
  intros. unfold proj_index_lifted. test_exact_equality.
Qed.

Definition proj_val (A : Type) (pv : sigT (vector A)) :=
  projT2 pv.

Lift vector list in proj_val as proj_val_lifted.

Theorem testVal:
  forall A l, proj_val_lifted A l = l.
Proof.
  intros. unfold proj_val_lifted. test_exact_equality.
Qed.

(* --- Simple functions --- *)

Definition hd (A : Type) (default : A) (l : list A) :=
  list_rect
    (fun (_ : list A) => A)
    default
    (fun (x : A) (_ : list A) (_ : A) =>
      x)
    l.

Definition hd_vect (A : Type) (default : A) (pv : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => A)
    default
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : A) =>
      x)
    (projT1 pv)
    (projT2 pv).

Lift list vector in hd as hd_vect_lifted.

Theorem test_hd_vect:
  forall (A : Type) (default : A) (pv : packed_vector A),
    hd_vect A default pv = hd_vect_lifted A default pv.
Proof.
  intros. reflexivity.
Qed.

Lift vector list in hd_vect_lifted as hd_lifted.

Theorem test_hd:
  forall (A : Type) (default : A) (l : list A),
    hd A default l = hd_lifted A default l.
Proof.
  intros. reflexivity.
Qed.

(* flist/flector version *)
(* these use save ornament to make sure we support it *)

Save ornament natFlector.flist natFlector.flector { promote = orn_flist_flector_nat; forget = orn_flist_flector_nat_inv }.

Definition hdF (default : nat) (l : natFlector.flist) :=
  natFlector.flist_rect
    (fun (_ : natFlector.flist) => nat)
    default
    (fun (x : nat) (_ : natFlector.flist) (_ : nat) =>
      x)
    l.

Definition hd_vectF (default : nat) (pv : sigT natFlector.flector) :=
  natFlector.flector_rect
    (fun (n0 : nat) (_ : natFlector.flector n0) => nat)
    default
    (fun (n0 : nat) (x : nat) (_ : natFlector.flector n0) (_ : nat) =>
      x)
    (projT1 pv)
    (projT2 pv).

Lift natFlector.flist natFlector.flector in hdF as hd_vectF_lifted.

Theorem test_hd_vectF:
  forall (default : nat) (pv : sigT natFlector.flector),
    hd_vectF default pv = hd_vectF_lifted default pv.
Proof.
  intros. reflexivity.
Qed.

Lift natFlector.flector natFlector.flist in hd_vectF_lifted as hdF_lifted.

Theorem test_hdF:
  forall (default : nat) (l : natFlector.flist),
    hdF default l = hdF_lifted default l.
Proof.
  intros. reflexivity.
Qed.

(* hd_error *)

Definition hd_error (A : Type) (l : list A) :=
  list_rect
    (fun (_ : list A) => option A)
    None
    (fun (x : A) (_ : list A) (_ : option A) =>
      Some x)
    l.

Definition hd_vect_error (A : Type) (v : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (_ : vector A n0) => option A)
    None
    (fun (n0 : nat) (x : A) (_ : vector A n0) (_ : option A) =>
      Some x)
    (projT1 v)
    (projT2 v).

Lift list vector in hd_error as hd_vect_error_lifted.

Theorem test_hd_vect_error:
  forall (A : Type) (pv : packed_vector A),
    hd_vect_error A pv = hd_vect_error_lifted A pv.
Proof.
  intros. reflexivity.
Qed.

Lift vector list in hd_vect_error_lifted as hd_error_lifted.

Theorem test_hd_error:
  forall (A : Type) (l : list A),
    hd_error A l = hd_error_lifted A l.
Proof.
  intros. reflexivity.
Qed.

(* append *)

(*
 * Test applying ornaments to lift functions, without internalizing
 * the ornamentation (so the type won't be useful yet).
 *)

Definition append (A : Type) (l1 : list A) (l2 : list A) :=
  list_rect
    (fun (_ : list A) => list A)
    l2
    (fun (a : A) (_ : list A) (IH : list A) =>
      a :: IH)
    l1.

Definition append_vect_inner (A : Type) (pv1 : sigT (vector A)) (pv2 : sigT (vector A)) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => sigT (fun (n : nat) => vector A n))
    (existT (vector A) (projT1 pv2) (projT2 pv2))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IH : sigT (fun (n : nat) => vector A n)) =>
      existT
        (vector A)
        (S (projT1 IH))
        (consV A (projT1 IH) a (projT2 IH)))
    (projT1 pv1)
    (projT2 pv1).

Definition append_vect (A : Type) (pv1 : sigT (vector A)) (pv2 : sigT (vector A)) :=
  existT _ (projT1 (append_vect_inner A pv1 pv2)) (projT2 (append_vect_inner A pv1 pv2)).

Lift list vector in append as append_vect_lifted.

Theorem test_append_vect:
  forall (A : Type) (pv1 : packed_vector A) (pv2 : packed_vector A),
    append_vect A pv1 pv2  = append_vect_lifted A pv1 pv2.
Proof.
  reflexivity.
Qed.

Lift vector list in append_vect_lifted as append_lifted.

Theorem test_append :
  forall (A : Type) (l1 : list A) (l2 : list A),
    append A l1 l2  = append_lifted A l1 l2.
Proof.
  intros. reflexivity.
Qed.

(* append for flectors *)

Definition appendF (l1 : natFlector.flist) (l2 : natFlector.flist) :=
  natFlector.flist_rect
    (fun (_ : natFlector.flist) => natFlector.flist)
    l2
    (fun (a : nat) (_ : natFlector.flist) (IH : natFlector.flist) =>
      natFlector.consF a IH)
    l1.

Definition append_vectF_inner (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector) :=
  natFlector.flector_rect
    (fun (n0 : nat) (v0 : natFlector.flector n0) => sigT natFlector.flector)
    (existT natFlector.flector (projT1 pv2) (projT2 pv2))
    (fun (n0 : nat) (a : nat) (v0 : natFlector.flector n0) (IH : sigT natFlector.flector) =>
      existT
        natFlector.flector
        (natFlector.SIfEven a (projT1 IH))
        (natFlector.consFV (projT1 IH) a (projT2 IH)))
    (projT1 pv1)
    (projT2 pv1).

Definition append_vectF (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector) :=
  existT _ (projT1 (append_vectF_inner pv1 pv2)) (projT2 (append_vectF_inner pv1 pv2)).

Lift natFlector.flist natFlector.flector in appendF as append_vectF_lifted.

Theorem test_append_vectF:
  forall (pv1 : sigT natFlector.flector) (pv2 : sigT natFlector.flector),
    append_vectF pv1 pv2 = append_vectF_lifted pv1 pv2.
Proof.
  intros. reflexivity.
Qed.

Lift natFlector.flector natFlector.flist in append_vectF as appendF_lifted.

Theorem test_appendF :
  forall (l1 : natFlector.flist) (l2 : natFlector.flist),
    appendF l1 l2  = appendF_lifted l1 l2.
Proof.
  intros. reflexivity.
Qed.

(* tl *)

Definition tl (A : Type) (l : list A) :=
  @list_rect
    A
    (fun (l0 : list A) => list A)
    (@nil A)
    (fun (a : A) (l0 : list A) (_ : list A) =>
      l0)
    l.

Definition tl_vect_inner (A : Type) (pv : packed_vector A) :=
  vector_rect
    A
    (fun (n0 : nat) (v0 : vector A n0) => sigT (fun (n : nat) => vector A n))
    (existT (vector A) 0 (nilV A))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (_ : sigT (fun (n : nat) => vector A n)) =>
      existT (vector A) n0 v0)
    (projT1 pv)
    (projT2 pv).

Definition tl_vect (A : Type) (pv : packed_vector A) :=
  existT _ (projT1 (tl_vect_inner A pv)) (projT2 (tl_vect_inner A pv)).

Lift list vector in tl as tl_vect_lifted.

Theorem test_tl_vect:
  forall (A : Type) (pv : packed_vector A),
    tl_vect A pv = tl_vect_lifted A pv.
Proof.
  intros. reflexivity.
Qed.

Lift vector list in tl_vect as tl_lifted.

Theorem test_tl:
  forall (A : Type) (l : list A),
    tl A l = tl_lifted A l.
Proof.
  intros. reflexivity.
Qed.

(*
 * In as an application of an induction principle
 *)
Definition In (A : Type) (a : A) (l : list A) : Prop :=
  @list_rect
    A
    (fun (_ : list A) => Prop)
    False
    (fun (b : A) (l0 : list A) (IHl : Prop) =>
      a = b \/ IHl)
    l.

Definition In_vect (A : Type) (a : A) (pv : sigT (vector A)) : Prop :=
  @vector_rect
    A
    (fun (n1 : nat) (_ : vector A n1) => Prop)
    False
    (fun (n1 : nat) (b : A) (_ : vector A n1) (IHv : Prop) =>
      a = b \/ IHv)
    (projT1 pv)
    (projT2 pv).

Lift list vector in In as In_vect_lifted.

Theorem test_in_vect:
  forall (A : Type) (a : A) (pv : packed_vector A),
    In_vect A a pv = In_vect_lifted A a pv.
Proof.
  intros. reflexivity.
Qed.

Lift vector list in In_vect as In_lifted.

Theorem test_in:
  forall (A : Type) (a : A) (l : list A),
    In A a l = In_lifted A a l.
Proof.
  intros. reflexivity.
Qed.

(* --- Proofs --- *)

(* app_nil_r *)

Definition app_nil_r (A : Type) (l : list A) :=
  @list_ind
    A
    (fun (l0 : list A) => append A l0 (@nil A) = l0)
    (@eq_refl (list A) (@nil A))
    (fun (a : A) (l0 : list A) (IHl : append A l0 (@nil A) = l0) =>
      @eq_ind_r
        (list A)
        l0
        (fun (l1 : list A) => @cons A a l1 = @cons A a l0)
        (@eq_refl (list A) (@cons A a l0))
        (append A l0 (@nil A))
        IHl)
    l.

Definition app_nil_r_vect (A : Type) (pv : packed_vector A) :=
  vector_ind
    A
    (fun (n0 : nat) (v0 : vector A n0) =>
      append_vect A (existT (vector A) n0 v0) (existT (vector A) O (nilV A)) = existT (vector A) n0 v0)
    (@eq_refl (sigT (vector A)) (existT (vector A) O (nilV A)))
    (fun (n0 : nat) (a : A) (v0 : vector A n0) (IHp : append_vect A (existT (vector A) n0 v0) (existT (vector A) O (nilV A)) = existT (vector A) n0 v0) =>
      @eq_ind_r
        (sigT (vector A))
        (existT (vector A) n0 v0)
        (fun (pv1 : sigT (vector A)) =>
          existT (vector A) (S (projT1 pv1)) (consV A (projT1 pv1) a (projT2 pv1)) = existT (vector A) (S n0) (consV A n0 a v0))
        (@eq_refl (sigT (vector A)) (existT (vector A) (S n0) (consV A n0 a v0)))
        (append_vect A (existT (vector A) n0 v0) (existT (vector A) 0 (nilV A)))
        IHp)
    (projT1 pv)
    (projT2 pv).

Lift list vector in app_nil_r as app_nil_r_vect_lifted.

Theorem test_app_nil_r_vect_exact:
  forall (A : Type) (pv : sigT (vector A)),
    append_vect_lifted A (existT (vector A) (projT1 pv) (projT2 pv)) (existT (vector A) 0 (nilV A)) = (existT (vector A) (projT1 pv) (projT2 pv)).
Proof.
  exact app_nil_r_vect_lifted.
Qed.

Lift vector list in app_nil_r_vect as app_nil_r_lifted.

Theorem test_app_nil_r:
  forall (A : Type) (l : list A),
    append_lifted A l (@nil A) = l.
Proof.
  exact app_nil_r_lifted.
Qed.

(* app_nil_r with flectors *)

Definition app_nil_rF (l : natFlector.flist) :=
  natFlector.flist_ind
    (fun (l0 : natFlector.flist) => appendF l0 natFlector.nilF = l0)
    (@eq_refl natFlector.flist natFlector.nilF)
    (fun (a : nat) (l0 : natFlector.flist) (IHl : appendF l0 natFlector.nilF = l0) =>
      @eq_ind_r
        natFlector.flist
        l0
        (fun (l1 : natFlector.flist) => natFlector.consF a l1 = natFlector.consF a l0)
        (@eq_refl natFlector.flist (natFlector.consF a l0))
        (appendF l0 natFlector.nilF)
        IHl)
    l.

(* this also checks that the shorthand notation works with functors *)
Lift natFlector.flist natFlector.flector in app_nil_rF as app_nil_r_vectF_lifted.

Theorem test_app_nil_r_vectF_exact:
  forall (pv : sigT natFlector.flector),
    append_vectF_lifted (existT natFlector.flector (projT1 pv) (projT2 pv)) (existT natFlector.flector 0 natFlector.nilFV) = (existT natFlector.flector (projT1 pv) (projT2 pv)).
Proof.
    exact app_nil_r_vectF_lifted.
Qed.

(* in_split *)

Theorem in_split :
  forall A x (l:list A), In A x l -> exists l1 l2, l = append A l1 (x::l2).
Proof.
  induction l; simpl; destruct 1.
  subst a; auto.
  exists nil, l; auto.
  destruct (IHl H) as (l1,(l2,H0)).
  exists (a::l1), l2; simpl. apply f_equal. auto.
Defined.

Preprocess in_split as in_split'.
Lift list vector in in_split' as in_split_vect_lifted.

Theorem test_in_split_vect_exact:
  forall (A : Type) (x : A) (pv : sigT (vector A)),
    In_vect_lifted A x (existT (vector A) (projT1 pv) (projT2 pv)) ->
       exists pv1 pv2 : sigT (vector A),
         existT (vector A) (projT1 pv) (projT2 pv) =
         append_vect_lifted A pv1
           (existT (vector A) (S (projT1 pv2)) (consV A (projT1 pv2) x (projT2 pv2))).
Proof.
  exact in_split_vect_lifted.
Qed.

(* discrimination *)

Definition is_cons (A : Type) (l : list A) :=
  list_rect
    (fun (_ : list A) => Prop)
    False
    (fun (_ : A) (_ : list A) (_ : Prop) => True)
    l.

Lift list vector in is_cons as is_cons_lifted.

(* hd_error_some_nil *)

Lemma hd_error_some_nil : forall A l (a:A), hd_error A l = Some a -> l <> nil.
Proof.
  unfold hd_error. destruct l; now discriminate.
Defined.

Preprocess hd_error_some_nil as hd_error_some_nil'.
Lift list vector in hd_error_some_nil' as hd_error_some_nil_vect_lifted.

Theorem test_hd_error_some_nil_vect_exact:
  forall (A : Type) (l : {H : nat & vector A H}) (a : A),
    hd_vect_error A (existT (vector A) (projT1 l) (projT2 l)) = Some a ->
    existT (vector A) (projT1 l) (projT2 l) <> existT (vector A) 0 (nilV A).
Proof.
   exact hd_error_some_nil_vect_lifted.
Qed.

(* --- Regressing the letin bug --- *)
Definition test_letin (A : Type) (xs : {n:nat & vector A n}) : {n:nat & vector A n} :=
  let n := projT1 xs in
  existT _ n (projT2 xs).

Lift vector list in test_letin as test_letin_list_lifted.

Lemma test_letin_list_lifted_ok (A : Type) (xs : list A) :
  test_letin_list_lifted A xs = xs.
Proof. reflexivity. Defined.

(* --- Regressing the bug Nate caught with LIFT-PACK and variables --- *)

(*
 * See: https://github.com/uwplse/ornamental-search/issues/14
 *)

Lemma tl_ok:
 forall (A : Type) (x : A) (xs xs' : list A),
   xs = cons x xs' -> 
   tl A xs = xs'.
Proof. 
  intros A a xs xs' E. rewrite E. reflexivity. 
Defined.

Lift list vector in tl_ok as tlV_ok.  

Theorem test_tlV_ok: 
  forall (A : Type) (x : A) (xs xs' : sigT (vector A)),
    existT (vector A) (projT1 xs) (projT2 xs) = existT (vector A) (S (projT1 xs')) (consV A (projT1 xs') x (projT2 xs')) -> 
    tl_vect_lifted A (existT (vector A) (projT1 xs) (projT2 xs)) = (existT (vector A) (projT1 xs') (projT2 xs')).
Proof.
  exact tlV_ok.
Qed.

Lemma uncons_eq:
  forall (A : Type) (x y : A) (xs ys : list A),
    cons x xs = cons y ys -> 
    x = y /\ xs = ys.
Proof. 
  intros A x y xs ys E. split. exact (f_equal (hd A x) E). exact (f_equal (tl A) E). 
Defined.

Lift list vector in uncons_eq as unconsV_eq.

Theorem test_uncons_eqV_ok:
  forall (A : Type) (x y : A) (xs ys : sigT (vector A)),
    existT (vector A) (S (projT1 xs)) (consV A (projT1 xs) x (projT2 xs)) = existT (vector A) (S (projT1 ys)) (consV A (projT1 ys) y (projT2 ys)) ->
    x = y /\ existT (vector A) (projT1 xs) (projT2 xs) = existT (vector A) (projT1 ys) (projT2 ys).
Proof.
  exact unconsV_eq.
Qed.

(* --- Lifting trees with different argument orders --- *)

Definition bintree_map (A : Type) (B : Type) (f : A -> B) (t : bintree A) :=
  bintree_rect
    A
    (fun _ => bintree B)
    (leaf B)
    (fun l IHl a r IHr => node B IHl (f a) IHr)
    t.

Lemma map_id: 
  forall (A : Type) (b : bintree A),
    bintree_map A A id b = b.
Proof.
  intros. induction b.
  - auto.
  - simpl. rewrite IHb1. rewrite IHb2. auto.
Defined.

Lift bintree bintreeV in bintree_map as bintree_mapV.
Lift bintree bintreeV in map_id as map_idV.

(* --- Caching only handles one pair, so need an alias for now --- *)

Definition bintree_map' (A : Type) (B : Type) (f : A -> B) (t : bintree A) :=
  bintree_rect
    A
    (fun _ => bintree B)
    (leaf B)
    (fun l IHl a r IHr => node B IHl (f a) IHr)
    t.

Lemma map_id': 
  forall (A : Type) (b : bintree A),
    bintree_map' A A id b = b.
Proof.
  intros. induction b.
  - auto.
  - simpl. rewrite IHb1. rewrite IHb2. auto.
Defined.

Lift bintree bintreeV2 in bintree_map' as bintree_mapV2.
Lift bintree bintreeV2 in map_id' as map_idV2.

(* --- Universe regression --- *)

Set DEVOID lift type.

Definition type := Type.

Lift bintree bintreeV2 in type as type'.

  
