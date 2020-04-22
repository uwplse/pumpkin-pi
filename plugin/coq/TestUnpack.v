(*
 * Basic lifting tests for unpack, building on TestLift.v
 *)

Add LoadPath "coq".
Require Import Vector.
Require Import List.
Require Import Test.
Require Import TestLift.
Require Import Ornamental.Ornaments.
Require Import Infrastructure.

Set DEVOID lift type.

Definition packed_list_rect := Test.orn_list_vector_rect.
Definition length {T} l := orn_list_vector_index T l.
Definition packed T n := { s : sigT (vector T) & projT1 s = n}.

(* --- Simple constructor tests ---- *)

Program Definition nilp (T : Type):
  { l : list T & length l = 0 }.
Proof.
  exists (nil' T). (* lists *)
  reflexivity. (* lengths *)
Defined.

Lift list vector in nilp as nilpv.
Lift packed vector in nilpv as nilV.

Theorem testNil:
  nilV = Test.nilV.
Proof.
  reflexivity.
Qed.

Definition nilV' (A : Type) := Test.nilV A.

Lift vector packed in nilV' as nilpv'.
Lift vector list in nilpv' as nilp'.

Theorem testNilV:
  forall A, nilp' A = nilp A.
Proof.
  intros. reflexivity.
Qed.

Program Definition consp (T : Type) (n : nat) (t : T):
  { l : list T & length l = n} ->
  { l : list T & length l = S n }.
Proof.
  intros. apply packed_list_rect with (P := fun (_ : { l : list T & length l = n }) => { l : list T & length l = S n}).
  - intros. exists (cons t a). (* lists *)
    simpl. auto. (* lengths *)
  - apply X.
Defined.

Lift list vector in consp as conspv.
Lift packed vector in conspv as consV.

Theorem testCons:
  consV = Test.consV.
Proof.
  reflexivity.
Qed.

Definition consV' (T : Type) (n : nat) (t : T) (v : vector T n) := Test.consV T n t v.

Lift vector packed in consV' as conspv'.
Print conspv'.
Lift vector list in conspv' as consp'.

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
(* these use save ornament to make sure wess support it *)

Save ornament natFlector.flist natFlector.flector { promote = orn_flist_flector_nat; forget = orn_flist_flector_nat_inv}. 

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




  


Definition packed T n := { s : sigT (vector T) & projT1 s = n}.

Configure Lift vector packed { opaque Eqdep_dec.UIP_dec Nat.eq_dec Vector.t_rect Coq.Vectors.VectorDef.t_rect eq_sym eq_trans }.


Definition minimal_test (T : Type) (n : nat) := { s : { n : nat & vector T n } & projT1 s = n }.
Lift packed vector in minimal_test as minimal_test_lifted. (* TODO move to tests somewhere *)
Print minimal_test_lifted.
Definition proj1_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT1 pv.
Print proj1_test.
Lift packed vector in proj1_test as proj1_test_lifted.
Definition proj1_test_expected (T : Type) (n : nat) (v : vector T n) := existT _ n v.
Print proj1_test_expected.
Print proj1_test_lifted.
Definition minimal_test_2 (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := pv.
Lift packed vector in minimal_test_2 as minimal_test_2_lifted { opaque eq_rect }. (* TODO need to stop this from reducing generally... refold or something *)
Print minimal_test_2_lifted.
Definition proj2_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT2 pv.
Lift packed vector in proj2_test as proj2_test_lifted.

Print proj2_test_lifted.

Definition lifted (T : Type) (n : nat)  (pv : vector T n) :=
  existT (fun (s : sigT (vector T)) => projT1 s = n) (existT (fun n => vector T n) n pv) (eq_refl n).
Check lifted.
Definition ex_test_constr (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) : {s : {x : nat & vector T x} & projT1 s = n} :=
  (fun n v H => existT _ (existT _ n v) H) (projT1 (projT1 pv)) (projT2 (projT1 pv)) (projT2 pv).

Print ex_test_constr.
Lift packed vector in ex_test_constr as ex_test_constr_lifted.
Print ex_test_constr_lifted.
Lemma ex_test_constr_lift_correct :
  forall T n v, ex_test_constr_lifted T n v = v.
Proof.
  reflexivity.
Qed.

(* TODO we will need to eta expand below to above before running: *)
Definition ex_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := existT _ (projT1 pv) (projT2 pv).
Definition ex_test_expected (T : Type) (n : nat) (v : vector T n) := v.

Lift packed vector in ex_test as ex_test_lifted.
Print ex_test_lifted. (* TODO yay!!! ok now move on to other tests *)

Definition proj1_eta_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT1 (existT _ (projT1 pv) (projT2 pv)).
Lift packed vector in proj1_eta_test as proj1_eta_test_lifted.
Print proj1_eta_test_lifted.

Definition my_id (T : Type) (n : nat) (v : vector T n) := v.
Lift vector packed in my_id as id'.
Definition id_expected (T : Type) (n : nat) (v : {s : {x : nat & vector T x} & projT1 s = n}) :=
existT (fun s : {x : nat & vector T x} => projT1 s = n)
  (existT (vector T) (projT1 (projT1 v)) (projT2 (projT1 v))) 
  (projT2 v).
Lemma test_id: id' = id_expected.
Proof.
  reflexivity.
Qed.

Definition my_pack_coh (T : Type) (n : nat) (v : vector T n) :=
    (@existT nat (vector T) n v).
Lift vector packed in my_pack_coh as my_pack_coh'.
Print my_pack_coh'.

Print t_unpack.
Print unpack_generic.
Print unpack_generic_section.
(*
TODO fail gracefully (can we remove p2 rule everywhere?):
Definition my_refl_coh (T : Type) (n : nat) (v : vector T n) :=
  erefl n.
Fail Lift vector packed in my_refl_coh as my_refl_coh'. (* TODO can't instantiate evars --- don't resolve until here and when that happens, don't lift coh *)
*)
Definition my_pack (T : Type) (n : nat) (v : vector T n) :=
  @existT (sigT (vector T)) (fun (s : sigT (vector T)) => projT1 s = n)
    (@existT nat (vector T) n v)
    (@eq_refl nat n).
Lift vector packed in my_pack as my_pack'.
Print my_pack'.

Definition my_id_rew (T : Type) (n : nat) (v : vector T n) := 
  @eq_rect nat n (t T) v n (@eq_refl nat n). (* rew eq_refl in v *)
Print my_id_rew.
Lift vector packed in my_id_rew as id''.
Print id''. (* TODO needs simplify poject packed _badly_ *)

Definition my_nil (T : Type) := nilV T.
Lift vector packed in my_nil as my_nil'.
Print my_nil'.

Definition my_cons (T : Type) (n : nat) (v : vector T n) (t : T) := consV n t v.
Lift vector packed in my_cons as my_cons'.

Definition packed_cons_ex_2 (T : Type) (n : nat) (v : vector T n) (t : T) : sigT (fun (n : nat) => { s0 : sigT (vector T) & projT1 s0 = n }) :=
  existT _ (S n) (existT _ (existT (vector T) (S n) (consV n t v)) eq_refl).

Definition packed_cons (T : Type) (n : nat) (v : vector T n) (t : T) :=
  existT _ (S n) (consV n t v).
Lift vector packed in packed_cons as packed_cons'.

Definition packed_nil (T : Type) := existT _ 0 (nilV T).
Lift vector packed in packed_nil as packed_nil'.
Print packed_nil'.

Definition packed_nil_ex_2 (T : Type) : sigT (fun (n : nat) => { s0 : sigT (vector T) & projT1 s0 = n }) :=
  existT _ 0 (existT _ (existT (vector T) 0 (nilV T)) eq_refl).
