Add LoadPath "coq/playground".
Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

Notation vector := Vector.t.
Notation nilV := Vector.nil.
Notation consV := Vector.cons.

Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.
Set DEVOID lift type.

(*
 * Attempt at understanding why lifting eliminators is OK, formally.
 *)

(* --- Algebraic ornaments --- *)

Definition sigT_vect_rect (A : Type) (P : {H : nat & vector A H} -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (l : {H : nat & vector A H}),
        P (existT (vector A) (projT1 l) (projT2 l)) ->
        P (existT (vector A) (S (projT1 l)) (consV A a (projT1 l) (projT2 l)))) 
  (l : {H : nat & vector A H}) :=
VectorDef.t_rect 
  A
  (fun (n : nat) (t : vector A n) => P (existT (vector A) n t))
  pnil
  (fun (h : A) (n : nat) (t : vector A n) (H : P (existT (vector A) n t)) =>
    pcons h (existT (vector A) n t) H) 
  (projT1 l) 
  (projT2 l).

Lift list vector in list_rect as sigT_vect_rect_lifted.
Lift vector list in sigT_vect_rect_lifted as list_rect_lifted.

Lemma lift_list_rect_correct: sigT_vect_rect_lifted = sigT_vect_rect.
Proof.
  reflexivity.
Qed.

Lemma lift_sigT_vect_rect_correct: list_rect_lifted = list_rect.
Proof.
  reflexivity.
Qed.

Definition list_rect_eta (A : Type) (P : list A -> Type)
  (pnil : P nil)
  (pcons : forall (a : A) (l : list A),
        P l ->
        P (cons a l))
  (l : list A) :=
@list_rect
  A
  (fun (l : list A) => P l)
  pnil
  (fun (h : A) (l : list A) (H : P l) =>
    pcons h l H) 
  l.

Definition path_rect_ltv_inv (A : Type) (P : list A -> Type) (s : sigT (vector A)):=
  P (list_to_t_inv A s).

Definition path_rect_ltv (A : Type) (P : sigT (vector A) -> Type) (l : list A):=
  P (list_to_t A l).

Definition list_rect_eta_1 (A : Type) (P : list A -> Type)
  (pnil : P nil)
  (pcons : forall (a : A) (l : list A),
        P l ->
        P (cons a l))
  (s : sigT (vector A)) :=
@list_rect
  A
  P
  pnil
  (fun (h : A) (l : list A) (H : P l) =>
    pcons h l H) 
  (list_to_t_inv A s).

Definition list_rect_eta_2 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : (path_rect_ltv A P) nil)
  (pcons : forall (a : A) (l : list A),
        (path_rect_ltv A P) l ->
        (path_rect_ltv A P) (cons a l))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : (path_rect_ltv A P) l) =>
    pcons h l H) 
  (list_to_t_inv A s).

Lemma path_rect_coh:
  forall (A : Type) (P : sigT (vector A) -> Type) (l : list A),
    (path_rect_ltv A P) l = P (list_to_t A l).
Proof.
  reflexivity.
Qed.

Definition list_rect_eta_3 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (list_to_t A nil))
  (pcons : forall (a : A) (l : list A),
        P (list_to_t A l) ->
        P (list_to_t A (cons a l)))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
    pcons h l H) 
  (list_to_t_inv A s).

Lemma refold_cons:
  forall (A : Type) (P : sigT (vector A) -> Type) (l : list A) (a : A),
    (list_to_t A (cons a l)) = existT (vector A) (S (list_to_t_index A l)) (consV A a (list_to_t_index A l) (projT2 (list_to_t A l))).
Proof.
  reflexivity.
Qed.

Definition list_rect_eta_4 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (list_to_t A nil))
  (pcons : forall (a : A) (l : list A),
        P (list_to_t A l) ->
        P (existT (vector A) (S (list_to_t_index A l)) (consV A a (list_to_t_index A l) (projT2 (list_to_t A l)))))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
    pcons h l H) 
  (list_to_t_inv A s).

Definition list_rect_eta_5 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P s->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
@list_rect
  A
  (path_rect_ltv A P)
  pnil
  (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
    pcons h (list_to_t A l) H) 
  (list_to_t_inv A s).

Check eq_rect.

Lemma path_ind_retract:
  forall A P (s : sigT (vector A)),
    path_rect_ltv A P (list_to_t_inv A s) ->
    P s.
Proof.
  intros. apply (@eq_rect (sigT (vector A)) (list_to_t A (list_to_t_inv A s)) _ X s (list_to_t_retraction A s)). 
Defined.

Definition list_rect_eta_6 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P s->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
path_ind_retract
  A
  P
  s
  (@list_rect
    A
    (path_rect_ltv A P)
    pnil
    (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
      pcons h (list_to_t A l) H) 
    (list_to_t_inv A s)).

Lemma path_ind_eta:
  forall A P (s : sigT (vector A)),
    P s ->
    P (existT (vector A) (projT1 s) (projT2 s)).
Proof.
  intros. induction s. auto.
Defined.

Definition list_rect_eta_7 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P s ->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
path_ind_eta
  A
  P
  s
  (path_ind_retract
    A
    P
    s
    (@list_rect
      A
      (path_rect_ltv A P)
      pnil
      (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
        pcons h (list_to_t A l) H) 
      (list_to_t_inv A s))).

Definition list_rect_eta_8 (A : Type) (P : sigT (vector A) -> Type)
  (pnil : P (existT (vector A) 0 (nilV A)))
  (pcons : forall (a : A) (s : sigT (vector A)),
        P (existT (vector A) (projT1 s) (projT2 s)) ->
        P (existT (vector A) (S (projT1 s)) (consV A a (projT1 s) (projT2 s))))
  (s : sigT (vector A)) :=
path_ind_eta
  A
  P
  s
  (path_ind_retract
    A
    P
    s
    (@list_rect
      A
      (path_rect_ltv A P)
      pnil
      (fun (h : A) (l : list A) (H : P (list_to_t A l)) =>
        pcons h (list_to_t A l) H) 
      (list_to_t_inv A s))).

(* ^ This general form is what works. What we get is because of some equality: *)

Lemma sigT_vect_rect_correct:
  forall A P pnil pcons s,
    sigT_vect_rect A P pnil pcons s =
    list_rect_eta_8 A P pnil pcons s.
Proof.
  (* ??? *)
Abort.

(* ^ May not need propositional equality here; try in HoTT *)

(* --- Unpacked equiv --- *)

Definition pltv (T : Type) (n : nat) (pl : { l : list T & list_to_t_index T l = n }) : vector T n :=
  @eq_rect 
    nat
    (list_to_t_index T (projT1 pl))
    (vector T)
    (list_rect
      (fun l0 : list T => vector T (list_to_t_index T l0))
      (nilV T)
      (fun (a : T) (l0 : list T) (IHl : vector T (list_to_t_index T l0)) => 
         consV T a (list_to_t_index T l0) IHl)
      (projT1 pl))
    n
    (projT2 pl).  

Definition vtl (T : Type) (n : nat) (v : vector T n) :=
  VectorDef.t_rect 
    T
    (fun (n0 : nat) (_ : vector T n0) => {l : list T & list_to_t_index T l = n0})
    (existT (fun l : list T => list_to_t_index T l = 0) nil eq_refl)
    (fun (h : T) (n0 : nat) (_ : vector T n0) (IHv : {l : list T & list_to_t_index T l = n0}) =>
      existT 
        (fun l : list T => list_to_t_index T l = S n0) 
        (h :: projT1 IHv)
        (eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl (projT2 IHv)))
    n
    v.

(*
 * Will want to simplify these, but here's the gist
 * (some help from Jason Gross: https://github.com/uwplse/ornamental-search/issues/39)
 *)
Lemma pltv_section:
  forall T n pl, vtl T n (pltv T n pl) = pl.
Proof.
  intros T. assert (forall (l : list T), vtl T (list_to_t_index T l) (pltv T (list_to_t_index T l) (existT _ l eq_refl)) = existT _ l eq_refl).
  - induction l; intros.
    + reflexivity.
    + unfold pltv in IHl. unfold pltv. simpl in *. rewrite IHl. reflexivity.
  - intros n pl. induction pl. specialize (H x). 
    unfold pltv. simpl. rewrite <- p. apply H.
Defined.

(* ^ Term is so ugly, which may get in the way of generating; think about what lemmas we need *)

Lemma pltv_retraction:
  forall T n v, pltv T n (vtl T n v) = v.
Proof.
  induction v.
  - reflexivity.
  - unfold pltv. simpl. generalize dependent (vtl T n v). intros s H.
    induction s. simpl. subst. simpl. reflexivity.
Defined.

Program Definition plist_rect : (* Give the list proof motive a dummy eq proof at eq_refl *)
  forall (A : Type) (P : forall n : nat, { l : list A & list_to_t_index A l = n } -> Type),
    P 0 (existT _ (@nil A) eq_refl) ->
    (forall (h : A) (n : nat) (t : { l : list A & list_to_t_index A l = n }), P n t -> P (S n) (existT _ (@cons A h (projT1 t)) (f_equal S (projT2 t)))) ->
    forall (n : nat) (t : { l : list A & list_to_t_index A l = n }), P n t.
Proof.
  intros. assert (forall (l : list A), P (list_to_t_index A l) (existT _ l eq_refl)).
  - induction l. (* Proof about lists and their lengths *)
    + apply X.
    + apply (X0 a (list_to_t_index A l) (existT _ l eq_refl) IHl).
  - induction t. rewrite <- p. apply X1. (* Rewrite to be the nice length *)
Defined.

Program Definition plist_easy_rect :
  forall (A : Type) (P : list A -> Type) (n : nat) (Q : forall (n : nat) (l : list A), P l -> Type),
    forall (list_proof : forall (l : list A), P l), (* list proof *)
    forall (length_proof : forall (l : list A), list_to_t_index A l = n -> Q n l (list_proof l)), (* length proof *)
    forall (pl : { l : list A & list_to_t_index A l = n }),
      Q n (projT1 pl) (list_proof (projT1 pl)). (* packed proof *)
Proof.
  intros A P n Q list_proof length_proof pl.
  apply (length_proof (projT1 pl) (projT2 pl)).
Defined.

(*
 * From Example.v:
 *)
Module hs_to_coq'.

(* From:
 * https://github.com/antalsz/hs-to-coq/blob/master/base/GHC/List.v
 *)
Definition zip {a} {b} : list a -> list b -> list (a * b)%type :=
  fix zip arg_0__ arg_1__
        := match arg_0__, arg_1__ with
           | nil, _bs => nil
           | _as, nil => nil
           | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
  end.

(* From:
 * https://github.com/antalsz/hs-to-coq/blob/master/core-semantics-no-values/semantics.v
 *)
Fixpoint zip_with {A} {B} {C} (f : A -> B -> C) (s : list A) (t : list B) : list C :=
  match s , t with
    | a :: s' , b :: t' => f a b :: zip_with f s' t'
    | _       , _       => nil
  end.

From Coq Require Import ssreflect ssrbool ssrfun.
Import EqNotations.

Theorem zip_with_is_zip {A} {B} :
  zip_with (@pair A B) =2 zip.
Proof. by elim => [|a s IH] [|b t] //=; rewrite IH. Qed.

End hs_to_coq'.

Preprocess Module hs_to_coq' as hs_to_coq.

Check and_rect.

Module Elims.

(*
 * Attempt to find a good eliminator.
 * This is tricky because dependent rewriting breaks things when we lift later.
 *)
Theorem packed_list_rect_eta:
  forall (A : Type) (n : nat) (P : { l : list A & list_to_t_index A l = n } -> Type),
    (forall (l : list A) (H : list_to_t_index A l = n), P (existT _ l H)) ->
    forall pl, P (existT _ (projT1 pl) (projT2 pl)).
Proof.
  intros A n P pf pl. apply (pf (projT1 pl) (projT2 pl)).
Defined.

Theorem packed_list_rect:
  forall (A : Type) (n : nat) (P : { l : list A & list_to_t_index A l = n } -> Type),
    (forall (l : list A) (H : list_to_t_index A l = n), P (existT _ l H)) ->
    forall pl, P pl.
Proof.
  intros A n P pf pl. induction pl. apply (packed_list_rect_eta A n P pf (existT _ x p)).
Defined.

End Elims.

Preprocess Module Elims as Elims' { opaque list_to_t_index sigT_rect }.

Lemma zip_index':
  forall {a} {b} (l1 : list a) (l2 : list b),
    list_to_t_index _ l1 = list_to_t_index _ l2 ->
    list_to_t_index _ (hs_to_coq.zip a b l1 l2) = list_to_t_index _ l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Lemma zip_index_n':
  forall {a} {b} (n : nat) (l1 : list a) (l2 : list b),
    list_to_t_index _ l1 = n ->
    list_to_t_index _ l2 = n ->
    list_to_t_index _ (hs_to_coq.zip a b l1 l2) = n.
Proof.
  intros. rewrite <- H. apply zip_index'. eapply eq_trans; eauto. 
Defined.

Preprocess zip_index' as zip_index.
Preprocess zip_index_n' as zip_index_n.

Program Definition zip_pl:
  forall {a} {b} {n : nat},
    { l1 : list a & list_to_t_index a l1 = n } ->
    { l2 : list b & list_to_t_index b l2 = n } ->
    { l3 : list (a * b) & list_to_t_index (a * b) l3 = n }.
Proof.
  intros a b n pl1. apply Elims'.packed_list_rect with (A := a) (n := n).
  - intros l H pl2. 
    (* list function: *)
    exists (hs_to_coq.zip a b l (projT1 pl2)). 
    (* length invariant: *)
    apply zip_index_n; auto. apply (projT2 pl2).
  - apply pl1. 
Defined.

Lemma zip_with_index':
  forall {A} {B} {C} f (l1 : list A) (l2 : list B),
    list_to_t_index _ l1 = list_to_t_index _ l2 ->
    list_to_t_index _ (hs_to_coq.zip_with A B C f l1 l2) = list_to_t_index _ l1.
Proof.
  induction l1, l2; intros; auto; inversion H.
  simpl. f_equal. auto.
Defined.

Lemma zip_with_index_n':
  forall {A} {B} {C} f (n : nat) (l1 : list A) (l2 : list B),
    list_to_t_index _ l1 = n ->
    list_to_t_index _ l2 = n ->
    list_to_t_index _ (hs_to_coq.zip_with A B C f l1 l2) = n.
Proof.
  intros. rewrite <- H. apply zip_with_index'. eapply eq_trans; eauto.
Defined.

Preprocess zip_with_index' as zip_with_index.
Preprocess zip_with_index_n' as zip_with_index_n.

Program Definition zip_with_pl:
  forall {A} {B} {C} (f : A -> B -> C) {n : nat},
    { l1 : list A & list_to_t_index A l1 = n } ->
    { l2 : list B & list_to_t_index B l2 = n } ->
    { l3 : list C & list_to_t_index C l3 = n }.
Proof.
  intros A B C f n pl1. apply Elims'.packed_list_rect with (A := A) (n := n).
  - intros l H pl2.
    (* list function: *)
    exists (hs_to_coq.zip_with A B C f l (projT1 pl2)).
    (* length invariant: *)
    apply zip_with_index_n; auto. apply (projT2 pl2).
  - apply pl1.
Defined.

From Coq Require Import Eqdep_dec Arith.

Lemma zip_with_is_zip_pl :
  forall {A} {B} {n} (pl1 : { l1 : list A & list_to_t_index A l1 = n }) (pl2 : { l2 : list B & list_to_t_index B l2 = n }),
    zip_with_pl pair pl1 pl2 = zip_pl pl1 pl2.
Proof.
  intros A B n pl1. 
  apply Elims'.packed_list_rect with (A := A) (n := n) (P := fun (pl1 : {l1 : list A & list_to_t_index A l1 = n}) => forall pl2 : {l2 : list B & list_to_t_index B l2 = n}, zip_with_pl pair pl1 pl2 = zip_pl pl1 pl2). 
  intros l  H pl2.
  (* list proof: *)
  apply EqdepFacts.eq_sigT_sig_eq.
  exists (hs_to_coq.zip_with_is_zip A B l (projT1 pl2)).
  (* length invariant: *)
  apply (UIP_dec Nat.eq_dec). (* <-- Still not relational UIP, but can deal with later *)
Defined.

(* We can lift from that to sigT vect: *)

Print Elims'.packed_list_rect_eta.
Lift list vector in Elims'.packed_list_rect_eta as packed_vector_rect_eta.
Check packed_vector_rect_eta.
Print Elims'.packed_list_rect.

Definition foo (A : Type) (n : nat) (P : {l : list A & list_to_t_index A l = n} -> Type) (pl0 : {l : list A & list_to_t_index A l = n}) := 
  P pl0.

Print foo.

Lift list vector in foo as bar.
Print bar.

(*
: forall (A : Type) (n : nat) (P : {l : {H : nat & vector A H} & projT1 l = n} -> Type),
    (forall (l : {H : nat & vector A H}) (H : projT1 l = n),
       P (existT _ (existT _ (projT1 l) (projT2 l)) H)) ->
       forall pl,
         P (existT _ (existT _ (projT1 (projT1 pl)) (projT2 (projT1 pl))) (projT2 pl)).
*)

(* 
  (fun pl0 : {l : list A & list_to_t_index A l = n} => P pl0) *)
(* TODO what is broken here? What do we need? Something with eta... *)
Definition packed_vector_rect :=
fun (A : Type) (n : nat) (P : {l : {H : nat & vector A H} & projT1 l = n} -> Type)
    pf (pl: {l : {H : nat & vector A H} & projT1 l = n}) =>
 @sigT_rect
   {H : nat & vector A H} (* A *)
   (fun l : {H : nat & vector A H} => projT1 l = n) (* Q *)
   (fun pl : {l : {H : nat & vector A H} & projT1 l = n} => P (existT _ (existT _ (projT1 (projT1 pl)) (projT2 (projT1 pl))) (projT2 pl))) (* P0 *)
   (fun (x : {H : nat & vector A H}) (p : projT1 x = n) =>
     packed_vector_rect_eta (* want: P0 (existT Q x p) <=> P (existT Q x p)*)
       A (* have: P (existT _ (existT _ (projT1 x) (projT2 x)) p) *)
       n 
       P 
       pf
       (existT _ (existT _ (projT1 x) (projT2 x)) p)) 
   pl.

Check Elims'.packed_list_rect.
Check packed_vector_rect.

Print packed_vector_rect_eta.


Definition packed_vector_rect_eta' := 
fun (A : Type) (n : nat)
  (P : {l : {H : nat & vector A H} & projT1 l = n} -> Type)
  (pf : forall (l : {H : nat & vector A H}) (H : projT1 l = n),
          P (existT _ l H))
  (pl : {l : {H : nat & vector A H} & projT1 l = n}) =>
  pf (projT1 pl) (projT2 pl).

Definition packed_vector_rect' :=
fun (A : Type) (n : nat) (P : {l : {H : nat & vector A H} & projT1 l = n} -> Type)
    pf (pl: {l : {H : nat & vector A H} & projT1 l = n}) =>
 @sigT_rect
   {H : nat & vector A H} (* A *)
   (fun l : {H : nat & vector A H} => projT1 l = n) (* Q *)
   (fun pl : {l : {H : nat & vector A H} & projT1 l = n} => P pl) (* P0 *)
   (fun (x : {H : nat & vector A H}) (p : projT1 x = n) =>
     packed_vector_rect_eta' (* want: P0 (existT Q x p) <=> P (existT Q x p)*)
       A (* have: P (existT _ (existT _ (projT1 x) (projT2 x)) p) *)
       n 
       P 
       pf
       (existT _ x p)) 
   pl.


Definition packed_vector_rect :=
fun (A : Type) (n : nat) (P : {l : {H : nat & vector A H} & projT1 l = n} -> Type)
    pf (pl: {{H : nat & vector A H} & projT1 l = n}) =>
 @sigT_rect {H : nat & vector A H} (fun l : {H : nat & vector A H} => projT1 l = n)
 (fun pl : {l : {H : nat & vector A H} & projT1 l = n} => P pl)
 (fun (x : {H : nat & vector A H}) (p : projT1 x = n) =>
  packed_vector_rect_eta A n P pf
    (existT (fun l : {H : nat & vector A H} => projT1 l = n)
       (existT (fun H : nat => vector A H) (projT1 x) (projT2 x)) p)) pl.



Lift list vector in Elims'.packed_list_rect as packed_vector_rect.
Check packed_vector_rect_eta.
Print Elims'.packed_list_rect.

Lift list vector in Elims'.packed_list_rect as packed_vector_rect.
(* TODO probably missing some repacking somehow ^ *)
Lift list vector in zip_with_is_zip_pl as zip_with_is_zip_pv { opaque Nat.eq_dec UIP_dec EqdepFacts.eq_sigT_sig_eq }.

(*
 * Not bad, but could be simpler.
 *)

(* ^ TODO so we can implement that transport, but then the question becomes how to interface
   this and separate proofs over lists and proofs about their lengths, and automatically
   combine them into this form *)

(* --- What about splitting constructors? --- *)

Inductive list2 (T : Type) :=
| nil2 : list2 T
| cons2 : T -> list2 T -> list2 T
| never : False -> list2 T.

Program Definition list_to_list2 : forall (T : Type) (l : list T), list2 T.
Proof.
  intros. induction l.
  - apply nil2.
  - apply cons2.
    + apply a.
    + apply IHl.
Defined.

Program Definition list2_to_list : forall (T : Type) (l : list2 T), list T.
Proof.
  intros. induction l.
  - apply nil.
  - apply cons.
    + apply t.
    + apply IHl.
  - inversion f.
Defined.

Theorem list_to_list2_section:
  forall (T : Type) (l : list T), list2_to_list T (list_to_list2 T l) = l.
Proof.
  intros. induction l.
  - auto.
  - simpl. rewrite IHl. auto.
Defined.

Theorem list_to_list2_retraction:
  forall (T : Type) (l : list2 T), list_to_list2 T (list2_to_list T l) = l.
Proof.
  intros. induction l.
  - auto.
  - simpl. rewrite IHl. auto.
  - inversion f.
Defined.

Lemma list2_list_rect :
  forall (A : Type) (P : list2 A -> Type),
    P (nil2 A) ->
    (forall (a : A) (l : list2 A) (IH : P l),
      P (cons2 A a l)) ->
    forall (l : list2 A), P l.
Proof.
  intros A P pnil2 pcons2 l. induction l.
  - apply pnil2.
  - apply pcons2. apply IHl.
  - inversion f.
Defined.

Definition transport_nil:
  forall (A : Type) (P : list2 A -> Type),
    P (list_to_list2 A nil) ->
    P (nil2 A).
Proof.
  intros. apply X.
Defined.

Definition transport_nil_inv:
  forall (A : Type) (P : list2 A -> Type),
    P (nil2 A) ->
    P (list_to_list2 A nil).
Proof.
  intros. apply X.
Defined.

Definition transport_cons:
  forall (A : Type) (P : list2 A -> Type) (l : list2 A) (a : A),
    P (list_to_list2 A (cons a (list2_to_list A l))) ->
    P (cons2 A a l).
Proof.
  intros. simpl in X. rewrite list_to_list2_retraction in X. apply X.
Defined.

Definition transport_cons_inv:
  forall (A : Type) (P : list2 A -> Type) (l : list2 A) (a : A),
    P (cons2 A a l) ->
    P (list_to_list2 A (cons a (list2_to_list A l))).
Proof.
  intros. simpl. rewrite list_to_list2_retraction. apply X.
Defined.

(*
 * Definitely follows patterns from the equivalences, but still not sure
 * exactly what is happening here.
 *)

(* --- Let's see --- *)

Inductive Foo : nat -> Type :=
| f : forall (n : nat), Foo n.

Inductive Bar : nat -> Type :=
| f1 : Bar 0
| f2 : forall (n : nat), Bar n -> Bar (S n).

Program Definition Foo_to_Bar : forall (n : nat), Foo n -> Bar n.
Proof.
  intros. induction H.
  - induction n.
    + apply f1.
    + apply f2. apply IHn.
Defined.

Program Definition Bar_to_Foo : forall (n : nat), Bar n -> Foo n.
Proof.
  intros. apply f.
Defined.

Theorem Foo_to_Bar_section:
  forall (n : nat) (f : Foo n), Bar_to_Foo n (Foo_to_Bar n f) = f.
Proof.
  intros. induction f0.
  - induction n.
    + auto.
    + auto.
Defined.

Theorem Foo_to_Bar_retraction:
  forall (n : nat) (b : Bar n), Foo_to_Bar n (Bar_to_Foo n b) = b.
Proof.
  intros. induction b.
  - auto.
  - simpl. simpl in IHb. rewrite IHb. auto.
Defined.

Check Foo_rect.

Lemma Bar_nat_rect:
  forall (n : nat) (b : Bar n),
    nat_rect Bar f1 (fun (n : nat) (IHn : Bar n) => f2 n IHn) n = b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. rewrite IHb. reflexivity.
Defined.

Lemma Bar_Foo_rect:
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (nat_rect Bar f1 (fun _ IHn => f2 _ IHn) n)) -> (* <-- looks like repacking *)
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b. rewrite <- Bar_nat_rect. apply pf0. 
Defined.

(* So repacking really is dependent elimination! *)

Lemma Foo_Bar_rect:
  forall P : forall n : nat, Foo n -> Type,
    P 0 (f 0) ->
    (forall (n : nat) (f0 : Foo n), P n (f n) -> P (S n) (f (S n))) ->
    forall (n : nat) (b : Foo n), P n (f n).
Proof.
  intros P pf1 pf2 n f. induction f.
  - induction n.
    + apply pf1.
    + apply (pf2 n (f n)). apply IHn.
Defined.

(* Also note how each of these corresponds to Foo_to_Bar and Bar_to_Foo, respectively. *)



