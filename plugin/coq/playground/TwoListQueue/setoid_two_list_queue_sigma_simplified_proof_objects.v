Require Import List Bool.
Import ListNotations.
Import Equivalence.
Require Import Morphisms.
Require Import Specif.
Require Import StructTact.StructTactics.
Require Import Coq.Classes.SetoidClass.
Module TwoListQueue.

Definition raw_queue (A : Type) := (list A * list A) % type.

Definition app_rev {A : Type} (q : raw_queue A) : list A :=
  match q with
  | (f, b) => f ++ (rev b)
  end.

Definition raw_equiv {A : Type} (q1 q2 : raw_queue A) : Prop :=
  app_rev q1 = app_rev q2.

(* https://www.cis.upenn.edu/~plclub/blog/2020-05-15-Rewriting-in-Coq/
https://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
 *)
#[export] Instance raw_equiv_refl {A : Type} : Reflexive (@raw_equiv A).
Proof.
  unfold Reflexive.
  reflexivity.
Qed.

#[export] Instance raw_equiv_sym {A : Type} : Symmetric (@raw_equiv A).
Proof.
  unfold Symmetric.
  intros.
  symmetry.
  apply H.
Qed.

#[export] Instance raw_equiv_trans {A : Type} : Transitive (@raw_equiv A).
Proof.
  unfold Transitive.
  intros.
  unfold raw_equiv.
  rewrite H.
  apply H0.
Qed.

#[export] Instance raw_equiv_equiv {A : Type} : Equivalence (@raw_equiv A).
Proof.
  split;
  [apply raw_equiv_refl
  |apply raw_equiv_sym
  |apply raw_equiv_trans].
Qed.

#[export] Instance raw_tlq_setoid {A : Type} : Setoid (@raw_queue A) :=
  {equiv := (@raw_equiv A)
   ;setoid_equiv := raw_equiv_equiv
  }.
  
Definition rep_ok {A : Type} (q : raw_queue A) : Prop :=
  match q with
  | (f, b) => f = [] -> b = []
  end.

Theorem rep_ok_contradiction : forall (A : Type) (a : A) (l : list A),
    rep_ok ([], a :: l) -> False.
Proof.
  intros.
  simpl in H.
  assert (@nil A = []).
  reflexivity.
  apply H in H0.
  discriminate.
Qed.

Ltac bad_rep_ok H := apply rep_ok_contradiction in H; contradiction.

Definition raw_empty {A : Type} : raw_queue A := ([],[]).
Definition raw_is_empty {A : Type} (q : raw_queue A) : bool :=
  match q with
  | ([], b) => true
  | (_::_, b) => false
  end.

Definition raw_enq {A : Type} (a : A) (q : raw_queue A) : raw_queue A :=
  match q with
  | ([], b) => ([a], b)
  | (h::t, b) => (h::t, a::b)
  end.

Definition raw_deq {A : Type} (q : raw_queue A) : raw_queue A :=
  match q with
  | ([], b) => ([], b)
  | (h::[], b) => (List.rev b, [])
  | (h::t, b) => (t, b)
  end.

Definition raw_peek {A : Type} (q : raw_queue A) : option A :=
  match q with
  | ([], b) => None
  | (h::t, b) => Some h
  end.

Theorem rep_ok_empty : forall (A : Type),
    rep_ok (@raw_empty A).
Proof.
  intros.
  simpl.
  trivial.
Qed.

Theorem rep_ok_enq : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> rep_ok (raw_enq a q).
Proof.
  intros.
  unfold rep_ok.
  destruct q.
  simpl.
  destruct l.
  - intros.
    unfold rep_ok in H.
    apply H.
    reflexivity.
  - intros.
    discriminate.
Qed.


Theorem rep_ok_deq : forall (A : Type) (q : raw_queue A),
    rep_ok q -> rep_ok (raw_deq q).
Proof.
  intros.
  destruct q.
  destruct l.
  - apply H.
  - simpl.
    destruct l.
    + simpl.
      intros.
      reflexivity.
    + simpl.
      intros.
      discriminate.
Qed.

Theorem raw_empty_is_empty : forall (A : Type),
    raw_is_empty (@raw_empty A) = true.
Proof.
  reflexivity.
Qed.

Lemma raw_enq_not_empty_base : forall (A : Type) (a : A) (l0 : list A) (H : rep_ok ([], l0)),
  raw_is_empty (raw_enq a ([], l0)) = false.
Proof.
  intros. reflexivity.
Qed.

Print raw_enq_not_empty_base.

Theorem raw_enq_not_empty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty (raw_enq a q) = false.
Proof.
  intros.
  induction q as [l l0].
  induction l.
  - apply (raw_enq_not_empty_base _ _ _ H).
  - reflexivity.
Qed.

Print raw_enq_not_empty.

Definition raw_enq_not_empty2 : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty (raw_enq a q) = false :=
fun (A : Type) (a : A) (q : raw_queue A)
  (H : rep_ok q) =>
prod_ind
  (fun q0 : list A * list A =>
   rep_ok q0 -> raw_is_empty (raw_enq a q0) = false)
  (fun (l l0 : list A) (H0 : rep_ok (l, l0)) =>
   list_ind
     (fun l1 : list A =>
      rep_ok (l1, l0) ->
      raw_is_empty (raw_enq a (l1, l0)) = false)
     (fun _ : rep_ok ([], l0) => eq_refl)
     (fun (a0 : A) (l1 : list A)
        (_ : rep_ok (l1, l0) ->
             raw_is_empty (raw_enq a (l1, l0)) = false)
        (_ : rep_ok (a0 :: l1, l0)) => eq_refl) l H0)
  q H.
  

Theorem raw_no_peek_empty : forall (A : Type),
  raw_peek (@raw_empty A) = None.
Proof.
  reflexivity.
Qed.

(*
Lemma is_empty_implies_empty : forall (A : Type) (q : queue A),
    rep_ok q -> is_empty q = true -> q = empty.
Proof.
  intros.
  destruct q.
  destruct l.
  - simpl in H.
    assert (l0 = []).
    auto.
    rewrite -> H1.
    reflexivity.
  - simpl in H0.
    discriminate.
Qed.
*)

Theorem raw_peek_singleton : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = true -> raw_peek (raw_enq a q) = Some a.
Proof.
  intros.
  destruct q.
  simpl.
  destruct l.
  - reflexivity.
  - discriminate.
Qed.

Lemma raw_is_empty_not_empty : forall (A : Type) (a : A) (l0 l1 : list A) (T : Type),
    raw_is_empty (a :: l0, l1) = true -> T.
Proof.
  intros.
  discriminate.
Qed.

Definition raw_empty_peek_singleton {A : Type} (a : A) (q : raw_queue A) := 
  raw_is_empty q = true -> raw_peek (raw_enq a q) = Some a.

Definition raw_peek_singleton2 : forall (A : Type) (a : A) (q : raw_queue A),
       rep_ok q ->
       raw_is_empty q = true -> raw_peek (raw_enq a q) = Some a :=
fun (A : Type) (a : A) (q : raw_queue A) 
  (H : rep_ok q) (H0 : raw_is_empty q = true) =>
prod_ind 
  (fun q0 : list A * list A =>
     raw_empty_peek_singleton a q0) (**P'*)
  (fun (a0 b : list A) (H2 : raw_is_empty (a0, b) = true) =>
   (list_ind
     (fun a1 : list A =>
       raw_empty_peek_singleton a (a1, b)) (**P*)
     (fun (_ : raw_is_empty ([], b) = true) =>
        eq_refl) (**P nil*)
     (fun (a1 : A) (l : list A) (**P l -> P a1::l*)
        (_ : raw_empty_peek_singleton a (l, b))
        (H4 : raw_is_empty (a1 :: l, b) = true) =>
          raw_is_empty_not_empty
            A
            a1
            l
            b
            (raw_peek (a1 :: l, a :: b) = Some a)
            H4)
     a0) (**list input*)
    H2) (**forall a0 b, P (a0, b)*)
  q (**type prod (list A) (list A)*)
  H0.

Theorem raw_peek_enq_nonempty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = false -> raw_peek (raw_enq a q) = raw_peek q.
Proof.
  intros.
  destruct q.
  simpl.
  destruct l.
  - discriminate.
  - reflexivity.
Qed.

(*
Theorem deq_singleton : forall (A : Type) (a : A) (q : queue A),
    rep_ok q -> is_empty q = true -> deq (enq a q) = q.
Proof.
  intros.
  apply is_empty_implies_empty in H0.
  rewrite H0.
  reflexivity.
  apply H.
Qed.
 *)

Theorem raw_deq_singleton : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_empty q = true -> raw_equiv (raw_deq (raw_enq a q)) q.
Proof.
  intros.
  unfold raw_equiv.
  destruct q.
  destruct l.
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - discriminate.
Qed.

Print raw_deq_singleton.

Lemma app_rev_lem : forall (A : Type) (a a0 a1 : A) (l0 : list A), 
  app_rev (raw_deq (raw_enq a ([a0], a1 :: l0))) =
  app_rev (raw_enq a (raw_deq ([a0], a1 :: l0))).
Proof.
  intros.
  simpl.
  induction (rev l0 ++ [a1]).
  - reflexivity.
  - rewrite app_nil_r.
    reflexivity.
Qed.

Definition raw_is_nonempty {A : Type} (q : raw_queue A)
 := raw_is_empty q = false.

Definition queue_ok {A : Type} (a : A) (q : raw_queue A) :=
  raw_equiv (raw_deq (raw_enq a q)) (raw_enq a (raw_deq q)).

Definition rep_ok_nonemp_q_ok {A : Type} (a : A) (q : raw_queue A) :=
  rep_ok q -> raw_is_nonempty q -> queue_ok a q.

Theorem raw_deq_enq_nonempty : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok_nonemp_q_ok a q.
Proof.
  intros.
  induction q as [l l0].
  induction l; try discriminate.
  unfold rep_ok_nonemp_q_ok.
  intros.
  induction l; try reflexivity.
  induction l0; try reflexivity.
  simpl.
  apply app_rev_lem.
Qed.
  
Print raw_deq_enq_nonempty.

Check prod_ind.

Definition raw_deq_enq_nonempty3 : forall (A : Type) (a : A) (q : raw_queue A),
    raw_is_nonempty q -> queue_ok a q
  :=
fun (A : Type) (a : A) (q : raw_queue A) =>
  prod_ind
    (fun q0 : list A * list A =>
       raw_is_nonempty q0 -> queue_ok a q0)
    (fun l l0 : list A =>
       list_ind
         (fun l1 : list A =>
           raw_is_nonempty (l1, l0) -> queue_ok a (l1, l0))
         (fun (H0 : raw_is_nonempty ([], l0)) =>
           False_ind
             (queue_ok a ([], l0))
             (eq_ind
                (raw_is_empty ([], l0))
                (fun e : bool =>
                   if e then True else False)
                I
                false
                H0))
         (fun (a0 : A)
              (l1 : list A)
              (IHl : _)
              (H0 : raw_is_nonempty (a0 :: l1, l0)) =>
            list_ind
              (fun l2 : list A =>
                 queue_ok a (a0 :: l2, l0))
              (list_ind
                 (fun l2 : list A =>
                    queue_ok a ([a0], l2))
                 eq_refl
                 (fun (a1: A) (l2 : list A) _ =>
                    app_rev_lem
                      A
                      a
                      a0
                      a1
                      l2)
                 l0)
              (fun (a1 : A) (l2 : list A) _
         => eq_refl) l1) l) q.

Definition raw_deq_enq_nonempty2 :
  forall (A : Type) (a : A) (q : raw_queue A),
       rep_ok q ->
       raw_is_empty q = false ->
       raw_equiv (raw_deq (raw_enq a q))
         (raw_enq a (raw_deq q)) :=
  fun (A : Type) (a : A) (q : raw_queue A)
  (H : rep_ok q) (H0 : raw_is_empty q = false) =>
prod_ind
  (fun q0 : list A * list A =>
     rep_ok q0 ->
     raw_is_empty q0 = false ->
     app_rev (raw_deq (raw_enq a q0)) =
     app_rev (raw_enq a (raw_deq q0)))
  (fun
     (l l0 : list A)
     (H1 : rep_ok (l, l0))
     (H2 : raw_is_empty (l, l0) = false) =>
     list_ind
       (fun l1 : list A =>
         rep_ok (l1, l0) ->
         raw_is_empty (l1, l0) = false ->
         (let (f, b) := raw_deq (raw_enq a (l1, l0)) in
         f ++ rev b) =
         (let (f, b) := raw_enq a (raw_deq (l1, l0)) in
         f ++ rev b))
       (fun
         (_ : rep_ok ([], l0))
         (H4 : raw_is_empty ([], l0) = false) =>
           let H5 : False :=
             eq_ind (raw_is_empty ([], l0))
               (fun e : bool => if e
                                then True
                                else False)
               I
               false
               H4 in
           False_ind
             ((let (f, b) :=
               raw_deq (raw_enq a ([], l0)) in
               f ++ rev b) =
              (let (f, b) :=
               raw_enq a (raw_deq ([], l0)) in
               f ++ rev b))
             H5)
       (fun
         (a0 : A)
         (l1 : list A)
         (IHl :
           rep_ok (l1, l0) ->
           raw_is_empty (l1, l0) = false ->
           (let (f, b) :=
             raw_deq (raw_enq a (l1, l0)) in
             f ++ rev b) =
           (let (f, b) :=
             raw_enq a (raw_deq (l1, l0)) in
             f ++ rev b))
         (H3 : rep_ok (a0 :: l1, l0))
         (H4 : raw_is_empty (a0 :: l1, l0) = false) =>
         list_ind
           (fun l2 : list A =>
             rep_ok (a0 :: l2, l0) ->
             raw_is_empty (a0 :: l2, l0) = false ->
             (rep_ok (l2, l0) ->
             raw_is_empty (l2, l0) = false ->
             (let (f, b) :=
                raw_deq (raw_enq a (l2, l0)) in
                f ++ rev b) =
             (let (f, b) :=
                raw_enq a (raw_deq (l2, l0)) in
                f ++ rev b)) ->
           (let (f, b) :=
              match l2 with
              | [] => (rev l0 ++ [a], [])
              | _ :: _ => (l2, a :: l0)
              end in
              f ++ rev b) =
              (let (f, b) :=
                raw_enq a
                match l2 with
                | [] => (rev l0, [])
                | _ :: _ => (l2, l0)
                end in
                f ++ rev b))
           (fun (H5 : rep_ok ([a0], l0))
           (H6 : raw_is_empty ([a0], l0) = false)
           (IHl0 : rep_ok ([], l0) ->
                   raw_is_empty ([], l0) = false ->
                   (let (f, b) :=
                      raw_deq (raw_enq a ([], l0)) in
                    f ++ rev b) =
                   (let (f, b) :=
                      raw_enq a (raw_deq ([], l0)) in
                    f ++ rev b)) =>
         list_ind
           (fun l2 : list A =>
            rep_ok ([a0], l2) ->
            raw_is_empty ([a0], l2) = false ->
            (rep_ok ([], l2) ->
             raw_is_empty ([], l2) = false ->
             (let (f, b) :=
                raw_deq (raw_enq a ([], l2)) in
              f ++ rev b) =
             (let (f, b) :=
                raw_enq a (raw_deq ([], l2)) in
              f ++ rev b)) ->
            (rev l2 ++ [a]) ++ [] =
            (let (f, b) :=
               match rev l2 with
               | [] => ([a], [])
               | h :: t => (h :: t, [a])
               end in
             f ++ rev b))
           (fun (_ : rep_ok ([a0], []))
              (_ : raw_is_empty ([a0], []) = false)
              (_ : rep_ok ([], []) ->
                   raw_is_empty ([], []) = false ->
                   (let (f, b) :=
                      raw_deq (raw_enq a ([], [])) in
                    f ++ rev b) =
                   (let (f, b) :=
                      raw_enq a (raw_deq ([], [])) in
                    f ++ rev b)) => eq_refl)
           (fun (a1 : A) (l2 : list A)
              (_ : rep_ok ([a0], l2) ->
                   raw_is_empty ([a0], l2) = false ->
                   (rep_ok ([], l2) ->
                    raw_is_empty ([], l2) = false ->
                    (let (f, b) :=
                       raw_deq (raw_enq a ([], l2)) in
                     f ++ rev b) =
                    (let (f, b) :=
                       raw_enq a (raw_deq ([], l2)) in
                     f ++ rev b)) ->
                   (rev l2 ++ [a]) ++ [] =
                   (let (f, b) :=
                      match rev l2 with
                      | [] => ([a], [])
                      | h :: t => (h :: t, [a])
                      end in
                    f ++ rev b))
              (_ : rep_ok ([a0], a1 :: l2))
              (_ : raw_is_empty ([a0], a1 :: l2) =
                   false)
              (_ : rep_ok ([], a1 :: l2) ->
                   raw_is_empty ([], a1 :: l2) = false ->
                   (let (f, b) :=
                      raw_deq
                        (raw_enq a ([], a1 :: l2)) in
                    f ++ rev b) =
                   (let (f, b) :=
                      raw_enq a
                        (raw_deq ([], a1 :: l2)) in
                    f ++ rev b)) =>
            let l3 := rev l2 ++ [a1] in
            list_ind
              (fun l4 : list A =>
               (l4 ++ [a]) ++ [] =
               (let (f, b) :=
                  match l4 with
                  | [] => ([a], [])
                  | h :: t => (h :: t, [a])
                  end in
                f ++ rev b)) eq_refl
              (fun (a2 : A) (l4 : list A)
                 (_ : (l4 ++ [a]) ++ [] =
                      (let (f, b) :=
                         match l4 with
                         | [] => ([a], [])
                         | h :: t => (h :: t, [a])
                         end in
                       f ++ rev b)) =>
               eq_ind_r
                 (fun l5 : list A =>
                  l5 = (a2 :: l4) ++ rev [a]) eq_refl
                 (app_nil_r ((a2 :: l4) ++ [a]))) l3)
           l0 H5 H6 IHl0)
        (fun (a1 : A) (l2 : list A)
           (_ : rep_ok (a0 :: l2, l0) ->
                raw_is_empty (a0 :: l2, l0) = false ->
                (rep_ok (l2, l0) ->
                 raw_is_empty (l2, l0) = false ->
                 (let (f, b) :=
                    raw_deq (raw_enq a (l2, l0)) in
                  f ++ rev b) =
                 (let (f, b) :=
                    raw_enq a (raw_deq (l2, l0)) in
                  f ++ rev b)) ->
                (let (f, b) :=
                   match l2 with
                   | [] => (rev l0 ++ [a], [])
                   | _ :: _ => (l2, a :: l0)
                   end in
                 f ++ rev b) =
                (let (f, b) :=
                   raw_enq a
                     match l2 with
                     | [] => (rev l0, [])
                     | _ :: _ => (l2, l0)
                     end in
                 f ++ rev b))
           (_ : rep_ok (a0 :: a1 :: l2, l0))
           (_ : raw_is_empty (a0 :: a1 :: l2, l0) =
                false)
           (_ : rep_ok (a1 :: l2, l0) ->
                raw_is_empty (a1 :: l2, l0) = false ->
                (let (f, b) :=
                   raw_deq (raw_enq a (a1 :: l2, l0)) in
                 f ++ rev b) =
                (let (f, b) :=
                   raw_enq a (raw_deq (a1 :: l2, l0)) in
                 f ++ rev b)) => eq_refl) l1 H3 H4 IHl)
     l H1 H2) q H H0.

Inductive reachable {A : Type} : raw_queue A -> Prop :=
| reach_empty : reachable raw_empty
| reach_enq : forall (a : A) (q : raw_queue A), reachable q -> reachable (raw_enq a q)
| reach_deq : forall (q : raw_queue A), reachable q -> reachable (raw_deq q).

Lemma empty_front_reachable {A : Type} : forall (l : list A),
    reachable (l, []).
Proof.
  intros.
  remember l as l_orig.
  destruct l.
  - rewrite Heql_orig.
    apply reach_empty.
  - rewrite <- (rev_involutive l_orig).
    apply (reach_deq ([a], rev l_orig)).
    induction (rev l_orig).
    + apply (reach_enq a raw_empty).
      apply (reach_empty).
    + apply (reach_enq a0 ([a], l0)).
      apply IHl0.
Qed.
  
Lemma rep_ok_reachable {A : Type} : forall (q : raw_queue A),
    rep_ok q -> reachable q.
Proof.
  intros.
  destruct q.    
  destruct l.
  - destruct l0.
    + apply reach_empty.
    + bad_rep_ok H.
  - induction l0.
    + apply empty_front_reachable.
    + apply (reach_enq a0 (a::l, l0)).
      apply IHl0.
      unfold rep_ok.
      intros.
      discriminate.
Qed.

Lemma reachable_rep_ok {A : Type} : forall (q : raw_queue A),
    reachable q -> rep_ok q.
Proof.
  intros.
  induction H.
  - unfold rep_ok.
    unfold raw_empty.
    intros.
    reflexivity.
  - destruct q.
    unfold rep_ok.
    simpl.
    destruct l.
    + intros.
      discriminate.
    + intros.
      discriminate.
  - destruct q.
    destruct l.
    + destruct l0.
      * unfold rep_ok.
        simpl.
        intros.
        reflexivity.
      * bad_rep_ok IHreachable.
    + destruct l.
      * simpl.
        intros.
        reflexivity.
      * simpl.
        intros.
        discriminate.
Qed.
  
Theorem raw_queue_ind {A : Type} : forall (P : raw_queue A -> Prop),
    P raw_empty ->
    (forall (a : A) (q : raw_queue A), (rep_ok q -> P q -> P (raw_enq a q))) ->
    (forall (q : raw_queue A), (rep_ok q -> P q -> P (raw_deq q))) ->
    forall q : raw_queue A, (rep_ok q -> P q).
Proof.
  intros.
  apply rep_ok_reachable in H2.
  induction H2.
  - apply H.
  - apply H0.
    apply reachable_rep_ok.
    apply H2.
    apply IHreachable.
  - apply H1.
    apply reachable_rep_ok.
    apply H2.
    apply IHreachable.
Qed.

Definition size {A : Type} (q : raw_queue A) : nat :=
  let (f,b) := q in
  length f + length b.

Lemma raw_deq_dec {A : Type} : forall (q : raw_queue A),
  raw_is_empty q = false -> S (size (raw_deq q)) = size q.
Proof.
  intros.
  destruct q.
  destruct l.
  - discriminate.
  - destruct l.
    + simpl.
      rewrite rev_length.
      rewrite <- plus_n_O.
      reflexivity.
    + reflexivity.
Qed.
     
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Wf_nat.
(** enqueue q2's elements onto q1*)
Program Fixpoint raw_app {A : Type} (q1 q2 : raw_queue A) {measure (size q2)} : raw_queue A :=
  match (raw_peek q2) with
  | None => q1
  | Some a => raw_app (raw_enq a q1) (raw_deq q2)
  end.
Next Obligation.
  unfold lt.
  rewrite raw_deq_dec.
  - apply le_n.
  - destruct q2.
    destruct l.
    + discriminate.
    + reflexivity.
Qed.

Theorem raw_app_front {A : Type} : forall (q1 q2 : raw_queue A),
  rep_ok q1 -> rep_ok q2 -> raw_is_empty q1 = false -> raw_peek (raw_app q1 q2) = raw_peek q1.
Proof.
  intros.
  apply (raw_queue_ind (fun q : raw_queue A => raw_is_empty q = false -> raw_peek (raw_app q q2) = raw_peek q)).
  - discriminate.
Abort.

(**
Theorem raw_deq_enq_nonempty_queue_ind : forall (A : Type) (a : A) (q : raw_queue A),
    rep_ok q -> raw_is_nonempty q -> queue_ok a q.
Proof.
  intros A a q.
  intros H.
  apply rep_ok_reachable in H.
  induction H.
  - intros.
    discriminate.
  - intros.    
    apply (raw_queue_ind (fun q : raw_queue A => raw_is_nonempty q -> queue_ok a q)).
  
  - intros.
    unfold raw_is_nonempty in H.
    discriminate.
  - intros.
    unfold queue_ok.
    unfold raw_equiv.
    apply rep_ok_reachable in H.
    unfold rep_ok in H.
    unfold raw_is_nonempty in H0.

    
  generalize dependent q.
  unfold rep_ok_nonemp_q_ok.
  unfold queue_ok.
  intros.
  apply raw_queue_ind.
  - unfold raw_equiv.
Abort.
**)  

(** Queue with representation invariant enforced. **)

Definition queue (A : Type) := sig (@rep_ok A) % type.

Definition equiv {A : Type} (q1 q2 : queue A) :=
  raw_equiv (proj1_sig q1) (proj1_sig q2).

#[export] Instance equiv_refl {A : Type} : Reflexive (@equiv A).
Proof.
  intros x.
  apply raw_equiv_refl.
Qed.

#[export] Instance equiv_sym {A : Type} : Symmetric (@equiv A).
Proof.
  unfold Symmetric.
  intros x y.
  apply raw_equiv_sym.
Qed.

#[export] Instance equiv_trans {A : Type} : Transitive (@equiv A).
Proof.
  unfold Transitive.
  unfold equiv.
  intros x y z.
  apply raw_equiv_trans.
Qed.

#[export] Instance equiv_equiv {A : Type} : Equivalence (@equiv A).
Proof.
  split;
  [apply equiv_refl
  |apply equiv_sym
  |apply equiv_trans].
Qed.

#[export] Instance tlq_setoid {A : Type} : Setoid (@queue A) :=
  {equiv := (@equiv A)
   ;setoid_equiv := equiv_equiv
  }.

Definition empty {A : Type} : queue A :=
  (exist rep_ok (@raw_empty A) (@rep_ok_empty A)). 

Definition is_empty {A : Type} (q : queue A) :=
  raw_is_empty (proj1_sig q).

Definition enq {A : Type} (a : A) (q : queue A) :=
  match q with
  | exist _ x p => exist rep_ok (raw_enq a x) (rep_ok_enq A a x p)
  end.

Definition deq {A : Type} (q : queue A) :=
  match q with
  | exist _ x p => exist rep_ok (raw_deq x) (rep_ok_deq A x p)
  end.

Definition peek {A : Type} (q : queue A) :=
  raw_peek (proj1_sig q).

Theorem empty_is_empty : forall (A : Type),
    is_empty (@empty A) = true.
Proof.
  apply raw_empty_is_empty.
Qed.

Theorem enq_not_empty : forall (A : Type) (a : A) (q : queue A),
    is_empty (enq a q) = false.
Proof.
  intros.
  destruct q.
  unfold is_empty.
  simpl.
  apply raw_enq_not_empty.
  apply r.
Qed.

Theorem no_peek_empty : forall (A : Type),
    peek (@empty A) = None.
Proof.
  apply raw_no_peek_empty.
Qed.

Theorem peek_singleton : forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> peek (enq a q) = Some a.
Proof.
  intros.
  induction q.
  simpl.
  unfold peek.
  apply raw_peek_singleton; assumption.
Qed.

Print peek_singleton.

Definition peek_singleton2 :=
  fun
    (A : Type)
    (a : A)
    (q : queue A)
    (H : is_empty q = true) =>
      sig_ind
        (fun q0 : {x : raw_queue A | rep_ok x} =>
          is_empty q0 = true -> peek (enq a q0) = Some a)
        (fun
          (x : raw_queue A)
          (p : rep_ok x)
          (H0 : is_empty (exist rep_ok x p) = true) =>
            raw_peek_singleton
              A
              a
              x
              p
              H0)
        q
        H.

Check sig_ind.

Theorem peek_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    is_empty q = false -> peek (enq a q) = peek q.
Proof.
  intros.
  destruct q.
  simpl.
  unfold peek.
  apply raw_peek_enq_nonempty; assumption.
Qed.

Theorem deq_singleton : forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> equiv (deq (enq a q)) q.
Proof.
  intros.
  destruct q.
  simpl.
  apply raw_deq_singleton; assumption.
Qed.

Theorem deq_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    is_empty q = false -> equiv (deq (enq a q)) (enq a (deq q)).
Proof.
  intros.
  destruct q.
  simpl.
  apply raw_deq_enq_nonempty; assumption.
Qed.

Lemma rev_reduce : forall (A : Type) (y : A) (lst : list A),
  lst <> nil -> rev lst = (last lst y) :: (rev (removelast lst)).
Proof.
  intros. induction lst as [ | h t IH].
   - contradiction.
   - simpl. destruct t.
     * auto.
     * rewrite IH. auto. discriminate.
Qed.

#[export] Instance enq_Proper {A : Type} (a : A) : Proper (equiv ==> equiv) (enq a).
Proof.
  intros q q' H.
  unfold equiv.
  destruct q, q'.
  simpl.
  destruct x, x0.
  simpl.
  unfold equiv in H.
  unfold raw_equiv in H.
  simpl in H.
  destruct l, l1; unfold raw_equiv; simpl in H; simpl.
  - f_equal.
    auto.
  - apply (f_equal (@rev A)) in H.
    rewrite rev_involutive in H.
    rewrite H in r.
    rewrite rev_reduce with (y := a) in r.
    bad_rep_ok r.
    discriminate.
  - apply (f_equal (@rev A)) in H.
    rewrite rev_involutive in H.
    rewrite <- H in r0.
    rewrite rev_reduce with (y := a) in r0.
    bad_rep_ok r0.
    discriminate.
  - repeat (rewrite app_assoc).
    rewrite app_comm_cons.
    rewrite H.
    reflexivity.
Qed.    

(**  
  destruct l, l0.
  - destruct l1.
    + destruct l2.
      * reflexivity.
      * apply rep_ok_contradiction in r0.
        contradiction.
    + discriminate.
  - destruct l1.
    + destruct l2.
      * apply rep_ok_contradiction in r.
        contradiction.
      * simpl in H.
        unfold raw_equiv.
        simpl.
        rewrite H.
        reflexivity.
    + apply rep_ok_contradiction in r.
      contradiction.
  - destruct l1.
    + destruct l2.
      * discriminate.
      * apply rep_ok_contradiction in r0.
        contradiction.
    + simpl in H.
      rewrite app_nil_r in H.
      rewrite H.
      unfold raw_equiv.
      simpl.
      rewrite app_assoc.
      reflexivity.
  - destruct l1.
    + destruct l2.
      * discriminate.
      * apply rep_ok_contradiction in r0.
        contradiction.
    + simpl in H.
      unfold raw_equiv.
      simpl.
      rewrite app_assoc.
      rewrite app_comm_cons.
      rewrite H.
      rewrite <- app_comm_cons.
      rewrite <- app_assoc.
      reflexivity.
Qed.
 **)

Theorem rep_ok_first_empty : forall (A : Type) (l : list A), rep_ok ([],l) -> l = [].
Proof.
  intros.
  destruct l; auto.
Qed.  

#[export] Instance deq_Proper {A : Type} : Proper ((@equiv A) ==> (@equiv A)) deq.
Proof.
  unfold equiv.
  intros q q' H.
  destruct q, q'.
  simpl.
  destruct x, x0.
  simpl.
  simpl in H.
  unfold raw_equiv.
  destruct l;
    try apply rep_ok_first_empty in r;
    subst.
  - unfold raw_equiv in H.
    simpl in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H.
    rewrite H.
    apply (f_equal (@rev A)) in H0.
    rewrite rev_involutive in H0.
    simpl in H0.
    rewrite H0.
    reflexivity.
  - destruct l1.
    + apply rep_ok_first_empty in r0.
      subst.
      unfold raw_equiv in H.
      simpl in H.
      discriminate.
    + destruct l, l1;
        try (unfold raw_equiv in H);
        simpl in H;
        simpl;
        inversion H;
        try rewrite app_nil_r;
        reflexivity.
Qed.

#[export] Instance peek_Proper {A : Type} : Proper ((@equiv A) ==> (@eq (option A))) peek.
Proof.
  intros q q' H.
  unfold equiv in H.
  destruct q, q'.
  unfold raw_equiv in H.
  simpl in H.
  destruct x, x0.
  unfold peek.
  simpl.
  destruct l, l1.
  - reflexivity.
  - apply rep_ok_first_empty in r.
    subst.
    discriminate.
  - apply rep_ok_first_empty in r0.
    subst.
    discriminate.
  - simpl in H.
    inversion H.
    reflexivity.
Qed.

#[export] Instance is_empty_Proper {A : Type} : Proper ((@equiv A) ==> (@eq bool)) is_empty.
Proof.
  intros q q' H.
  unfold equiv in H.
  destruct q, q'.
  destruct x, x0.
  unfold is_empty.
  simpl.
  unfold raw_equiv in H.
  destruct l, l1; try reflexivity; simpl in H.
  - apply rep_ok_first_empty in r.
    subst.
    discriminate.
  - apply rep_ok_first_empty in r0.
    subst.
    discriminate.
Qed.  
  
End TwoListQueue.
