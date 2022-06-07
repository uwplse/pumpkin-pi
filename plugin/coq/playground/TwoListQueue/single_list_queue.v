Require Import List Bool.
Import ListNotations.
Require Import Coq.Classes.SetoidClass.
Module SimpleQueue.

Definition queue (A : Type) := list A % type.

#[export] Instance slq_setoid {A : Type} : Setoid (@queue A) :=
  {equiv := eq
   ;setoid_equiv := eq_equivalence
  }.

Definition empty {A : Type} : queue A := [].
Definition is_empty {A : Type} (q : queue A) : bool :=
  match q with
  | []  => true
  | _::_ => false
  end.

Definition enq {A : Type} (a : A) (q : queue A) : queue A :=
  q ++ [a].

Definition deq {A : Type} (q : queue A) : queue A :=
  match q with
  | [] => []
  | h::t => t
  end.

Definition peek {A : Type} (q : queue A) : option A :=
  match q with
  | [] => None
  | h::t => Some h
  end.

Definition equiv {A : Type} (q1 q2 : queue A) : Prop :=
  q1 = q2.

Theorem empty_is_empty : forall (A : Type),
    is_empty (@empty A) = true.
Proof.
  reflexivity.
Qed.

Theorem enq_not_empty : forall (A : Type) (a : A) (q : queue A),
    is_empty (enq a q) = false.
Proof.
  intros.
  induction q; reflexivity.
Qed.

Theorem no_peek_empty : forall (A : Type),
  peek (@empty A) = None.
Proof.
  reflexivity.
Qed.

Lemma is_empty_implies_empty : forall (A : Type) (q : queue A),
    is_empty q = true -> q = empty.
Proof.
  intros.
  induction q.
  - reflexivity.
  - discriminate.
Qed.

Theorem peek_singleton : forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> peek (enq a q) = Some a.
Proof.
  intros.
  induction q.
  - reflexivity.
  - discriminate.
Qed.

Print peek_singleton.

Definition peek_singleton2 :
  forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> peek (enq a q) = Some a :=
  fun (A : Type) (a : A) (q : queue A)
  (H : is_empty q = true) =>
  list_ind
    (fun q0 : list A =>
      is_empty q0 = true -> peek (enq a q0) = Some a)
    (fun _ : is_empty [] = true => eq_refl)
    (fun (a0 : A) (q0 : list A)
      (_ : is_empty q0 = true ->
        peek (enq a q0) = Some a)
      (H0 : is_empty (a0 :: q0) = true) =>
        let H1 : False :=
          eq_ind
            (is_empty (a0 :: q0))
            (fun e : bool => if e then False else True)
            I
            true
            H0 in
        False_ind
          (peek (enq a (a0 :: q0)) = Some a)
          H1)
    q
  H.

Theorem peek_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    is_empty q = false -> peek (enq a q) = peek q.
Proof.
  intros.
  induction q.
  - discriminate.
  - reflexivity.
Qed.

Theorem deq_singleton : forall (A : Type) (a : A) (q : queue A),
    is_empty q = true -> deq (enq a q) = q.
Proof.
  intros.
  apply is_empty_implies_empty in H.
  rewrite H.
  reflexivity.
Qed.

Theorem deq_enq_nonempty : forall (A : Type) (a : A) (q : queue A),
    is_empty q = false -> equiv (deq (enq a q)) (enq a (deq q)).
Proof.
  intros.
  unfold equiv.
  induction q.
  - discriminate.
  - reflexivity.
Qed.

Print deq_enq_nonempty.

Check list_ind.

Definition deq_enq_nonempty2 :
  forall (A : Type) (a : A) (q : queue A),
       is_empty q = false ->
       equiv (deq (enq a q)) (enq a (deq q)) :=
  fun (A : Type) (a : A) (q : queue A)
  (H : is_empty q = false) =>
    list_ind
      (fun q0 : list A =>
        is_empty q0 = false ->
        deq (enq a q0) = enq a (deq q0))
      (fun H0 : is_empty [] = false =>
        let H1 : False :=
          eq_ind (is_empty [])
            (fun e : bool => if e then True else False)
            I
            false
            H0 in
        False_ind
          (deq (enq a []) = enq a (deq []))
          H1)
      (fun (a0 : A) (q0 : list A)
        (_ : is_empty q0 = false ->
          deq (enq a q0) = enq a (deq q0))
        (_ : is_empty (a0 :: q0) = false) =>
         eq_refl)
      q
      H.
End SimpleQueue.
