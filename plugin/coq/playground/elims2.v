Add LoadPath "coq/playground".
Require Import Vector.
Require Import List.
Require Import elims.

Notation vector := Vector.t.
Notation nilV := Vector.nil.
Notation consV := Vector.cons.

(*
 * More of an attempt at understanding why lifting eliminators is OK, formally.
 *)

(* --- Algebraic ornaments --- *)

Module Algebraic.

Definition transport_A_B {T} := list_to_t T.
Definition transport_B_A {T} := list_to_t_inv T.

(*
 * Dependent constructors with explicit transport:
 *)
Definition Tenilv T := transport_A_B (@nil T).
Definition Teconsv T t s := transport_A_B (@cons T t (transport_B_A s)).

(*
 * Dependent constructors with implicit transport:
 *)
Definition enilv T := existT _ 0 (nilV T).
Definition econsv T t s := existT _ (S (projT1 s)) (@consV T t (projT1 s) (projT2 s)).

(*
 * Correspondence:
 *)
Lemma Tenilv_enilv:
  forall (T : Type), Tenilv T = enilv T.
Proof.
  reflexivity.
Defined.

Lemma transport_cons:
  forall (T : Type) (t : T) (l : list T),
    transport_A_B (@cons T t l) =
    existT _ (S (projT1 (transport_A_B l))) (@consV T t (projT1 (transport_A_B l)) (projT2 (transport_A_B l))).
Proof.
  reflexivity.
Defined.

Lemma Teconsv_econsv:
  forall (T : Type) (t : T) (s : sigT (vector T)),
    Teconsv T t s = econsv T t s.
Proof.
  intros. unfold Teconsv, econsv.
  rewrite transport_cons.
  rewrite list_to_t_retraction.
  auto.
Defined.

(*
 * Dependent elimination with explicit transport:
 *)
Definition TQ {T : Type} (P : sigT (vector T) -> Type) := fun l => P (transport_A_B l).

Program Definition Tpenilv {T : Type} (P : sigT (vector T) -> Type) :
  P (Tenilv T) -> 
  TQ P (@nil T).
Proof.
  intros pnil. apply pnil.
Defined.

Definition Tpeconsv {T : Type} (P : sigT (vector T) -> Type) :
  (forall t (s : sigT (vector T)), P s -> P (Teconsv T t s)) ->
  (forall t (l : list T), TQ P l -> TQ P (@cons T t l)).
Proof.
  intros pcons. intros t l IHl. unfold TQ.
  specialize (pcons t (transport_A_B l)).
  rewrite Teconsv_econsv in pcons.
  apply pcons.
  apply IHl.
Defined.

Lemma PQ_retract:
  forall {T} P s,
    @TQ T P (transport_B_A s) = P s.
Proof.
  intros. unfold TQ. f_equal. apply list_to_t_retraction.
Defined.

Lemma TsigT_vect_rect :
  (forall (T : Type) (P : list T -> Type),
    P nil ->
    (forall (t : T) (l : list T), P l -> P (@cons T t l)) ->
    forall (l : list T), P l) ->
  (forall (T : Type) (P : sigT (vector T) -> Type),
    P (Tenilv T) ->
    (forall (t : T) (s : sigT (vector T)), P s -> P (Teconsv T t s)) ->
    forall (s : sigT (vector T)), P s).
Proof.
  intros list_rect T P qnil qcons s. rewrite <- PQ_retract. 
  apply (@list_rect T (TQ P) (Tpenilv P qnil) (Tpeconsv P qcons) (transport_B_A s)).
Defined.

Definition sigT_vect_rect_via_list_rect := TsigT_vect_rect list_rect.

(*
 * Dependent elimination with implicit transport:
 *)
Lemma sigT_vect_rect :
  (forall (T : Type) (P : sigT (vector T) -> Type),
    P (enilv T) ->
    (forall (t : T) (s : sigT (vector T)), P s -> P (econsv T t s)) ->
    forall (s : sigT (vector T)), P s).
Proof.
  intros T P qnil qcons s. induction s. induction p.
  - apply qnil.
  - specialize (qcons h (existT _ n p) IHp). (* <- note reconstruction *)
    apply qcons.
Defined.

(* Where we have eliminated something, we reconstruct it inside of the innermost eliminator. *)

(* Maybe we want to instead think about the relation corresponding to the equivalence: *)
Inductive List_to_t_inv (T : Type) : sigT (vector T) -> list T -> Type :=
| enilv_nil : List_to_t_inv T (enilv T) (@nil T)
| econsv_cons: forall (t : T) (s : sigT (vector T)) (l : list T),
    List_to_t_inv T s l ->
    List_to_t_inv T (econsv T t s) (@cons T t l).

Check List_to_t_inv_rect.

(* forall (T : Type)
         (P : forall (s : {x : nat & vector T x}) (l : list T),
              List_to_t_inv T s l -> Type),
       P (enilv T) Datatypes.nil (enilv_nil T) ->
       (forall (t0 : T) (s : {x : nat & vector T x}) (l : list T)
          (l0 : List_to_t_inv T s l),
        P s l l0 -> P (econsv T t0 s) (t0 :: l) (econsv_cons T t0 s l l0)) ->
       forall (s : {x : nat & vector T x}) (l : list T) (l0 : List_to_t_inv T s l),
       P s l l0 *)

Lemma list_to_t_inv_List_to_t_inv:
  forall T s,
    List_to_t_inv T s (list_to_t_inv T s).
Proof.
  intros T s. induction s. induction p.
  - constructor.
  - apply econsv_cons with (t0 := h) in IHp.
    apply IHp.
Defined.

Lemma sigT_vect_rect' :
  (forall (T : Type) (P : sigT (vector T) -> Type),
    P (enilv T) ->
    (forall (t : T) (s : sigT (vector T)), P s -> P (econsv T t s)) ->
    forall (s : sigT (vector T)), P s).
Proof.
  intros T P pnil pcons s. 
  pose proof (List_to_t_inv_rect T (fun (s : sigT (vector T)) (l : list T) (H : List_to_t_inv T s l) => P s)) as H.
  specialize (H pnil).
  specialize (H (fun t0 s l l0 IH => pcons t0 s IH)).
  specialize (H s (list_to_t_inv T s) (list_to_t_inv_List_to_t_inv T s)).
  apply H.
Defined.

(* Interesting *)

(* Now let's define a literal inductive type without the junk: *)
Inductive SigT_vect (T : Type) : sigT (vector T) -> Type :=
| Enilv : SigT_vect T (enilv T)
| Econsv: forall (t : T) (s : sigT (vector T)),
    SigT_vect T s ->
    SigT_vect T (econsv T t s).

Check SigT_vect_rect.

(* SigT_vect_rect
     : forall (T : Type) (P : forall s : {x : nat & vector T x}, SigT_vect T s -> Type),
       P (enilv T) (Enilv T) ->
       (forall (t0 : T) (s : {x : nat & vector T x}) (s0 : SigT_vect T s),
        P s s0 -> P (econsv T t0 s) (Econsv T t0 s s0)) ->
       forall (s : {x : nat & vector T x}) (s0 : SigT_vect T s), P s s0*)

Lemma sigT_vect_SigT_vect:
  forall (T : Type) (s : sigT (vector T)),
    SigT_vect T s.
Proof.
  intros T s. induction s. induction p.
  - apply Enilv.
  - apply Econsv with (t0 := h) in IHp. apply IHp.
Defined.

Lemma sigT_vect_rect'' :
  (forall (T : Type) (P : sigT (vector T) -> Type),
    P (enilv T) ->
    (forall (t : T) (s : sigT (vector T)), P s -> P (econsv T t s)) ->
    forall (s : sigT (vector T)), P s).
Proof.
  intros T P pnil pcons s. 
  pose proof (sigT_vect_SigT_vect T s) as S. induction S.
  - apply pnil.
  - apply pcons. apply IHS.
Defined.

(*
 * OK, so at its core, the transformation for the eliminator is the transformation needed
 * to show the correspondence between the type definition and the inductive relation
 * describing the equivalence with the right shape. Here, it is sigT_vect_SigT_vect.
 *)

End Algebraic.

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
  intros. induction f0. reflexivity.
Defined.

Theorem Foo_to_Bar_retraction:
  forall (n : nat) (b : Bar n), Foo_to_Bar n (Bar_to_Foo n b) = b.
Proof.
  intros. induction b.
  - auto.
  - simpl. simpl in IHb. rewrite IHb. auto.
Defined.

(*
 * Constructor:
 *)
Definition Tbarf (n : nat) :=
  Foo_to_Bar n (f n).

Definition barf (n : nat) :=
  nat_rect Bar f1 (fun _ IHn => f2 _ IHn) n.

Lemma Tbarf_barf:
  forall (n : nat), Tbarf n = barf n.
Proof.
  reflexivity.
Defined.

Lemma Foo_Bar_P:
  forall (n : nat) (P : forall (n : nat), Bar n -> Type) (b : Bar n), 
    P n (Foo_to_Bar n (Bar_to_Foo n b)) ->
    P n b.
Proof.
  intros. rewrite Foo_to_Bar_retraction in X. apply X.
Defined.

Lemma Bar_Foo_rect:
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (barf n)) ->
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b.
  apply Foo_Bar_P. (* in algorithm, though, we internalize this retraction call? How? *)
  apply pf0.
Defined.

(* internalized retraction becomes: *)
Lemma Bar_nat_rect_1:
  forall (n : nat) (b : Bar n),
    Foo_to_Bar n (f n) = b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. unfold Foo_to_Bar in IHb. simpl in IHb. rewrite IHb. reflexivity.
Defined.

Lemma Bar_nat_rect:
  forall (n : nat) (b : Bar n),
    nat_rect Bar f1 (fun (n : nat) (IHn : Bar n) => f2 n IHn) n = b.
Proof.
  intros. induction b.
  - reflexivity.
  - simpl. rewrite IHb. reflexivity.
Defined.

Lemma Bar_Foo_rect':
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (barf n)) ->
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b.
  rewrite <- Bar_nat_rect.
  apply pf0.
Defined.

(* internalized section becomes: *)

Theorem Foo_to_Bar_section_1:
  forall (n : nat) (f : Foo n), Bar_to_Foo n (nat_rect Bar f1 (fun (n : nat) (IHn : Bar n) => f2 n IHn) n) = f.
Proof.
  intros. induction f0. reflexivity.
Defined.

Theorem Foo_to_Bar_section_2:
  forall (n : nat) (f0 : Foo n), nat_rect Foo (f 0) (fun (n : nat) (IHn : Foo n) => f (S n)) n = f0.
Proof.
  intros. induction f0. induction n; reflexivity. (* whyyyy *)
Defined.

Lemma Foo_Bar_rect:
  forall P : forall n : nat, Foo n -> Type,
    P 0 (f 0) ->
    (forall (n : nat) (f0 : Foo n), P n (f n) -> P (S n) (f (S n))) ->
    forall (n : nat) (b : Foo n), P n (f n).
Proof.
  intros P pf1 pf2 n fo. induction n. (* <-- internalized Foo_to_Bar *)
  - apply pf1.
  - apply (pf2 n (f n)). apply IHn. apply f. (* <-- internalized Bar_to_Foo *)
Defined.

(* IDK, I'm confused by how to define these eliminators more generally *)

Inductive FFoo : forall (n : nat), Foo n -> Type :=
| FF1 : FFoo 0 (f 0)
| FF2 :
    forall (n : nat) (fo : Foo n),
      FFoo n fo ->
      FFoo (S n) (f (S n)).

Inductive BBar : forall (n : nat), Bar n -> Type :=
| FF : forall n, BBar n (nat_rect (fun (n1 : nat) => Bar n1) f1 (fun (n1 : nat) (IHn : Bar n1) => f2 n1 IHn) n).

Lemma nat_eta:
  forall (n : nat),
    n = nat_rect (fun (n1 : nat) => nat) 0 (fun (n1 : nat) (IHn : nat) => S IHn) n.
Proof.
  induction n.
  - auto.
  - simpl. rewrite IHn. auto.
Defined.

Lemma bar_eta:
  forall (n : nat) (b : Bar n),
    b = Bar_rect (fun (n1 : nat) => nat) 0 (fun (n1 : nat) (IHn : nat) => S IHn) n.
Proof.
  induction n.
  - auto.
  - simpl. rewrite IHn. auto.
Defined.

Check sigT_rect.

Lemma sigT_vect_eta:
  forall (T : Type) (s : sigT (vector T)),
    s = sigT_rect (fun s => sigT (vector T)) (fun n v => existT _ n v) s.
Proof.
  intros. induction s. reflexivity.
Defined.

Lemma Bar_BBar:
  forall (n : nat) (b : Bar n),
    BBar n b.
Proof.
  intros. pose proof (FF n) as bb.
  rewrite <- nat_eta in bb.
  - apply FF.
  - apply (FF H). 
  - apply FF. 
  - apply FF in IHb. unfold f2. simpl.
Defined.

Lemma Bar_Foo_rect'':
  forall (P : forall (n : nat), Bar n -> Type),
    (forall (n : nat), P n (barf n)) ->
    (forall (n : nat) (b : Bar n), P n b).
Proof.
  intros P pf0 n b.
  pose proof (Bar_BBar n b) as bb.
  induction bb.
  apply pf0.
Defined.

Lemma Foo_FFoo:
  forall (n : nat) (fo : Foo n),
    FFoo n fo.
Proof.
  intros. induction fo. induction n.
  - apply FF1.
  - apply FF2 in IHn. apply IHn. 
Defined.

Lemma Foo_FFoo':
  forall (n : nat) (fo : Foo n),
    FFoo n (Bar_to_Foo n (Foo_to_Bar n fo)).
Proof.
  intros. induction fo. simpl. induction n.
  - apply FF1.
  - apply FF2 in IHn. apply IHn. 
Defined.

Lemma Foo_Bar_rect':
  forall P : forall n : nat, Foo n -> Type,
    P 0 (f 0) ->
    (forall (n : nat) (f0 : Foo n), P n (f n) -> P (S n) (f (S n))) ->
    forall (n : nat) (b : Foo n), P n (f n).
Proof.
  intros P pf1 pf2 n fo.
  pose proof (Foo_FFoo n fo) as ff.
  induction ff.
  - apply pf1.
  - apply pf2; auto.
Defined.

(* Foo_to_Bar = 
fun (n : nat) (H : Foo n) =>
Foo_rec (fun (n0 : nat) (_ : Foo n0) => Bar n0)
  (fun n0 : nat =>
   nat_rec (fun n1 : nat => Bar n1) f1 (fun (n1 : nat) (IHn : Bar n1) => f2 n1 IHn) n0)
  n H
     : forall n : nat, Foo n -> Bar n*)

