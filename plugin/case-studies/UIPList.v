(*
 * This entire file is adapted from this gist:
 * https://gist.github.com/JoJoDeveloping/e44659128428a6bcd202585bb1b3a27f
 * by Johannes Matthias Hostert, with permission.
 *)

From Coq Require Import Arith Lia List.
Require Import EqdepFacts.

Definition sigma {X:Type} {x y : X} (H : x=y) : y=x := match H in (_=z) return z=x with eq_refl _ => eq_refl end.
Definition tau {X:Type} {x y z: X} (H1 : x=y) : y=z -> x=z := match H1 in (_=w) return w=z->x=z with eq_refl _ => fun H => H end.

(* A hedberg function yields a constant path if both arguments are equal
   (i.e. the output path does not depend on the input path)
   Usually these are constructed using an equalitiy decider.
   Here, we will do something different. *)
Definition is_hedberg (X:Type) (f : forall (x y:X), x=y -> x=y) :=
  forall x y H1 H2, f x y H1 = f x y H2.

(* Simple proof of UIP from existence of a Hedberg function.
   My version is due to Prof. Smolka's lecture notes: https://www.ps.uni-saarland.de/~smolka/drafts/icl_book.pdf (chapter 24),
   which cites Kraus et al @ TLCA 2013 as the original source *)
Lemma hedberg_to_UIP X f : is_hedberg X f -> UIP_ X.
Proof.
  intros H1 x y E1 E2.
  assert (forall (e:x=y), tau (f _ _ e) (sigma (f _ _ eq_refl)) = e) as Heq1.
  { intros e. destruct e. destruct (f x x eq_refl). easy. }
  rewrite <- (Heq1 E1).
  rewrite <- (Heq1 E2).
  rewrite (H1 x y E1 E2).
  reflexivity.
Qed.

(* by cleverly using constructor laws, we similarly gain a hedberg function for list *)
Lemma list_ctor_law1 (X:Type) (h1 h2 : X) (t1 t2 : list X) : (h1::t1) = (h2::t2) -> h1 = h2.
Proof. intros H; congruence. Qed.
Lemma list_ctor_law2 (X:Type) (h1 h2 : X) (t1 t2 : list X) : (h1::t1) = (h2::t2) -> t1 = t2.
Proof. intros H; congruence. Qed.
Lemma list_ctor_law3 (X:Type) (h1 h2 : X) (t1 t2 : list X) : h1 = h2 -> t1 = t2 -> (h1::t1) = (h2::t2).
Proof. intros H1 H2; congruence. Qed.

(* Our hedberg function. The key idea is extracting and recombining the equalities.
   This means that the intermediate equalities are all on X, which has UIP.
   Thus they are all equal, and their combination is also equal, yielding a hedberg function.
   See below for a formal proof *)
Fixpoint UIP_list_hedberg (X:Type) (l1 l2 : list X) : l1 = l2 -> l1 = l2.
Proof.
  destruct l1 as [|l1h l1t]; destruct l2 as [|l2h l2t]; intros Heq; try (exfalso; congruence).
  - reflexivity.
  - apply list_ctor_law3.
    + eapply list_ctor_law1, Heq.
    + eapply (UIP_list_hedberg _), list_ctor_law2, Heq.
Defined.

Lemma UIP_list_is_hedberg (X:Type) (Huip : UIP_ X) : is_hedberg _ (UIP_list_hedberg X).
Proof.
  intros x y; induction x as [|xh xr IH] in y|-*; destruct y as [|yh yr]; intros E1 E2; try (exfalso; congruence).
  - cbn. easy.
  - cbn.
    erewrite (Huip _ _ (list_ctor_law1 X xh yh xr yr E1)).
    erewrite (IH _ (list_ctor_law2 X xh yh xr yr E1)).
    reflexivity.
Qed.

Lemma UIP_to_list (T : Type) : UIP_ T -> UIP_ (list T).
Proof.
  intros H x y. eapply hedberg_to_UIP. apply (UIP_list_is_hedberg _ H).
Qed.

(*
 * We can use a similar approach for pairs (new code from here on out)
 *)
Lemma pair_ctor_law1 (X : Type) (x1 x2 : X) (x1' x2' : X) : (x1, x2) = (x1', x2') -> x1 = x1'.
Proof. intros; congruence. Qed.
Lemma pair_ctor_law2 (X : Type) (x1 x2 : X) (x1' x2' : X) : (x1, x2) = (x1', x2') -> x2 = x2'.
Proof. intros; congruence. Qed.
Lemma pair_ctor_law3 (X:Type) (x1 x2 : X) (x1' x2' : X) : x1 = x1' -> x2 = x2' -> (x1, x2) = (x1', x2').
Proof. intros; congruence. Qed.

(* Our hedberg function *)
Fixpoint UIP_pair_hedberg (X:Type) (p1 p2 : X * X) : p1 = p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; intros Heq; try (exfalso; congruence).
  apply pair_ctor_law3.
  - eapply pair_ctor_law1, Heq.
  - eapply pair_ctor_law2, Heq.
Defined.

Lemma UIP_pair_is_hedberg (X:Type) (Huip : UIP_ X) : is_hedberg _ (UIP_pair_hedberg X).
Proof.
  intros x y; destruct x; destruct y; intros E1 E2; try (exfalso; congruence).
  cbn. erewrite (Huip _ _ (pair_ctor_law1 X x x0 x1 x2 E1)).
  erewrite (Huip _ _ (pair_ctor_law2 X x x0 x1 x2 E1)).
  reflexivity.
Qed.

Lemma UIP_to_pair (T : Type) : UIP_ T -> UIP_ (T * T).
Proof.
  intros H x y. eapply hedberg_to_UIP. apply (UIP_pair_is_hedberg _ H).
Qed.
