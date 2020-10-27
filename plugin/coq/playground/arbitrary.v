(*
 * ANY equivalence can be expressed by a configuration. Here is a proof!
 *)
Require Import Ornamental.Ornaments.

Set DEVOID lift type.

(*
 * Assume two arbitrary equivalent types A and B:
 *)
Parameter A : Type.
Parameter B : Type.

(*
 * And assume an arbitrary equivalence between them:
 *)
Parameter f : A -> B.
Parameter g : B -> A.

Parameter section : forall (a : A), g (f a) = a.
Parameter retraction : forall (b : B), f (g b) = b.

(* --- Defining a configuration for the arbitrary equivalence --- *)

(*
 * The trick is to view each a : A as g (f a). So DepConstr:
 *)
Definition dep_constr_A_0 (b : B) : A := g b.
Definition dep_constr_B_0 (b : B) : B := b.

(*
 * Eta:
 *)
Definition eta_A (a : A) : A := a.
Definition eta_B (b : B) : B := b.

(*
 * DepElim:
 *)
Program Definition dep_elim_A (P : A -> Type) (f0 : forall (b : B), P (dep_constr_A_0 b)) (a : A) : P (eta_A a).
Proof.
  unfold eta_A. rewrite <- section. apply f0.
Defined.

Program Definition dep_elim_B (P : B -> Type) (f0 : forall (b : B), P (dep_constr_B_0 b)) (b : B) : P (eta_B b).
Proof.
  apply f0.
Defined.

(* 
 * We use a modified version of Gaëtan Gilbert's proof,
 * using the adjunction machinery that Jasper Hugunin proved for us a
 * while ago. Without Gaëtan's help, I wouldn't have understood how to
 * use this.
 *)
Definition retraction_adjoint := Adjoint.fg_id' f g section retraction.

Lemma is_adjoint (b : B) : section (g b) = f_equal g (retraction_adjoint b).
Proof.
  apply Adjoint.g_adjoint.
Defined.

Lemma iota_A_aux_gen:
  forall (P : A -> Type) (b : B) (f0 : forall (b : B), P (dep_constr_A_0 b)),
    dep_elim_A
      P
      (fun b0 : B => f0 b0)
      (dep_constr_A_0 b)
    =
    f0 b.
Proof.
  intros P b f0. unfold dep_elim_A.
  unfold dep_constr_A_0.
  rewrite is_adjoint.
  destruct (retraction_adjoint b).
  reflexivity.
Defined.

Lemma iota_A_0:
  forall (P : A -> Type) (f0 : forall b : B, P (dep_constr_A_0 b))  (b : B) (Q : P (eta_A (dep_constr_A_0 b)) -> Type),
    Q (dep_elim_A P f0 (dep_constr_A_0 b)) ->
    Q (f0 b).
Proof.
  intros. rewrite <- iota_A_aux_gen. apply X.
Defined.

Lemma iota_B_0 :
  forall (P : B -> Type) (f0 : forall (b : B), P (dep_constr_B_0 b)) (b : B) (Q : P (dep_constr_B_0 b) -> Type),
    Q (dep_elim_B P f0 (dep_constr_B_0 b)) ->
    Q (f0 b).
Proof.
  intros. apply X.
Defined.

(*
 * The proof of dep_elim_OK would require univalence or UP,
 * as noted in the paper.
 *)

(* --- Proving the induced equivalence --- *)

(*
 * These should form their own equivalence:
 *)
Definition f' (a : A) : B :=
  dep_elim_A (fun _ => B) (fun b => dep_constr_B_0 b) a.

Definition g' (b : B) : A :=
  dep_elim_B (fun _ => A) (fun b => dep_constr_A_0 b) b.

(*
 * Ah, here is yet another surprise!
 * These each follow by _both_ iota, not just by one.
 * Need to think more and fix paper appropriately.
 * The idea that it forms an equivalence is true, but my proof sketch of section
 * and retraction doesn't follow in all cases---sometimes need both iota.
 * What is the meaning of this? And when will I eat dinner?
 *)
Lemma section' (a : A) : g' (f' a) = a.
Proof.
  replace a with (eta_A a) by reflexivity.
  apply dep_elim_A.
  intros b0.
  unfold f'. unfold g'.
  unfold dep_constr_A_0 at 1. unfold dep_constr_A_0 at 1.
  apply (iota_B_0 (fun _ => A) (fun b0 : B => dep_constr_A_0 b0) b0).
  apply (iota_A_0 (fun _ => B) (fun b0 : B => dep_constr_B_0 b0) b0).
  reflexivity.
Defined.

Lemma retraction' (b : B) : f' (g' b) = b.
Proof.
  replace b with (eta_B b) by reflexivity.
  apply dep_elim_B.
  intros b0.
  unfold f'. unfold g'.
  unfold dep_constr_B_0 at 1. unfold dep_constr_B_0 at 1.
  apply (iota_A_0 (fun _ => B) (fun b0 : B => dep_constr_B_0 b0) b0).
  apply (iota_B_0 (fun _ => A) (fun b0 : B => dep_constr_A_0 b0) b0).
  reflexivity.
Defined.

(* --- Using the configuration --- *)

(*
 * We can then transform functions and proofs using this equivalence.
 *
 * First we save the equivalence:
 *)
Save equivalence A B { promote = f'; forget = g' }.
Configure Lift A B {
  constrs_a = dep_constr_A_0;
  constrs_b = dep_constr_B_0;
  elim_a = dep_elim_A;
  elim_b = dep_elim_B;
  eta_a = eta_A;
  eta_b = eta_B;
  iota_a = iota_A_0;
  iota_b = iota_B_0
}.

(*
 * Same note from flip.v: Note that since we don't have unification
 * heuristics for custom equivalences, for now we'll need to represent the configuration
 * terms explicitly everywhere. And also because the transformation tries to transform
 * _everything_ that matches, but our dependent constructors take B and A respectively as
 * inputs, we need to baby the transformation into understanding when _not_ to lift a B.
 *
 * So the answer here is: we can handle any equivalence, but when
 * it comes to the details of handling it usefully, the usability barriers come up a lot here.
 * In particular all of our notes in the paper about the current lack of:
 * 1) custom unification heuristics, and
 * 2) type-directed search
 * become extremely relevant.
 *)
Module Over_A.
  (*
   * These are fine:
   *)
  Definition from_x (X : Type) (from_x : X -> A) (x : X) : A := from_x x.
  Definition to_x (X : Type) (to_x : A -> X) (a : A) : X := to_x a.

  (*
   * The catch is whenever you can _only_ create a B from an A,
   * you will not be able to remove references to A. Obviously, I guess.
   *)
   Definition ignore_A := A.
   Definition from_A (a : ignore_A) : A := dep_constr_A_0 (f a).

End Over_A.

Lift Module A B in Over_A as Over_B { opaque Over_A.ignore_A }.
Print Over_B.from_x.
Print Over_B.to_x.
Print Over_B.from_A.

(* 
 * So, as we see above, this way, we get something OK. It's just not the most
 * useful configuration. It is always OK: given any (a : A), we can always choose
 * some b such that (g b = a), since a and b are equivalent:
 *)
Lemma this_is_fine_gif:
  forall (a : A), { b : B | g b = a}.
Proof.
  intros a. exists (f a). apply section.
Defined.

(*
 * But writing all of our functions and proofs this way would be silly.
 * So with concrete instances of A, like when A is inductive,
 * we can split up into cases.
 *
 * For example, let A be list T and let B be sigT (vector T), using the standard equivalence.
 * Since (g (existT _ 0 (nilV T))) reduces to (nil T), and similarly for the cons case,
 * and nil and cons are the only two ways to construct a list, we split g into
 * two cases: nil and cons, and let those be dep_constr_A_0 and dep_constr_A_1.
 * This gives us the standard configuration.
 *)
