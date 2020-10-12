(*
 * ANY equivalence can be expressed by a configuration. Here is a proof!
 *)
Require Import Ornamental.Ornaments.

Set DEVOID lift type.

Parameter A : Type.
Parameter B : Type.

Parameter f : A -> B.
Parameter g : B -> A.

Parameter section : forall (a : A), g (f a) = a.
Parameter retraction : forall (b : B), f (g b) = b.

(*
 * We don't want to lift this, so later we'll set it as opaque.
 * For now redefine it to make this clear.
 *)
Definition ignore_A := A.

(* --- Defining a configuration for the arbitrary equivalence --- *)

(*
 * Then we get:
 *)
Definition dep_constr_A_0 (a : ignore_A) : A := a.
Definition dep_constr_B_0 (a : ignore_A) : B := f a.

(*
 * Eta:
 *)
Definition eta_A (a : A) := a.
Definition eta_B (b : B) := b.

(*
 * This gives us dep_elim:
 *)
Program Definition dep_elim_A (P : A -> Type) (f0 : forall (a : A), P (dep_constr_A_0 a)) (a : A) : P (eta_A a).
Proof.
  apply f0.
Defined.

Program Definition dep_elim_B (P : B -> Type) (f0 : forall (a : A), P (dep_constr_B_0 a)) (b : B) : P (eta_B b).
Proof.
  rewrite <- retraction. apply f0.
Defined.

(*
 * iota over A is easy, but for iota over B it is a bit weirder:
 *)
Lemma iota_A_0 :
  forall (P : A -> Type) (f0 : forall (a : A), P (dep_constr_A_0 a)) (a : A) (Q : P (dep_constr_A_0 a) -> Type),
    Q (dep_elim_A P f0 (dep_constr_A_0 a)) ->
    Q (f0 a).
Proof.
  intros. apply X.
Defined.

(* 
 * For iota over B, we use a modified version of Gaëtan Gilbert's proof,
 * using the adjunction machinery that Jasper Hugunin proved for us a
 * while ago. Without Gaëtan's help, I wouldn't have understood how to
 * use this.
 *)
Definition section_adjoint := Adjoint.fg_id' g f retraction section.

Lemma is_adjoint (a : A) : retraction (f a) = f_equal f (section_adjoint a).
Proof.
  apply Adjoint.g_adjoint.
Defined.

Lemma iota_B_aux_gen:
  forall (P : B -> Type) (a : A) (f0 : forall (a : A), P (dep_constr_B_0 a)),
    dep_elim_B
      P
      (fun a0 : A => f0 a0)
      (dep_constr_B_0 a)
    =
    f0 a.
Proof.
  intros P a f0. unfold dep_elim_B.
  unfold dep_constr_A_0. unfold dep_constr_B_0. unfold eta_B.
  unfold dep_constr_B_0 in *.
  rewrite is_adjoint.
  destruct (section_adjoint a).
  reflexivity.
Defined.

(*
 * Then we get:
 *)
Lemma iota_B_0 :
  forall (P : B -> Type) (f0 : forall (a : A), P (dep_constr_B_0 a)) (a : A) (Q : P (dep_constr_B_0 a) -> Type),
    Q (dep_elim_B P f0 (dep_constr_B_0 a)) ->
    Q (f0 a).
Proof.
  intros. unfold dep_elim_B in X. unfold eta_B in X. unfold dep_constr_B_0 in X.
  rewrite <- iota_B_aux_gen. apply X.
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
  dep_elim_A (fun _ => B) (fun a => dep_constr_B_0 a) a.

Definition g' (b : B) : A :=
  dep_elim_B (fun _ => A) (fun a => dep_constr_A_0 a) b.

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
  intros a0.
  unfold f'. unfold g'.
  unfold dep_constr_A_0 at 1. unfold dep_constr_A_0 at 1.
  apply (iota_B_0 (fun _ => A) (fun a0 : A => dep_constr_A_0 a0) a0).
  apply (iota_A_0 (fun _ => B) (fun a0 : A => dep_constr_B_0 a0) a0).
  reflexivity.
Defined.

Lemma retraction' (b : B) : f' (g' b) = b.
Proof.
  replace b with (eta_B b) by reflexivity.
  apply dep_elim_B.
  intros a.
  unfold f'. unfold g'.
  unfold dep_constr_B_0 at 1. unfold dep_constr_B_0 at 1.
  apply (iota_A_0 (fun _ => B) (fun a0 : A => dep_constr_B_0 a0) a).
  apply (iota_B_0 (fun _ => A) (fun a0 : A => dep_constr_A_0 a0) a).
  reflexivity.
Defined.

(* --- Using the configuration --- *)

(*
 * We can then transform functions and proofs using this equivalence.
 * However, this does not necessarily imply _usefulness_ of the transformation
 * for every equivalence---note that the trivial construction of the equivalence
 * does not remove references to the old type entirely.
 * In particular, dep_constr_B applies f, and dep_elim_B rewrites by retraction.
 * Though these occurrences may reduce away later.
 *)

(*
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
  Definition id (a : A) := a.

  Parameter X : Type.
  Axiom from_x : X -> A.
  Axiom to_x : A -> X.

  (*
   * The transformation doesn't work unless we tell the transformation that this:
   *)
  Definition from_x_implicit (x : X) : A := from_x x.
  (*
   * is an application of dep_constr:
   *)
  Definition from_x_explicit (x : X) : A := dep_constr_A_0 (from_x x).

  (*
   * Similarly:
   *)
  Definition to_x_implicit (a : A) : X := to_x a.
  (*
   * is an application of dep_elim:
   *)
  Definition to_x_explicit (a : A) := dep_elim_A (fun _ => X) (fun a0 => to_x a0) a.

End Over_A.

(*
 * opaque says to ignore ignore_A :
 *)
Lift Module A B in Over_A as Over_B { opaque ignore_A eq_ind eq_ind_r }.
Print Over_B.from_x_explicit.
(* Over_B.from_x_explicit = fun x : Over_B.X => f (Over_A.from_x x)
     : Over_B.X -> B*)
Print Over_B.to_x_explicit.
(* Over_B.to_x_explicit = 
fun a : B =>
eq_rect (f (g (eta_B a))) (fun _ : B => Over_B.X) (Over_A.to_x (g (eta_B a))) 
  (eta_B a) (retraction (eta_B a))
     : forall a : B, (fun _ : B => Over_B.X) (eta_B a) *)

(* 
 * So, as we see above, this way, we get something OK. But when we know
 * nothing about A and B or the equivalence between them, we can't get
 * rid of all occurrences to A yet. In contrast, if we know how f behaves
 * (and we know how from_x behaves), we can effectively reduce (f (OverA.from x x))
 * ahead of time to get something over B, and transform directly.
 * We could similarly port proofs then without rewriting by retraction.
 * And this is where the transformation is useful for repair.
 *)
