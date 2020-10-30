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
Definition eta_A (a : A) := a.
Definition eta_B (b : B) := b.

Lemma eta_OK_A : forall (a : A), eta_A a = a.
Proof.
  reflexivity.
Defined.
Lemma eta_OK_B : forall (b : B), eta_B b = b.
Proof.
  reflexivity.
Defined.

(*
 * DepElim:
 *)
Program Definition dep_elim_A (P : A -> Type) (f0 : forall (b : B), P (dep_constr_A_0 b)) (a : A) : P (eta_A a).
Proof.
  rewrite <- section. apply f0.
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

Lemma iota_A_aux_gen :
  forall (P : A -> Type) (b : B) (f0 : forall (b : B), P (dep_constr_A_0 b)),
    dep_elim_A
      P
      (fun b0 : B => f0 b0)
      (dep_constr_A_0 b)
    =
    eq_rect (dep_constr_A_0 b) (fun H : A => P H) (f0 b) (eta_A (dep_constr_A_0 b)) (eq_sym (eta_OK_A (dep_constr_A_0 b))).
Proof.
  intros P b f0. unfold dep_elim_A.
  unfold dep_constr_A_0. rewrite eta_OK_A.
  rewrite is_adjoint.
  destruct retraction_adjoint.
  reflexivity.
Defined.

(*
 * This nasty eq_rect ... here reduces to just (f0 b), it is just included for clarity in the general case
 * where eta is not identity.
 *)
Lemma iota_A_0:
  forall (P : A -> Type) (f0 : forall b : B, P (dep_constr_A_0 b))  (b : B) (Q : P (eta_A (dep_constr_A_0 b)) -> Type),
    Q (dep_elim_A P f0 (dep_constr_A_0 b)) ->
    Q (eq_rect (dep_constr_A_0 b) (fun H : A => P H) (f0 b) (eta_A (dep_constr_A_0 b)) (eq_sym (eta_OK_A (dep_constr_A_0 b)))).
Proof.
  intros. rewrite <- iota_A_aux_gen. apply X.
Defined.

(*
 * This follows by reflexivity, but I abstract to show the type signatures and so on:
 *)
Lemma iota_B_aux_gen :
  forall (P : B -> Type) (b : B) (f0 : forall (b : B), P (dep_constr_B_0 b)),
    dep_elim_B
      P
      (fun b0 : B => f0 b0)
      (dep_constr_B_0 b)
    =
    eq_rect (dep_constr_B_0 b) (fun H : B => P H) (f0 b) (eta_B (dep_constr_B_0 b)) (eq_sym (eta_OK_B (dep_constr_B_0 b))).
Proof.
  intros P b f0. unfold dep_elim_B.
  unfold dep_constr_B_0. destruct eta_OK_B.
  reflexivity.
Defined.

(*
 * Likewise, this nasty eq_rect ... here reduces to just (f0 b).
 *)
Lemma iota_B_0 :
  forall (P : B -> Type) (f0 : forall (b : B), P (dep_constr_B_0 b)) (b : B) (Q : P (eta_B (dep_constr_B_0 b)) -> Type),
    Q (dep_elim_B P f0 (dep_constr_B_0 b)) ->
    Q (eq_rect (dep_constr_B_0 b) (fun H : B => P H) (f0 b) (eta_B (dep_constr_B_0 b)) (eq_sym (eta_OK_B (dep_constr_B_0 b)))).
Proof.
  intros. rewrite <- iota_B_aux_gen. apply X.
Defined.

(* --- Proof that this configuration is OK --- *)

(*
 * Here we prove the correctness criteria from Figure 12.
 *)

(*
 * First we define f, g, section, and retraction:
 *)
Definition f' (a : A) : B :=
  dep_elim_A (fun _ => B) (fun b => dep_constr_B_0 b) a.

Definition g' (b : B) : A :=
  dep_elim_B (fun _ => A) (fun b => dep_constr_A_0 b) b.

Lemma section' (a : A) : g' (f' a) = a.
Proof.
  replace a with (eta_A a) by (apply eta_OK_A).
  apply dep_elim_A.
  intros b0. unfold dep_constr_A_0 at 1.
  replace (dep_constr_A_0 b0) with (eq_rect (dep_constr_B_0 b0) (fun _ : B => A) (dep_constr_A_0 b0) (eta_B (dep_constr_B_0 b0)) (eq_sym (eta_OK_B (dep_constr_B_0 b0)))).
  - apply (iota_B_0 (fun _ => A) (fun b0 : B => dep_constr_A_0 b0) b0 (fun a => (g' (f' (dep_constr_A_0 b0))) = a)).
    replace (dep_constr_B_0 b0) with (eq_rect (dep_constr_A_0 b0) (fun _ : A => B) (dep_constr_B_0 b0) (eta_A (dep_constr_A_0 b0)) (eq_sym (eta_OK_A (dep_constr_A_0 b0)))).
    + apply (iota_A_0 (fun _ => B) (fun b0 : B => dep_constr_B_0 b0) b0 (fun b => (g' (f' (dep_constr_A_0 b0))) = g' b)).
      reflexivity.
    + destruct (eta_OK_A (dep_constr_A_0 b0)). reflexivity.
  - destruct (eta_OK_B (dep_constr_B_0 b0)). reflexivity.
Defined.

Print section'.

Lemma retraction' (b : B) : f' (g' b) = b.
Proof.
  replace b with (eta_B b) by (apply eta_OK_B).
  apply dep_elim_B.
  intros b0. unfold dep_constr_B_0 at 1.
  replace (dep_constr_B_0 b0) with (eq_rect (dep_constr_A_0 b0) (fun _ : A => B) (dep_constr_B_0 b0) (eta_A (dep_constr_A_0 b0)) (eq_sym (eta_OK_A (dep_constr_A_0 b0)))).
  - apply (iota_A_0 (fun _ => B) (fun b0 : B => dep_constr_B_0 b0) b0 (fun b => (f' (g' (dep_constr_B_0 b0))) = b)).
    replace (dep_constr_A_0 b0) with (eq_rect (dep_constr_B_0 b0) (fun _ : B => A) (dep_constr_A_0 b0) (eta_B (dep_constr_B_0 b0)) (eq_sym (eta_OK_B (dep_constr_B_0 b0)))).
    + apply (iota_B_0 (fun _ => A) (fun b0 : B => dep_constr_A_0 b0) b0 (fun b => (f' (g' (dep_constr_B_0 b0))) = f' b)).
      reflexivity.
    + destruct (eta_OK_B (dep_constr_B_0 b0)). reflexivity.
  - destruct (eta_OK_A (dep_constr_A_0 b0)). reflexivity.
Defined.

(*
 * To avoid dependencies, we unfold the definition of transport here.
 *)
Lemma dep_constr_OK :
  forall (b : B), dep_constr_A_0 b = g (dep_constr_B_0 b).
Proof.
  reflexivity.
Defined.

Definition section_adjoint := Adjoint.fg_id' g f retraction section.

Lemma is_adjoint' (a : A) : retraction (f a) = f_equal f (section_adjoint a).
Proof.
  apply Adjoint.g_adjoint.
Defined.

(*
 * Same here:
 *)
Lemma dep_elim_OK_typ :
  forall P f0 b,
    dep_elim_B P f0 b =
    eq_rect
      (f (eta_A (g b)))
      (fun (H : B) => P H)
      (dep_elim_A (fun (a : A) => P (f a)) (fun b => f0 (f (dep_constr_A_0 b))) (g b)) 
      (eta_B b)
      (retraction b).
Proof.
  intros P f0 b. unfold dep_elim_B. destruct (eta_OK_B b).
  unfold dep_elim_A. unfold eta_A. unfold eta_B.
  rewrite is_adjoint.
  destruct retraction_adjoint.
  rewrite is_adjoint'.
  destruct section_adjoint.
  reflexivity.
Defined.

Definition elim_eta_A := dep_elim_A.
Definition elim_eta_B := dep_elim_B.

Definition iota_OK_0_A := iota_A_0.
Definition iota_OK_0_B := iota_B_0.

(*
 * eta_OK is up top of the file.
 *)

(* --- Using the configuration --- *)

(*
 * We can transform functions and proofs using this equivalence.
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




