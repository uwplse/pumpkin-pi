Add LoadPath "coq/playground".
Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

(* --- 9/17: Playing with a Reviewer A example --- *)

Inductive I :=
| A : I
| B : I.

Module Old'.

Definition and (i1 i2 : I) : I :=
  match i1 with
  | A => i2
  | B => B
  end.

Definition or (i1 i2 : I) : I :=
  match i1 with
  | A => A
  | B => i2
  end.

Definition neg (i : I) : I :=
  match i with
  | A => B
  | B => A
  end.

Theorem demorgan_1:
  forall (i1 i2 : I), 
    neg (and i1 i2) =
    or (neg i1) (neg i2).
Proof.
  intros i1 i2. induction i1; auto.
Defined.

Theorem demorgan_2:
  forall (i1 i2 : I), 
    neg (or i1 i2) =
    and (neg i1) (neg i2).
Proof.
  intros i1 i2. induction i1; auto.
Defined.

End Old'.

Preprocess Module Old' as Old { opaque I_ind }.
Import Old.

(* We will change the type to this: *)
Inductive J :=
| makeJ : bool -> J.

(* --- Configuration ---*)

(*
 * This example uses manual configuration. Many of the examples we see later will
 * do this part automatically! The exact meaning of this will be explained
 * later. But essentially, this tells the tool which constructor maps to true 
 * and which maps to false:
 *)
Definition dep_constr_I_0 : I := A.
Definition dep_constr_I_1 : I := B.

Definition dep_constr_J_0 : J := makeJ true.
Definition dep_constr_J_1 : J := makeJ false.

(*
 * How to eta-expand I and J (trivial here):
 *)
Definition eta_I (i : I) : I := i.
Definition eta_J (j : J) : J := j.

(*
 * How to map between eliminators:
 *)
Definition dep_elim_I P f0 f1 i : P (eta_I i) :=
  I_rect P f0 f1 i.

Definition dep_elim_J P f0 f1 j : P (eta_J j) :=
  J_rect P (fun b => bool_rect _ f0 f1 b) j.

(*
 * And how to reduce inductive cases of eliminators, which here is trivial since
 * there are no inductive cases of these types:
 *)
Definition iota_I_0 (P : I -> Type) (f0 : P A) (f1 : P B) (Q : P A -> Type) (H : Q f0) :=
  H.

Definition iota_I_1 (P : I -> Type) (f0 : P A) (f1 : P B) (Q : P B -> Type) (H : Q f1) :=
  H.

Definition iota_J_0 (P : J -> Type) (f0 : P (makeJ true)) (f1 : P (makeJ false)) (Q : P (makeJ true) -> Type) (H : Q f0) :=
  H.

Definition iota_J_1 (P : J -> Type) (f0 : P (makeJ true)) (f1 : P (makeJ false)) (Q : P (makeJ false) -> Type) (H : Q f1) :=
  H.

(* --- Equivalence --- *)

(*
 * Automatic configuration also does this part automatically,
 * but here we used manual configuration.
 *
 * For now, manual configuration doesn't construct the
 * equivalence, so you need to construct it yourself.
 * A bit silly! Should fix this soon. After all,
 * it's a really simple algorithm. Our two functions
 * eliminate over one type and construct the other:
 *)
Definition f (i : I) : J :=
  dep_elim_I (fun _ => J) dep_constr_J_0 dep_constr_J_1 i.

Definition g (j : J) : I :=
  dep_elim_J (fun _ => I) dep_constr_I_0 dep_constr_I_1 j.

(*
 * And our two proofs eliminate over one type and reduce using the iota reduction rules:
 *)
Definition section (i : I) : g (f i) = i :=
  dep_elim_I
    (fun i => g (f i) = i)
    (iota_I_0 (fun _ => J) dep_constr_J_0 dep_constr_J_1 (fun j => g j = g dep_constr_J_0) eq_refl)
    (iota_I_1 (fun _ => J) dep_constr_J_0 dep_constr_J_1 (fun j => g j = g dep_constr_J_1) eq_refl)
    i.

Definition retraction (j : J) : f (g j) = j :=
  dep_elim_J
    (fun j => f (g j) = j)
    (iota_J_0 (fun _ => I) dep_constr_I_0 dep_constr_I_1 (fun i => f i = f dep_constr_I_0) eq_refl)
    (iota_J_1 (fun _ => I) dep_constr_I_0 dep_constr_I_1 (fun i => f i = f dep_constr_I_1) eq_refl)
    j.

(* --- Saving the configuration and equivalence --- *)

(*
 * Then we just save that:
 *)
Save equivalence I J { promote = f; forget = g }.

Configure Lift I J {
  constrs_a = dep_constr_I_0 dep_constr_I_1;
  constrs_b = dep_constr_J_0 dep_constr_J_1;
  elim_a = dep_elim_I;
  elim_b = dep_elim_J;
  eta_a = eta_I;
  eta_b = eta_J;
  iota_a = iota_I_0 iota_I_1;
  iota_b = iota_J_0 iota_J_1
}.

(* --- Repairing the functions and proofs --- *)

(*
 * Now we repair the module:
 *)
Repair Module I J in Old as New { hint "auto" }.

(*
 * Our functions behave the same way, but are defined over J instead of I:
 *)
Print New.and.
Lemma and_OK: 
  forall (j1 j2 : J),
    New.and j1 j2 = f (Old.and (g j1) (g j2)).
Proof.
  intros. induction j1. induction b; auto.
  simpl. rewrite retraction. auto.
Defined.

Print New.or.
Lemma or_OK: 
  forall (j1 j2 : J),
    New.or j1 j2 = f (Old.or (g j1) (g j2)).
Proof.
  intros. induction j1. induction b; auto.
  simpl. rewrite retraction. auto.
Defined.

Print New.neg.
Lemma neg_OK: 
  forall (j : J),
    New.neg j = f (Old.neg (g j)).
Proof.
  intros. induction j. induction b; auto.
Defined.

(*
 * And our proofs still hold:
 *)
Check New.demorgan_1.
Check New.demorgan_2.

(* --- Using suggested tactics --- *)

(*
 * Let's use the suggested tactics from Repair (up to renaming):
 *)
Theorem demorgan_1:
  forall j1 j2 : J, 
    New.neg (New.and j1 j2) = New.or (New.neg j1) (New.neg j2).
Proof.
  intros j1 j2. induction j1 as [b].
  induction b as [ | ]; auto.
Defined.

Theorem demorgan_2:
  forall j1 j2 : J,
    New.neg (New.or j1 j2) = New.and (New.neg j1) (New.neg j2).
Proof.
  intros j1 j2. induction j1 as [b].
  induction b as [ | ]; auto.
Defined.

(* --- Manual effort --- *)

(*
 * How hard is this to do manually?
 * (Using pattern matching even though the tool uses eliminators.)
 * Start time: 18:05
 * End time: 18:13
 * So we get 8 minutes of savings, but with a small overhead of writing the
 * configuration above.
 *)
Definition and' (i1 i2 : J) : J :=
  match i1 with
  | makeJ true => i2
  | makeJ false => makeJ false
  end.

Definition or' (i1 i2 : J) : J :=
  match i1 with
  | makeJ true => makeJ true
  | makeJ false => i2
  end.

Definition neg' (i : J) : J :=
  match i with
  | makeJ true => makeJ false
  | makeJ false => makeJ true
  end.

Theorem demorgan_1':
  forall (i1 i2 : J), 
    neg' (and' i1 i2) =
    or' (neg' i1) (neg' i2).
Proof.
  intros i1 i2. induction i1; auto.
  induction b; auto.
Defined.

Theorem demorgan_2':
  forall (i1 i2 : J), 
    neg' (or' i1 i2) =
    and' (neg' i1) (neg' i2).
Proof.
  intros i1 i2. induction i1; auto.
  induction b; auto.
Defined.

(* --- Note on opposite direction ---*)

(*
 * In the opposite direction, we can used cached terms,
 * but if we want to get around matching problems entirely,
 * we can just define a different configuration with the
 * natural eliminator for J.
 *)