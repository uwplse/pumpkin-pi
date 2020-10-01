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

Definition dep_constr_I_0 : I := A.
Definition dep_constr_I_1 : I := B.

Definition dep_constr_J_0 : J := makeJ true.
Definition dep_constr_J_1 : J := makeJ false.

Definition eta_I (i : I) : I := i.
Definition eta_J (j : J) : J := j.

Definition dep_elim_I P f0 f1 i : P (eta_I i) :=
  I_rect P f0 f1 i.

Definition dep_elim_J P f0 f1 j : P (eta_J j) :=
  J_rect P (fun b => bool_rect _ f0 f1 b) j.

Definition iota_I_0 (P : I -> Type) (f0 : P A) (f1 : P B) (Q : P A -> Type) (H : Q f0) :=
  H.

Definition iota_I_1 (P : I -> Type) (f0 : P A) (f1 : P B) (Q : P B -> Type) (H : Q f1) :=
  H.

Definition iota_J_0 (P : J -> Type) (f0 : P (makeJ true)) (f1 : P (makeJ false)) (Q : P (makeJ true) -> Type) (H : Q f0) :=
  H.

Definition iota_J_1 (P : J -> Type) (f0 : P (makeJ true)) (f1 : P (makeJ false)) (Q : P (makeJ false) -> Type) (H : Q f1) :=
  H.

(*
 * For now, manual configuration doesn't construct the
 * equivalence, so you need to construct it yourself.
 * A bit silly! Should fix this soon. After all,
 * it's a really simple algorithm:
 *)
Definition f (i : I) : J :=
  dep_elim_I (fun _ => J) dep_constr_J_0 dep_constr_J_1 i.

Definition g (j : J) : I :=
  dep_elim_J (fun _ => I) dep_constr_I_0 dep_constr_I_1 j.

(* The iotas below could also be eq_refls, but just to make a point I'll expand them *)
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

Save equivalence I J { promote = f; forget = g }.

(*
 * OK now we can do this:
 *)
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

(*
 * Now we lift the module:
 *)
Repair Module I J in Old as New.

Print New.and.
Print New.or.
Print New.neg.
Check New.demorgan_1.
Check New.demorgan_2.

(*
 * Let's use the suggested tactics:
 *)
Theorem demorgan_1:
  forall j1 j2 : J, 
    New.neg (New.and j1 j2) = New.or (New.neg j1) (New.neg j2).
Proof.
  intros i1 i2. induction i1 as [b].
  induction b as [ | ]; reflexivity.
Defined.

Theorem demorgan_2:
  forall j1 j2 : J,
    New.neg (New.or j1 j2) = New.and (New.neg j1) (New.neg j2).
Proof.
  intros j1 j2. induction j1 as [b].
  induction b as [ | ]; reflexivity.
Defined.

(*
 * In the opposite direction, we can used cached terms,
 * but if we want to get around matching problems entirely,
 * we can just define a different configuration with the
 * natural eliminator for J.
 *)