Require Import Relation_Definitions Morphisms.

Definition START_REWRITE {A B : Type} {a1 a2 : A} {eq : relation A} (H : eq a1 a2) (H2 : Type) (x : B) := x.

Ltac rewrite_annotate H :=
  match goal with
  | [ |- ?H2 ] =>
      apply (START_REWRITE H H2); rewrite H
  | _ => idtac
  end.

Ltac solve3 x t :=
  match goal with
  | |- respectful _ _ _ _ =>
    let H := fresh "H" in
    intros ? ? H; solve3 x ltac:(try setoid_rewrite H; t)
  | _ => t; induction x; simpl; (try (f_equiv; auto); try (t; reflexivity))
  end.

Ltac solve2 x t :=
  match goal with
  | |- Proper _ _ =>
    unfold Proper; solve3 x t
  | _ => 
    let H := fresh "H" in
    intros H ?; solve2 x ltac:(try setoid_rewrite H; t)
  end.

Ltac solve_elim_proper :=
  let x := fresh "x" in
  intros x; solve2 x ltac:(idtac).

Ltac solve_respectful2 t :=
 match goal with
   | |- respectful _ _ _ _ =>
     let H := fresh "H" in
     intros ? ? H; solve_respectful ltac:(try setoid_rewrite H; t)
   | _ => t; reflexivity
 end.

Ltac solve_proper2 :=
  timeout 3 (unfold Proper; solve_respectful2 ltac:(idtac)).
