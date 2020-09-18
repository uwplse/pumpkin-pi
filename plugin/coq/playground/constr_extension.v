Add LoadPath "coq/playground".
Require Import List.
Require Import Ornamental.Ornaments.

Set DEVOID search prove equivalence.
Set DEVOID lift type.

(*
 * Attempts at figuring equivalences that correspond to constructor extension,
 * and the corresponding eliminator transformation, so we can make a good
 * interface for asking the user for exactly the new information that is needed,
 * and inferring it when possible.
 *)

(* --- No new information --- *)

Module NoNewInformation.

Inductive list_ext (A : Type) : Type :=
| nil_ext : list_ext A
| cons_ext : A -> list_ext A -> list_ext A
| nil_ext2 : list_ext A.

(*
 * This version gets you from proofs about list to proofs about list_ext, but
 * just ignores the nil_ext2 case:
 *)

Program Definition list_ext_inv (A : Type) (l : list_ext A) : Prop.
Proof.
  induction l.
  - apply True.
  - apply IHl.
  - apply False.
Defined.

Program Definition list_list_ext :
  forall (A : Type), list A -> sigT (fun (l : list_ext A) => list_ext_inv A l).
Proof.
  intros A l. induction l.
  - exists (nil_ext A). simpl. auto.
  - exists (cons_ext A a (projT1 IHl)). simpl.
    destruct IHl. simpl. auto.
Defined.

Program Definition list_ext_list :
  forall (A : Type), sigT (fun (l : list_ext A) => list_ext_inv A l) -> list A.
Proof.
  intros A lp. induction lp. induction x.
  - apply nil.
  - apply cons.
    + apply a.
    + apply IHx. simpl in p. apply p.
  - inversion p. 
Defined.

Lemma list_list_ext_cons:
  forall (A : Type) (a : A) (l : list A),
    list_list_ext A (a :: l) =
    existT (fun (l : list_ext A) => list_ext_inv A l) (cons_ext A a (projT1 (list_list_ext A l))) (projT2 (list_list_ext A l)).
Proof.
  intros A a l. simpl. auto.
Defined.

Lemma list_ext_list_cons:
  forall (A : Type) (a : A) (l : sigT (fun (l : list_ext A) => list_ext_inv A l)),
    list_ext_list A (existT (fun l => list_ext_inv A l) (cons_ext A a (projT1 l)) (projT2 l)) =
    a :: list_ext_list A (existT (fun l => list_ext_inv A l) (projT1 l) (projT2 l)).
Proof.
  intros A a l. simpl. auto.
Defined.

Lemma list_ext_eta:
  forall (A : Type) (l : sigT (fun (l : list_ext A) => list_ext_inv A l)),
    existT (fun (l : list_ext A) => list_ext_inv A l) (projT1 l) (projT2 l) =
    l.
Proof.
  intros. induction l. auto.
Defined.

Program Definition list_list_ext_section :
  forall (A : Type) (l : list A), list_ext_list A (list_list_ext A l) = l.
Proof.
  intros A l. induction l.
  - reflexivity.
  - rewrite list_list_ext_cons. rewrite list_ext_list_cons. rewrite list_ext_eta.
    rewrite IHl. auto.
Defined.

Program Definition list_list_ext_retraction: 
  forall (A : Type) (pl : sigT (fun (l : list_ext A) => list_ext_inv A l)), list_list_ext A (list_ext_list A pl) = pl.
Proof.
  intros A l. induction l. induction x.
  - simpl. simpl in p. destruct p. auto.
  - compute. compute in IHx. rewrite IHx. auto.
  - simpl. destruct p.
Defined.

(*
 * This version asks you for the extra information needed to get your list proofs
 * to proofs about list_ext (TODO what is this?)
 *)

Inductive list_missing (A : Type) : Type :=
| missing_nil2 : list_missing A.

Definition list_missing_inv (A : Type) (lo : option (list_missing A)) : Type :=
  match lo with
  | Some l => prod (list A) (list_missing A)
  | None => list A
  end.

Program Definition list_list_ext' :
  forall (A : Type), sigT (fun lo => list_missing_inv A lo) -> list_ext A.
Proof.
  intros A s. induction s. induction x.
  - induction p. induction a0.
    + apply nil_ext2.
    + apply cons_ext.
      * apply a0.
      * apply IHa0. 
  - induction p.
    + apply nil_ext.
    + apply cons_ext.
      * apply a.
      * apply IHp.
Defined.

Program Definition list_ext_list' :
  forall (A : Type), list_ext A -> sigT (fun lo => list_missing_inv A lo).
Proof.
  intros A l. induction l.
  - exists None. apply nil.
  - induction IHl. induction x.
    + exists (Some a0). induction p.
      simpl. apply pair. apply (cons a a1). apply b.
    + exists None. apply (cons a p). 
  - exists (Some (missing_nil2 A)). simpl.
    apply pair.
    + apply nil.
    + apply (missing_nil2 A).
Defined.

Program Definition list_list_ext_section' :
  forall (A : Type) lo, list_ext_list' A (list_list_ext' A lo) = lo.
Proof.
  intros A lo. induction lo. destruct x.
  - simpl. induction p. induction a.
    + simpl. induction b. induction l. reflexivity.
    + compute. compute in IHa. rewrite IHa. auto.
  - simpl. induction p.
    + simpl. auto.
    + compute. compute in IHp. rewrite IHp. auto.
Defined.

Program Definition list_list_ext_retraction': 
  forall (A : Type) l, list_list_ext' A (list_ext_list' A l) = l.
Proof.
  intros A l. induction l.
  - simpl. auto.
  - simpl. remember (list_ext_list' A l) as l'. induction l'. simpl.
    induction x.
    + induction p. simpl. rewrite <- IHl. simpl. auto.
    + simpl. rewrite <- IHl. simpl. auto.
  - simpl. auto.
Defined.

End NoNewInformation.

(* --- 9/17: Playing with a Reviewer A example --- *)

(*
 * Everything above this point is from February.
 * I just think this fits most nicely into this file.
 *)

Inductive I :=
| A : I
| B : I.

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
 * Simple lifting tests:
 *)
Lift I J in A as A_lifted.
Lift I J in B as B_lifted.

Lemma A_lift_correct:
  A_lifted = makeJ true.
Proof.
  reflexivity.
Defined.

Lemma B_lift_correct:
  B_lifted = makeJ false.
Proof.
  reflexivity.
Defined.

Lift I J in f as f_lifted.
Lift I J in g as g_lifted.

Lemma f_lifted_is_g_lifted:
  f_lifted = g_lifted.
Proof.
  reflexivity.
Defined.

Lift I J in section as section_lifted.
Lift I J in retraction as retraction_lifted.

Lemma section_lifted_is_retraction_lifted:
  section_lifted = retraction_lifted.
Proof.
  reflexivity.
Defined.

(*
 * In the opposite direction, we can used cached terms,
 * but if we want to get around matching problems entirely,
 * we can just define a different configuration with the
 * natural eliminator for J.
 *)

(* --- No new inductive information --- *)

(* TODO *)

(* --- New inductive information --- *)

(* TODO *)
