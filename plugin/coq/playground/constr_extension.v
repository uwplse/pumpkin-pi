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

(* --- No new inductive information --- *)

(* TODO *)

(* --- New inductive information --- *)

(* TODO *)
