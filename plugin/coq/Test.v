Require Import List.
Require Import Ornamental.Ornaments.

Set DEVOID search prove coherence.
Set DEVOID search prove equivalence.
Set DEVOID search smart eliminators.

(*--- Lists and Vectors ---*)

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

Definition packed_vector (T : Type) :=
  sigT (fun (n : nat) => vector T n).

Find ornament list vector as orn_list_vector.

Theorem test_index:
  forall (A : Type) (l : list A),
    orn_list_vector_index A l = length l.
Proof.
  intros. auto.
Qed.

Theorem test_orn:
  forall (A : Type) (l : list A),
    packed_vector A.
Proof.
  exact orn_list_vector.
Qed.

Theorem test_orn_index:
  forall (A : Type) (l : list A),
    projT1 (orn_list_vector A l) = orn_list_vector_index A l.
Proof.
  exact orn_list_vector_coh.
Qed.

Theorem test_orn_inv:
  forall (A : Type) (v : packed_vector A),
    list A.
Proof.
  exact orn_list_vector_inv.
Qed.

Theorem test_orn_inv_unpack:
  forall (A : Type) (n : nat) (v : vector A n),
    list A.
Proof.
  intros. apply orn_list_vector_inv. exists n. apply v.
Qed.

Theorem test_section:
  forall (A : Type) (l : list A),
    orn_list_vector_inv A (orn_list_vector A l) = l.
Proof.
  exact orn_list_vector_section.
Qed.

Theorem test_retraction:
  forall (A : Type) (v : packed_vector A),
    orn_list_vector A (orn_list_vector_inv A v) = v.
Proof.
  exact orn_list_vector_retraction.
Qed.

Theorem test_adjunction:
  forall (A : Type) (l : list A),
    orn_list_vector_retraction_adjoint A (orn_list_vector A l) =
    f_equal (orn_list_vector A) (orn_list_vector_section A l).
Proof.
  exact orn_list_vector_adjunction.
Qed.

(* --- Test auto-generated ornament name --- *)

Find ornament list vector.

Theorem test_index_auto:
  forall (A : Type) (l : list A),
    list_to_vector_index A l = length l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_auto:
  forall (A : Type) (l : list A),
    packed_vector A.
Proof.
  exact list_to_vector.
Qed.

Theorem test_orn_index_auto:
  forall (A : Type) (l : list A),
    projT1 (list_to_vector A l) = list_to_vector_index A l.
Proof.
  exact list_to_vector_coh.
Qed.

Theorem test_orn_inv_auto:
  forall (A : Type) (v : packed_vector A),
    list A.
Proof.
  exact list_to_vector_inv.
Qed.

Theorem test_orn_inv_unpack_auto:
  forall (A : Type) (n : nat) (v : vector A n),
    list A.
Proof.
  intros. apply list_to_vector_inv. exists n. apply v.
Qed.

Theorem test_section_auto:
  forall (A : Type) (l : list A),
    list_to_vector_inv A (list_to_vector A l) = l.
Proof.
  exact list_to_vector_section.
Qed.

Theorem test_retraction_auto:
  forall (A : Type) (v : packed_vector A),
    list_to_vector A (list_to_vector_inv A v) = v.
Proof.
  exact list_to_vector_retraction.
Qed.

Theorem test_adjunction_auto:
  forall (A : Type) (l : list A),
    list_to_vector_retraction_adjoint A (list_to_vector A l) =
    f_equal (list_to_vector A) (list_to_vector_section A l).
Proof.
  exact list_to_vector_adjunction.
Qed.

(* --- Lists and "flectors" --- *)

Module Type Even.
Parameter A : Type.
Parameter isEven : A -> bool.
End Even.

Module Flector (E : Even).
Definition A := E.A.
Definition isEven := E.isEven.
Definition SIfEven a n := if isEven a then S n else n.

Inductive flist : Type :=
| nilF : flist
| consF :
    forall (a : A),
      flist ->
      flist.

Inductive flector : nat -> Type :=
| nilFV : flector 0
| consFV :
    forall (n : nat) (a : A),
      flector n ->
      flector (SIfEven a n).

Find ornament flist flector as orn_flist_flector.

(* For testing *)
Definition countEven (l : flist) :=
  flist_rect
    (fun (_ : flist) => nat)
    0
    (fun (a : A) (l : flist) (IH : nat) =>
      SIfEven a IH)
    l.

Theorem test_index_flector:
  forall (l : flist),
    orn_flist_flector_index l = countEven l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_flector:
  forall (l : flist),
    sigT flector.
Proof.
  exact orn_flist_flector.
Qed.

Theorem test_orn_index_flector:
  forall (l : flist),
    projT1 (orn_flist_flector l) = orn_flist_flector_index l.
Proof.
  exact orn_flist_flector_coh.
Qed.

Theorem test_orn_inv_flector:
  forall (v : sigT flector),
    flist.
Proof.
  exact orn_flist_flector_inv.
Qed.

Theorem test_orn_inv_unpack_flector:
  forall (n : nat) (v : flector n),
    flist.
Proof.
  intros. apply orn_flist_flector_inv. exists n. apply v.
Qed.

Theorem test_section_flector:
  forall (l : flist),
    orn_flist_flector_inv (orn_flist_flector l) = l.
Proof.
  exact orn_flist_flector_section.
Qed.

Theorem test_retraction_flector:
  forall (v : sigT flector),
    orn_flist_flector (orn_flist_flector_inv v) = v.
Proof.
  exact orn_flist_flector_retraction.
Qed.

End Flector.

(* TODO temp while fixing module bug *)
Module natEven <: Even.
Definition A := nat.
Definition isEven (n : nat) :=
  nat_rect
    (fun (_ : nat) => bool)
    true
    (fun (_ : nat) (IH : bool) =>
      negb IH)
    n.
End natEven.

Module natFlector := Flector natEven.

Definition orn_flist_flector_nat := natFlector.orn_flist_flector.
Definition orn_flist_flector_nat_inv := natFlector.orn_flist_flector_inv.
Definition orn_flist_flector_nat_index := natFlector.orn_flist_flector_index.

(* --- Backwards lists --- *)

Inductive rev_list (A : Type) : Type :=
| rev_nil : rev_list A
| rev_cons : rev_list A -> A -> rev_list A.

Inductive rev_vector (A : Type) : nat -> Type :=
| rev_nilV : rev_vector A 0
| rev_consV : forall (n : nat), rev_vector A n -> A -> rev_vector A (S n).

Definition packed_rev_vector (T : Type) :=
  sigT (A := nat) (fun (n : nat) => rev_vector T n).

Find ornament rev_list rev_vector as orn_rev_list_rev_vector.

Definition rev_list_length (A : Type) (rl : rev_list A) :=
  rev_list_rect
    A
    (fun (_ : rev_list A) => nat)
    0
    (fun (r : rev_list A) (n : nat) (a : A) =>
      S n)
    rl.

Theorem test_index_2:
  forall (A : Type) (l : rev_list A),
    orn_rev_list_rev_vector_index A l = rev_list_length A l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_2:
  forall (A : Type) (l : rev_list A),
    packed_rev_vector A.
Proof.
  exact orn_rev_list_rev_vector.
Qed.

Theorem test_orn_index_2:
  forall (A : Type) (l : rev_list A),
    projT1 (orn_rev_list_rev_vector A l) = orn_rev_list_rev_vector_index A l.
Proof.
  exact orn_rev_list_rev_vector_coh.
Qed.

Theorem test_orn_inv_2:
  forall (A : Type) (l : packed_rev_vector A),
    rev_list A.
Proof.
  exact orn_rev_list_rev_vector_inv.
Qed.

Theorem test_orn_inv_unpack_2:
  forall (A : Type) (n : nat) (v : rev_vector A n),
    rev_list A.
Proof.
  intros. apply orn_rev_list_rev_vector_inv. exists n. apply v.
Qed.

Theorem test_section_2:
  forall (A : Type) (l : rev_list A),
    orn_rev_list_rev_vector_inv A (orn_rev_list_rev_vector A l) = l.
Proof.
  exact orn_rev_list_rev_vector_section.
Qed.

Theorem test_retraction_2:
  forall (A : Type) (l : packed_rev_vector A),
    orn_rev_list_rev_vector A (orn_rev_list_rev_vector_inv A l) = l.
Proof.
  exact orn_rev_list_rev_vector_retraction.
Qed.

Theorem test_adjunction_2:
  forall (A : Type) (l : rev_list A),
    orn_rev_list_rev_vector_retraction_adjoint A (orn_rev_list_rev_vector A l) =
    f_equal (orn_rev_list_rev_vector A) (orn_rev_list_rev_vector_section A l).
Proof.
  exact orn_rev_list_rev_vector_adjunction.
Qed.

(* --- Binary Trees and Indexed Binary Trees --- *)

Inductive bintree (A : Type) : Type :=
| leaf :
    bintree A
| node :
    bintree A -> A -> bintree A -> bintree A.

Inductive bintreeV (A : Type) : nat -> Type :=
| leafV :
    bintreeV A 0
| nodeV :
    forall (n m : nat),
      bintreeV A n -> A -> bintreeV A m -> bintreeV A (S (n + m)).

Definition packed_bintreeV (T : Type) :=
  sigT (A := nat) (fun (n : nat) => bintreeV T n).

Find ornament bintree bintreeV as orn_bintree_bintreeV.

Definition bintree_size (A : Type) (tr : bintree A) :=
  bintree_rect
    A
    (fun (_ : bintree A) => nat)
    0
    (fun (l : bintree A) (nl : nat) (a : A) (r : bintree A) (nr : nat) =>
      S (nl + nr))
    tr.

Theorem test_index_3:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_index A tr = bintree_size A tr.
Proof.
  intros. auto.
Qed.

Theorem test_orn_3:
  forall (A : Type) (tr : bintree A),
    packed_bintreeV A.
Proof.
  exact orn_bintree_bintreeV.
Qed.

Theorem test_orn_index_3:
  forall (A : Type) (tr : bintree A),
    projT1 (orn_bintree_bintreeV A tr) = orn_bintree_bintreeV_index A tr.
Proof.
  exact orn_bintree_bintreeV_coh.
Qed.

Theorem test_orn_inv_3:
  forall (A : Type) (tr : packed_bintreeV A),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_inv.
Qed.

Theorem test_orn_inv_unpack_3:
  forall (A : Type) (n : nat) (tr : bintreeV A n),
    bintree A.
Proof.
  intros. apply orn_bintree_bintreeV_inv. exists n. apply tr.
Qed.

Theorem test_section_3:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_inv A (orn_bintree_bintreeV A tr) = tr.
Proof.
  exact orn_bintree_bintreeV_section.
Qed.

Theorem test_retraction_3:
  forall (A : Type) (tr : packed_bintreeV A),
    orn_bintree_bintreeV A (orn_bintree_bintreeV_inv A tr) = tr.
Proof.
  exact orn_bintree_bintreeV_retraction.
Qed.

Theorem test_adjunction_3:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_retraction_adjoint A (orn_bintree_bintreeV A tr) =
    f_equal (orn_bintree_bintreeV A) (orn_bintree_bintreeV_section A tr).
Proof.
  exact orn_bintree_bintreeV_adjunction.
Qed.

(* --- Lists of values of two types (making sure parameter logic works) --- *)

Inductive list2 (A : Type) (B : Type) : Type :=
| nil2 : list2 A B
| cons2 : A -> B -> list2 A B -> list2 A B.

Inductive vector2 (A : Type) (B : Type) : nat -> Type :=
| nilV2 : vector2 A B 0
| consV2 : forall (n : nat), A -> B -> vector2 A B n -> vector2 A B (S (S n)).

Definition packed_vector2 (A : Type) (B : Type) :=
  sigT (A := nat) (fun (n : nat) => vector2 A B n).

Definition length2 (A : Type) (B : Type) (l : list2 A B) :=
  list2_rect
    A
    B
    (fun (_ : list2 A B) => nat)
    0
    (fun (a : A) (b : B) (l' : list2 A B) (IH : nat) =>
      S (S IH))
    l.

Find ornament list2 vector2 as orn_list2_vector2.

Theorem test_index_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    orn_list2_vector2_index A B l = length2 A B l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    packed_vector2 A B.
Proof.
  exact orn_list2_vector2.
Qed.

Theorem test_orn_index_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    projT1 (orn_list2_vector2 A B l) = orn_list2_vector2_index A B l.
Proof.
  exact orn_list2_vector2_coh.
Qed.

Theorem test_orn_inv_4:
  forall (A : Type) (B : Type) (l : packed_vector2 A B),
    list2 A B.
Proof.
  exact orn_list2_vector2_inv.
Qed.

Theorem test_orn_inv_unpack_4:
  forall (A : Type) (B : Type) (n : nat) (l : vector2 A B n),
    list2 A B.
Proof.
  intros. apply orn_list2_vector2_inv. exists n. apply l.
Qed.

Theorem test_section_4:
  forall (A : Type) (B : Type) (l : list2 A B),
    orn_list2_vector2_inv A B (orn_list2_vector2 A B l) = l.
Proof.
  exact orn_list2_vector2_section.
Qed.

Theorem test_retraction_4:
  forall (A : Type) (B : Type) (l : packed_vector2 A B),
    orn_list2_vector2 A B (orn_list2_vector2_inv A B l) = l.
Proof.
  exact orn_list2_vector2_retraction.
Qed.

Theorem test_adjunction_4:
  forall (A B : Type) (l : list2 A B),
    orn_list2_vector2_retraction_adjoint A B (orn_list2_vector2 A B l) =
    f_equal (orn_list2_vector2 A B) (orn_list2_vector2_section A B l).
Proof.
  exact orn_list2_vector2_adjunction.
Qed.

(* --- Adding a nat index to a nat list --- *)

Inductive nat_list : Type :=
| nat_nil : nat_list
| nat_cons : nat -> nat_list -> nat_list.

Inductive nat_vector : nat -> Type :=
| nat_nilV : nat_vector 0
| nat_consV : forall (n : nat), nat -> nat_vector n -> nat_vector (S n).

Definition packed_nat_vector :=
  sigT (A := nat) (fun (n : nat) => nat_vector n).

Find ornament nat_list nat_vector as orn_natlist_natvector.

Definition nat_length (l : nat_list) :=
  nat_list_rect
    (fun (_ : nat_list) => nat)
    0
    (fun (_ : nat) (_ : nat_list) (IH : nat) =>
      S IH)
    l.

Theorem test_index_5:
  forall (l : nat_list),
    orn_natlist_natvector_index l = nat_length l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_5:
  forall (l : nat_list),
    packed_nat_vector.
Proof.
  exact orn_natlist_natvector.
Qed.

Theorem test_orn_index_5:
  forall (l : nat_list),
    projT1 (orn_natlist_natvector l) = orn_natlist_natvector_index l.
Proof.
  exact orn_natlist_natvector_coh.
Qed.

Theorem test_orn_inv_5:
  forall (v : packed_nat_vector),
    nat_list.
Proof.
  exact orn_natlist_natvector_inv.
Qed.

Theorem test_orn_inv_unpack_5:
  forall (n : nat) (v : nat_vector n),
    nat_list.
Proof.
  intros. apply orn_natlist_natvector_inv. exists n. apply v.
Qed.

Theorem test_section_5:
  forall (l : nat_list),
    orn_natlist_natvector_inv (orn_natlist_natvector l) = l.
Proof.
  exact orn_natlist_natvector_section.
Qed.

Theorem test_retraction_5:
  forall (v : packed_nat_vector),
    orn_natlist_natvector (orn_natlist_natvector_inv v) = v.
Proof.
  exact orn_natlist_natvector_retraction.
Qed.

Theorem test_adjunction_5:
  forall (l : nat_list),
    orn_natlist_natvector_retraction_adjoint (orn_natlist_natvector l) =
    f_equal orn_natlist_natvector (orn_natlist_natvector_section l).
Proof.
  exact orn_natlist_natvector_adjunction.
Qed.

(* --- BintreeV with nats in reverse order --- *)

Inductive bintreeV_rev (A : Type) : nat -> Type :=
| leafV_rev :
    bintreeV_rev A 0
| nodeV_rev :
    forall (n m : nat),
      bintreeV_rev A m -> A -> bintreeV_rev A n -> bintreeV_rev A (n + m).

Definition packed_bintreeV_rev (A : Type) :=
  sigT (A := nat) (fun (n : nat) => bintreeV_rev A n).

Definition bintree_size_rev (A : Type) (tr : bintree A) :=
  bintree_rect
    A
    (fun (_ : bintree A) => nat)
    0
    (fun (l : bintree A) (nl : nat) (a : A) (r : bintree A) (nr : nat) =>
      nr + nl)
    tr.

Find ornament bintree bintreeV_rev as orn_bintree_bintreeV_rev.

Theorem test_index_6:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_rev_index A tr = bintree_size_rev A tr.
Proof.
  intros. auto.
Qed.

Theorem test_orn_6:
  forall (A : Type) (tr : bintree A),
    packed_bintreeV_rev A.
Proof.
  exact orn_bintree_bintreeV_rev.
Qed.

Theorem test_orn_index_6:
  forall (A : Type) (tr : bintree A),
    projT1 (orn_bintree_bintreeV_rev A tr) = orn_bintree_bintreeV_rev_index A tr.
Proof.
  exact orn_bintree_bintreeV_rev_coh.
Qed.

Theorem test_orn_inv_6:
  forall (A : Type) (tr : packed_bintreeV_rev A),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_rev_inv.
Qed.

Theorem test_orn_inv_unpack_6:
  forall (A : Type) (n : nat) (tr : bintreeV_rev A n),
    bintree A.
Proof.
  intros. apply orn_bintree_bintreeV_rev_inv. exists n. apply tr.
Qed.

Theorem test_section_6:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_rev_inv A (orn_bintree_bintreeV_rev A tr) = tr.
Proof.
  exact orn_bintree_bintreeV_rev_section.
Qed.

Theorem test_retraction_6:
  forall (A : Type) (tr : packed_bintreeV_rev A),
    orn_bintree_bintreeV_rev A (orn_bintree_bintreeV_rev_inv A tr) = tr.
Proof.
  exact orn_bintree_bintreeV_rev_retraction.
Qed.

Theorem test_adjunction_6:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV_rev_retraction_adjoint A (orn_bintree_bintreeV_rev A tr) =
    f_equal (orn_bintree_bintreeV_rev A) (orn_bintree_bintreeV_rev_section A tr).
Proof.
  exact orn_bintree_bintreeV_rev_adjunction.
Qed.

(* --- Adding an index whose type that matches an already existing index --- *)

Inductive doublevector (A : Type) : nat -> nat -> Type :=
| dnilV : doublevector A 0 0
| dconsV :
    forall (n m : nat),
      A -> doublevector A n m -> doublevector A (S (S n)) (S m).

Definition packed_doublevector (A : Type) (m : nat) :=
  sigT (A := nat) (fun n : nat => doublevector A n m).

Find ornament vector doublevector as orn_vector_doublevector.

Definition vector_double_size (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n : nat) (v : vector A n) => nat)
    O
    (fun (n : nat) (a : A) (v : vector A n) (IH : nat) =>
      S (S IH))
    n
    v.

Theorem test_index_7:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector_index A n v = vector_double_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_7:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector A n.
Proof.
  exact orn_vector_doublevector.
Qed.

Theorem test_orn_index_7:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector A n v) = orn_vector_doublevector_index A n v.
Proof.
  exact orn_vector_doublevector_coh.
Qed.

Theorem test_orn_inv_7:
  forall (A : Type) (m : nat) (d : packed_doublevector A m),
    vector A m.
Proof.
  exact orn_vector_doublevector_inv.
Qed.

Theorem test_orn_inv_unpack_7:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector A n m),
    vector A m.
Proof.
  intros. apply orn_vector_doublevector_inv. exists n. apply d.
Qed.

Theorem test_section_7:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector_inv A n (orn_vector_doublevector A n v) = v.
Proof.
  exact orn_vector_doublevector_section.
Qed.

Theorem test_retraction_7:
  forall (A : Type) (n : nat) (v : packed_doublevector A n),
    orn_vector_doublevector A n (orn_vector_doublevector_inv A n v) = v.
Proof.
  exact orn_vector_doublevector_retraction.
Qed.

Theorem test_adjunction_7:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector_retraction_adjoint A n (orn_vector_doublevector A n v) =
    f_equal (orn_vector_doublevector A n) (orn_vector_doublevector_section A n v).
Proof.
  exact orn_vector_doublevector_adjunction.
Qed.

(* --- Same as above, but switch the position we change --- *)

Inductive doublevector2 (A : Type) : nat -> nat -> Type :=
| dnilV2 : doublevector2 A 0 0
| dconsV2 :
    forall (n m : nat),
      A -> doublevector2 A n m -> doublevector2 A (S n) (S (S m)).

Definition packed_doublevector2 (A : Type) (n : nat) :=
  sigT (A := nat) (fun (m : nat) => doublevector2 A n m).

Find ornament vector doublevector2 as orn_vector_doublevector2.

Theorem test_index_8:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector2_index A n v = vector_double_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_8:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector2 A n.
Proof.
  exact orn_vector_doublevector2.
Qed.

Theorem test_orn_index_8:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector2 A n v) = orn_vector_doublevector2_index A n v.
Proof.
  exact orn_vector_doublevector2_coh.
Qed.

Theorem test_orn_inv_8:
  forall (A : Type) (n : nat) (d : packed_doublevector2 A n),
    vector A n.
Proof.
  exact orn_vector_doublevector2_inv.
Qed.

Theorem test_orn_inv_unpack_8:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector2 A n m),
    vector A n.
Proof.
  intros. apply orn_vector_doublevector2_inv. exists m. apply d.
Qed.

Theorem test_section_8:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector2_inv A n (orn_vector_doublevector2 A n v) = v.
Proof.
  exact orn_vector_doublevector2_section.
Qed.

Theorem test_retraction_8:
  forall (A : Type) (n : nat) (v : packed_doublevector2 A n),
    orn_vector_doublevector2 A n (orn_vector_doublevector2_inv A n v) = v.
Proof.
  exact orn_vector_doublevector2_retraction.
Qed.

Theorem test_adjunction_8:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector2_retraction_adjoint A n (orn_vector_doublevector2 A n v) =
    f_equal (orn_vector_doublevector2 A n) (orn_vector_doublevector2_section A n v).
Proof.
  exact orn_vector_doublevector2_adjunction.
Qed.

(* --- Same as above, but with an identical index --- *)

Inductive doublevector3 (A : Type) : nat -> nat -> Type :=
| dnilV3 : doublevector3 A 0 0
| dconsV3 :
    forall (n m : nat),
      A -> doublevector3 A n m -> doublevector3 A (S n) (S m).

Definition packed_doublevector3 (A : Type) (n : nat) :=
  sigT (A := nat) (fun (m : nat) => doublevector3 A n m).

Find ornament vector doublevector3 as orn_vector_doublevector3.

Definition vector_size (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n : nat) (v : vector A n) => nat)
    O
    (fun (n : nat) (a : A) (v : vector A n) (IH : nat) =>
      S IH)
    n
    v.

Theorem test_index_9:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector3_index A n v = vector_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_9:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector3 A n.
Proof.
  exact orn_vector_doublevector3.
Qed.

Theorem test_orn_index_9:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector3 A n v) = orn_vector_doublevector3_index A n v.
Proof.
  exact orn_vector_doublevector3_coh.
Qed.

Theorem test_orn_inv_9:
  forall (A : Type) (n : nat) (d : packed_doublevector3 A n),
    vector A n.
Proof.
  exact orn_vector_doublevector3_inv.
Qed.

Theorem test_orn_inv_unpack_9:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector3 A n m),
    vector A n.
Proof.
  intros. apply orn_vector_doublevector3_inv. exists m. apply d.
Qed.

Theorem test_section_9:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector3_inv A n (orn_vector_doublevector3 A n v) = v.
Proof.
  exact orn_vector_doublevector3_section.
Qed.

Theorem test_retraction_9:
  forall (A : Type) (n : nat) (v : packed_doublevector3 A n),
    orn_vector_doublevector3 A n (orn_vector_doublevector3_inv A n v) = v.
Proof.
  exact orn_vector_doublevector3_retraction.
Qed.

Theorem test_adjunction_9:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector3_retraction_adjoint A n (orn_vector_doublevector3 A n v) =
    f_equal (orn_vector_doublevector3 A n) (orn_vector_doublevector3_section A n v).
Proof.
  exact orn_vector_doublevector3_adjunction.
Qed.


(* --- What if we change a base case index? --- *)

Inductive doublevector4 (A : Type) : nat -> nat -> Type :=
| dnilV4 : doublevector4 A 1 0
| dconsV4 :
    forall (n m : nat),
      A -> doublevector4 A n m -> doublevector4 A (S n) (S m).

Definition packed_doublevector4 (A : Type) (m : nat) :=
  sigT (A := nat) (fun (n : nat) => doublevector4 A n m).

Find ornament vector doublevector4 as orn_vector_doublevector4.

Definition S_vector_size (A : Type) (n : nat) (v : vector A n) :=
  vector_rect
    A
    (fun (n : nat) (v : vector A n) => nat)
    1
    (fun (n : nat) (a : A) (v : vector A n) (IH : nat) =>
      S IH)
    n
    v.

Theorem test_index_10:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector4_index A n v = S_vector_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_10:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector4 A n.
Proof.
  exact orn_vector_doublevector4.
Qed.

Theorem test_orn_index_10:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector4 A n v) = orn_vector_doublevector4_index A n v.
Proof.
  exact orn_vector_doublevector4_coh.
Qed.

Theorem test_orn_inv_10:
  forall (A : Type) (m : nat) (d : packed_doublevector4 A m),
    vector A m.
Proof.
  exact orn_vector_doublevector4_inv.
Qed.

Theorem test_orn_inv_unpack_10:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector4 A n m),
    vector A m.
Proof.
  intros. apply orn_vector_doublevector4_inv. exists n. apply d.
Qed.

Theorem test_section_10:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector4_inv A n (orn_vector_doublevector4 A n v) = v.
Proof.
  exact orn_vector_doublevector4_section.
Qed.

Theorem test_retraction_10:
  forall (A : Type) (n : nat) (v : packed_doublevector4 A n),
    orn_vector_doublevector4 A n (orn_vector_doublevector4_inv A n v) = v.
Proof.
  exact orn_vector_doublevector4_retraction.
Qed.

Theorem test_adjunction_10:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector4_retraction_adjoint A n (orn_vector_doublevector4 A n v) =
    f_equal (orn_vector_doublevector4 A n) (orn_vector_doublevector4_section A n v).
Proof.
  exact orn_vector_doublevector4_adjunction.
Qed.

(* --- Indices that are computed from existing hypotheses --- *)

Inductive hd_nat_list : nat -> Type :=
| hd_nat_nil : hd_nat_list 0
| hd_nat_cons :
    forall (m : nat) (n : nat),
      hd_nat_list m ->
      hd_nat_list n.

Definition packed_hd_nat_list :=
  sigT (A := nat) (fun (n : nat) => hd_nat_list n).

Find ornament nat_list hd_nat_list as orn_natlist_hdnatlist.

Definition nat_list_hd (nl : nat_list) :=
  nat_list_rect
    (fun (_ : nat_list) => nat)
    0
    (fun (n : nat) (_ : nat_list) (_ : nat) =>
      n)
    nl.

Theorem test_index_11:
  forall (nl : nat_list),
    nat_list_hd nl = orn_natlist_hdnatlist_index nl.
Proof.
  intros. auto.
Qed.

Theorem test_orn_11:
  forall (nl : nat_list),
    packed_hd_nat_list.
Proof.
  exact orn_natlist_hdnatlist.
Qed.

Theorem test_orn_index_11:
  forall (nl : nat_list),
    projT1 (orn_natlist_hdnatlist nl) = orn_natlist_hdnatlist_index nl.
Proof.
  exact orn_natlist_hdnatlist_coh.
Qed.

Theorem test_orn_inv_11:
  forall (hnl : packed_hd_nat_list),
    nat_list.
Proof.
  exact orn_natlist_hdnatlist_inv.
Qed.

Theorem test_orn_inv_unpack_11:
  forall (h : nat) (hnl : hd_nat_list h),
    nat_list.
Proof.
  intros. apply orn_natlist_hdnatlist_inv. exists h. apply hnl.
Qed.

Theorem test_section_11:
  forall (nl : nat_list),
    orn_natlist_hdnatlist_inv (orn_natlist_hdnatlist nl) = nl.
Proof.
  exact orn_natlist_hdnatlist_section.
Qed.

Theorem test_retraction_11:
  forall (nl : packed_hd_nat_list),
    orn_natlist_hdnatlist (orn_natlist_hdnatlist_inv nl) = nl.
Proof.
  exact orn_natlist_hdnatlist_retraction.
Qed.

Theorem test_adjunction_11:
  forall (nl : nat_list),
    orn_natlist_hdnatlist_retraction_adjoint (orn_natlist_hdnatlist nl) =
    f_equal orn_natlist_hdnatlist (orn_natlist_hdnatlist_section nl).
Proof.
  exact orn_natlist_hdnatlist_adjunction.
Qed.

(* --- Indices that depend on parameters --- *)

Inductive hd_list (A : Type) : option A -> Type :=
| hd_nil : hd_list A None
| hd_cons :
    forall (ao : option A) (a : A),
      hd_list A ao ->
      hd_list A (Some a).

Definition packed_hd_list (T : Type) :=
  sigT (A := option T) (fun (h : option T) => hd_list T h).

Find ornament list hd_list as orn_list_hdlist.

Theorem test_index_12:
  forall (A : Type) (l : list A),
    hd_error l = orn_list_hdlist_index A l.
Proof.
  intros. induction l; auto. (* not reducable because only one is a fix *)
Qed.

Theorem test_orn_12:
  forall (A : Type) (l : list A),
    packed_hd_list A.
Proof.
  exact orn_list_hdlist.
Qed.

Theorem test_orn_index_12:
  forall (A : Type) (l : list A),
    projT1 (orn_list_hdlist A l) = orn_list_hdlist_index A l.
Proof.
  exact orn_list_hdlist_coh.
Qed.

Theorem test_orn_inv_12:
  forall (A : Type) (hl : packed_hd_list A),
    list A.
Proof.
  exact orn_list_hdlist_inv.
Qed.

Theorem test_orn_inv_unpack_12:
  forall (A : Type) (ao : option A) (hl : hd_list A ao),
    list A.
Proof.
  intros. apply orn_list_hdlist_inv. exists ao. apply hl.
Qed.

Theorem test_section_12:
  forall (A : Type) (l : list A),
    orn_list_hdlist_inv A (orn_list_hdlist A l) = l.
Proof.
  exact orn_list_hdlist_section.
Qed.

Theorem test_retraction_12:
  forall (A : Type) (l : packed_hd_list A),
    orn_list_hdlist A (orn_list_hdlist_inv A l) = l.
Proof.
  exact orn_list_hdlist_retraction.
Qed.

Theorem test_adjunction_12:
  forall (A : Type) (l : list A),
    orn_list_hdlist_retraction_adjoint A (orn_list_hdlist A l) =
    f_equal (orn_list_hdlist A) (orn_list_hdlist_section A l).
Proof.
  exact orn_list_hdlist_adjunction.
Qed.

(* --- Indices that depend on prior indices --- *)

Inductive list_alt : Type -> Type :=
| nil_alt : forall A, list_alt A
| cons_alt :
    forall A, A -> list_alt A -> list_alt A.

Inductive hd_list_alt : forall (A : Type), option A -> Type :=
| hd_nil_alt : forall A, hd_list_alt A None
| hd_cons_alt :
    forall A (ao : option A) (a : A),
      hd_list_alt A ao ->
      hd_list_alt A (Some a).

Definition packed_hd_list_alt (T : Type) :=
  sigT (A := option T) (fun (h : option T) => hd_list_alt T h).

Find ornament list_alt hd_list_alt as orn_listalt_hdlistalt.

Definition list_alt_hd (A : Type) (l : list_alt A) :=
  list_alt_rect
    (fun (A : Type) (_ : list_alt A) => option A)
    (fun (A : Type) => None)
    (fun (A : Type) (a : A) (_ : list_alt A) (_ : option A) =>
       Some a)
    A
    l.

Theorem test_index_13:
  forall (A : Type) (l : list_alt A),
    list_alt_hd A l = orn_listalt_hdlistalt_index A l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_13:
  forall (A : Type) (l : list_alt A),
    packed_hd_list_alt A.
Proof.
  exact orn_listalt_hdlistalt.
Qed.

Theorem test_orn_index_13:
  forall (A : Type) (l : list_alt A),
    projT1 (orn_listalt_hdlistalt A l) = orn_listalt_hdlistalt_index A l.
Proof.
  exact orn_listalt_hdlistalt_coh.
Qed.

Theorem test_orn_inv_13:
  forall (A : Type) (l : packed_hd_list_alt A),
    list_alt A.
Proof.
  exact orn_listalt_hdlistalt_inv.
Qed.

Theorem test_orn_inv_unpack_13:
  forall (A : Type) (ao : option A) (l : hd_list_alt A ao),
    list_alt A.
Proof.
  intros. apply orn_listalt_hdlistalt_inv. exists ao. apply l.
Qed.

Theorem test_section_13:
  forall (A : Type) (l : list_alt A),
    orn_listalt_hdlistalt_inv A (orn_listalt_hdlistalt A l) = l.
Proof.
  exact orn_listalt_hdlistalt_section.
Qed.

Theorem test_reraction_13:
  forall (A : Type) (l : packed_hd_list_alt A),
    orn_listalt_hdlistalt A (orn_listalt_hdlistalt_inv A l) = l.
Proof.
  exact orn_listalt_hdlistalt_retraction.
Qed.

Theorem test_adjunction_13:
  forall (A : Type) (l : list_alt A),
    orn_listalt_hdlistalt_retraction_adjoint A (orn_listalt_hdlistalt A l) =
    f_equal (orn_listalt_hdlistalt A) (orn_listalt_hdlistalt_section A l).
Proof.
  exact orn_listalt_hdlistalt_adjunction.
Qed.

(* --- Indexing by the old type, but without making it fin-like --- *)

Inductive nat_nat : nat -> Type :=
| OO : nat_nat 0
| SS : forall (n : nat), nat_nat n -> nat_nat (S n).

Definition packed_nat_nat :=
  sigT (A := nat) (fun (n : nat) => nat_nat n).

Find ornament nat nat_nat as orn_nat_natnat.

Definition nat_size (n : nat) :=
  nat_rect
    (fun (_ : nat) => nat)
    O
    (fun (_ : nat) (IH : nat) =>
      S IH)
    n.

Theorem test_index_14:
  forall (n : nat),
    nat_size n = orn_nat_natnat_index n.
Proof.
  intros. auto.
Qed.

Theorem test_orn_14:
  forall (n : nat),
    packed_nat_nat.
Proof.
  exact orn_nat_natnat.
Qed.

Theorem test_orn_index_14:
  forall (n : nat),
    projT1 (orn_nat_natnat n) = orn_nat_natnat_index n.
Proof.
  exact orn_nat_natnat_coh.
Qed.

Theorem test_orn_inv_14:
  forall (nn : packed_nat_nat),
    nat.
Proof.
  exact orn_nat_natnat_inv.
Qed.

Theorem test_orn_inv_unpack_14:
  forall (n : nat) (nn : nat_nat n),
    nat.
Proof.
  intros. apply orn_nat_natnat_inv. exists n. apply nn.
Qed.

Theorem test_section_14:
  forall (n : nat),
    orn_nat_natnat_inv (orn_nat_natnat n) = n.
Proof.
  exact orn_nat_natnat_section.
Qed.

Theorem test_retraction_14:
  forall (n : packed_nat_nat),
    orn_nat_natnat (orn_nat_natnat_inv n) = n.
Proof.
  exact orn_nat_natnat_retraction.
Qed.

Theorem test_adjunction_14:
  forall (n : nat),
    orn_nat_natnat_retraction_adjoint (orn_nat_natnat n) =
    f_equal orn_nat_natnat (orn_nat_natnat_section n).
Proof.
  exact orn_nat_natnat_adjunction.
Qed.

(* --- Regression of bug in more complicated index identification algorithm --- *)

(*
 * Minimal test case
 *)

Inductive doublevector5 (A : Type) : nat -> nat -> Type :=
| dnilV5 : doublevector5 A 0 0
| dconsV5 :
    forall (m n : nat),
      A -> doublevector5 A n m -> doublevector5 A (S n) (S (S m)).

Definition packed_doublevector5 (A : Type) (n : nat) :=
  sigT (A := nat) (fun m : nat => doublevector5 A n m).

Find ornament vector doublevector5 as orn_vector_doublevector5.

Theorem test_index_15:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector5_index A n v = vector_double_size A n v.
Proof.
  intros. reflexivity.
Qed.

Theorem test_orn_15:
  forall (A : Type) (n : nat) (v : vector A n),
    packed_doublevector5 A n.
Proof.
  exact orn_vector_doublevector5.
Qed.

Theorem test_orn_index_15:
  forall (A : Type) (n : nat) (v : vector A n),
    projT1 (orn_vector_doublevector5 A n v) = orn_vector_doublevector5_index A n v.
Proof.
  exact orn_vector_doublevector5_coh.
Qed.

Theorem test_orn_inv_15:
  forall (A : Type) (n : nat) (d : packed_doublevector5 A n),
    vector A n.
Proof.
  exact orn_vector_doublevector5_inv.
Qed.

Theorem test_orn_inv_unpack_15:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector5 A n m),
    vector A n.
Proof.
  intros. apply orn_vector_doublevector5_inv. exists m. apply d.
Qed.

Theorem test_section_15:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector5_inv A n (orn_vector_doublevector5 A n v) = v.
Proof.
  exact orn_vector_doublevector5_section.
Qed.

Theorem test_retraction_15:
  forall (A : Type) (n : nat) (v : packed_doublevector5 A n),
    orn_vector_doublevector5 A n (orn_vector_doublevector5_inv A n v) = v.
Proof.
  exact orn_vector_doublevector5_retraction.
Qed.

Theorem test_adjunction_15:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector5_retraction_adjoint A n (orn_vector_doublevector5 A n v) =
    f_equal (orn_vector_doublevector5 A n) (orn_vector_doublevector5_section A n v).
Proof.
  exact orn_vector_doublevector5_adjunction.
Qed.

(* --- More regression --- *)

(*
 * From case study, made ambiguous so the more complex algorithm runs,
 * and then simplified
 *)

Inductive _bst : nat -> nat -> Type :=
| _Branch (min_l min_r : nat) (max_l max_r : nat) (val : nat)
          (left : _bst min_l max_l) (right : _bst min_r max_r)
      : _bst min_l max_r
| _Leaf (val : nat) : _bst val val.

Definition inv (ord_l ord_r : nat) (max_l val min_r : nat) : nat :=
  ord_l *
  ord_r *
  (if Nat.ltb max_l val then 1 else 0) *
  (if Nat.ltb val min_r then 1 else 0).

Inductive bst : nat -> nat -> nat -> Type :=
| Branch (ord_l ord_r : nat) (min_l min_r : nat) (max_l max_r : nat)
         (val : nat)
         (left : bst min_l max_l ord_l) (right : bst min_r max_r ord_r)
      : bst min_l max_r (inv ord_l ord_r max_l val min_r)
| Leaf (val : nat) : bst val val 1.

Find ornament _bst bst.

Definition is_bst (n m : nat) (b : _bst n m) : nat :=
  _bst_rect
    (fun _ _ _  => nat)
    (fun (min_l min_r max_l max_r val : nat)
         (left : _bst min_l max_l) (IHl : nat)
         (right : _bst min_r max_r) (IHr : nat) =>
      inv IHl IHr max_l val min_r)
    (fun _ : nat => 1)
    n
    m
    b.

Definition packed_bst (n m : nat) :=
  sigT (A := nat) (fun (p : nat) => bst n m p).

Theorem test_index_16:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst_index n m b = is_bst n m b.
Proof.
  intros. reflexivity.
Qed.

Theorem test_orn_16:
  forall (n m : nat) (b : _bst n m),
    packed_bst n m.
Proof.
  exact _bst_to_bst.
Qed.

Theorem test_orn_index_16:
  forall (n m : nat) (b : _bst n m),
    projT1 (_bst_to_bst n m b) = _bst_to_bst_index n m b.
Proof.
  exact _bst_to_bst_coh.
Qed.

Theorem test_orn_inv_16:
  forall (n m : nat) (b : packed_bst n m),
    _bst n m.
Proof.
  exact _bst_to_bst_inv.
Qed.

Theorem test_orn_inv_unpack_16:
  forall (n m p : nat) (b : bst n m p),
    _bst n m.
Proof.
  intros n m p b. apply _bst_to_bst_inv. exists p. apply b.
Qed.

Theorem test_section_16:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst_inv n m (_bst_to_bst n m b) = b.
Proof.
  exact _bst_to_bst_section.
Qed.

Theorem test_retraction_16:
  forall (n m : nat) (b : packed_bst n m),
    _bst_to_bst n m (_bst_to_bst_inv n m b) = b.
Proof.
  exact _bst_to_bst_retraction.
Qed.

Theorem test_adjunction_16:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst_retraction_adjoint n m (_bst_to_bst n m b) =
    f_equal (_bst_to_bst n m) (_bst_to_bst_section n m b).
Proof.
  exact _bst_to_bst_adjunction.
Qed.

(* --- Make sure moving the hypotheses around works too --- *)

Inductive bst2 : nat -> nat -> nat -> Type :=
| Branch2 (ord_l : nat) (min_l min_r : nat) (max_l max_r : nat)
         (val : nat)
         (left : bst2 min_l max_l ord_l) (ord_r : nat) (right : bst2 min_r max_r ord_r)
      : bst2 min_l max_r (inv ord_l ord_r max_l val min_r)
| Leaf2 (val : nat) : bst2 val val 1.

Find ornament _bst bst2.

Definition packed_bst2 (n m : nat) :=
  sigT (A := nat) (fun (p : nat) => bst2 n m p).

Theorem test_index_17:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst2_index n m b = is_bst n m b.
Proof.
  intros. reflexivity.
Qed.

Theorem test_orn_17:
  forall (n m : nat) (b : _bst n m),
    packed_bst2 n m.
Proof.
  exact _bst_to_bst2.
Qed.

Theorem test_orn_index_17:
  forall (n m : nat) (b : _bst n m),
    projT1 (_bst_to_bst2 n m b) = _bst_to_bst2_index n m b.
Proof.
  exact _bst_to_bst2_coh.
Qed.

Theorem test_orn_inv_17:
  forall (n m : nat) (b : packed_bst2 n m),
    _bst n m.
Proof.
  exact _bst_to_bst2_inv.
Qed.

Theorem test_orn_inv_unpack_17:
  forall (n m p : nat) (b : bst2 n m p),
    _bst n m.
Proof.
  intros n m p b. apply _bst_to_bst2_inv. exists p. apply b.
Qed.

Theorem test_section_17:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst2_inv n m (_bst_to_bst2 n m b) = b.
Proof.
  exact _bst_to_bst2_section.
Qed.

Theorem test_retraction_17:
  forall (n m : nat) (b : packed_bst2 n m),
    _bst_to_bst2 n m (_bst_to_bst2_inv n m b) = b.
Proof.
  exact _bst_to_bst2_retraction.
Qed.

Theorem test_adjunction_17:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst2_retraction_adjoint n m (_bst_to_bst2 n m b) =
    f_equal (_bst_to_bst2 n m) (_bst_to_bst2_section n m b).
Proof.
  exact _bst_to_bst2_adjunction.
Qed.

(* --- Test moving around the index location --- *)

Inductive bst3 : nat -> nat -> nat -> Type :=
| Branch3 (ord_l : nat) (min_l min_r : nat) (max_l max_r : nat)
         (val : nat)
         (left : bst3 min_l ord_l max_l) (ord_r : nat) (right : bst3 min_r ord_r max_r)
      : bst3 min_l (inv ord_l ord_r max_l val min_r) max_r
| Leaf3 (val : nat) : bst3 val 1 val.

Find ornament _bst bst3.

Definition packed_bst3 (n m : nat) :=
  sigT (A := nat) (fun (p : nat) => bst3 n p m).

Theorem test_index_18:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst3_index n m b = is_bst n m b.
Proof.
  intros. reflexivity.
Qed.

Theorem test_orn_18:
  forall (n m : nat) (b : _bst n m),
    packed_bst3 n m.
Proof.
  exact _bst_to_bst3.
Qed.

Theorem test_orn_index_18:
  forall (n m : nat) (b : _bst n m),
    projT1 (_bst_to_bst3 n m b) = _bst_to_bst3_index n m b.
Proof.
  exact _bst_to_bst3_coh.
Qed.

Theorem test_orn_inv_18:
  forall (n m : nat) (b : packed_bst3 n m),
    _bst n m.
Proof.
  exact _bst_to_bst3_inv.
Qed.

Theorem test_orn_inv_unpack_18:
  forall (n m p : nat) (b : bst3 n p m),
    _bst n m.
Proof.
  intros n m p b. apply _bst_to_bst3_inv. exists p. apply b.
Qed.

Theorem test_section_18:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst3_inv n m (_bst_to_bst3 n m b) = b.
Proof.
  exact _bst_to_bst3_section.
Qed.

Theorem test_retraction_18:
  forall (n m : nat) (b : packed_bst3 n m),
    _bst_to_bst3 n m (_bst_to_bst3_inv n m b) = b.
Proof.
  exact _bst_to_bst3_retraction.
Qed.

Theorem test_adjunction_18:
  forall (n m : nat) (b : _bst n m),
    _bst_to_bst3_retraction_adjoint n m (_bst_to_bst3 n m b) =
    f_equal (_bst_to_bst3 n m) (_bst_to_bst3_section n m b).
Proof.
  exact _bst_to_bst3_adjunction.
Qed.

(* --- Binary trees with changed hypothesis order --- *)

Inductive bintreeV2 (A : Type) : nat -> Type :=
| leafV2:
    bintreeV2 A 0
| nodeV2 :
    forall (n : nat),
      bintreeV2 A n ->
      A ->
      forall (m : nat),
        bintreeV2 A m ->
        bintreeV2 A (S (n + m)).

Definition packed_bintreeV2 (T : Type) :=
  sigT (A := nat) (fun (n : nat) => bintreeV2 T n).

Find ornament bintree bintreeV2 as orn_bintree_bintreeV2.

Theorem test_index_19:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV2_index A tr = bintree_size A tr.
Proof.
  intros. reflexivity.
Qed.

Theorem test_orn_19:
  forall (A : Type) (tr : bintree A),
    packed_bintreeV2 A.
Proof.
  exact orn_bintree_bintreeV2.
Qed.

Theorem test_orn_index_19:
  forall (A : Type) (tr : bintree A),
    projT1 (orn_bintree_bintreeV2 A tr) = orn_bintree_bintreeV2_index A tr.
Proof.
  exact orn_bintree_bintreeV2_coh.
Qed.

Theorem test_orn_inv_19:
  forall (A : Type) (tr : packed_bintreeV2 A),
    bintree A.
Proof.
  exact orn_bintree_bintreeV2_inv.
Qed.

Theorem test_orn_inv_unpack_19:
  forall (A : Type) (n : nat) (tr : bintreeV2 A n),
    bintree A.
Proof.
  intros. apply orn_bintree_bintreeV2_inv. exists n. apply tr.
Qed.

Theorem test_section_19:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV2_inv A (orn_bintree_bintreeV2 A tr) = tr.
Proof.
  exact orn_bintree_bintreeV2_section.
Qed.

Theorem test_retraction_19:
  forall (A : Type) (tr : packed_bintreeV2 A),
    orn_bintree_bintreeV2 A (orn_bintree_bintreeV2_inv A tr) = tr.
Proof.
  exact orn_bintree_bintreeV2_retraction.
Qed.

Theorem test_adjunction_19:
  forall (A : Type) (tr : bintree A),
    orn_bintree_bintreeV2_retraction_adjoint A (orn_bintree_bintreeV2 A tr) =
    f_equal (orn_bintree_bintreeV2 A) (orn_bintree_bintreeV2_section A tr).
Proof.
  exact orn_bintree_bintreeV2_adjunction.
Qed.

(* (* --- TODO Index already existed in the old constructor, but wasn't used --- *) *)

(* (* --- TODO Index already existed in the old constructor, but was used differently --- *) *)

(* (* --- TODO weirder indexes --- *) *)

(* (* --- TODO examples from notebook etc --- *) *)
