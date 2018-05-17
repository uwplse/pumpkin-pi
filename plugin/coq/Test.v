Require Import List.
Require Import Ornamental.Ornaments.

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
  intros. reflexivity.
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

(*
 * TODO can't yet do inside of module b.c. of bug;
 * ask in France!
Find ornament flist flector as orn_flist_flector.
*)

(* For testing *)
Definition countEven (l : flist) :=
  flist_rect
    (fun (_ : flist) => nat)
    0
    (fun (a : A) (l : flist) (IH : nat) =>
      SIfEven a IH)
    l.

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

Find ornament natFlector.flist natFlector.flector as orn_flist_flector_nat.

Theorem test_index_flector:
  forall (l : natFlector.flist),
    orn_flist_flector_nat_index l = natFlector.countEven l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_flector:
  forall (l : natFlector.flist),
    sigT natFlector.flector.
Proof.
  exact orn_flist_flector_nat.
Qed.

Theorem test_orn_index_flector:
  forall (l : natFlector.flist),
    projT1 (orn_flist_flector_nat l) = orn_flist_flector_nat_index l.
Proof.
  intros. reflexivity.
Qed.

Theorem test_orn_inv_flector:
  forall (v : sigT natFlector.flector),
    natFlector.flist.
Proof.
  exact orn_flist_flector_nat_inv.
Qed.

Theorem test_orn_inv_unpack_flector:
  forall (n : nat) (v : natFlector.flector n),
    natFlector.flist.
Proof.
  intros. apply orn_flist_flector_nat_inv. exists n. apply v.
Qed.

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
  intros. reflexivity.
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
      bintreeV A n -> A -> bintreeV A m -> bintreeV A (n + m).

Definition packed_bintreeV (T : Type) :=
  sigT (A := nat) (fun (n : nat) => bintreeV T n).

Find ornament bintree bintreeV as orn_bintree_bintreeV.

Print orn_bintree_bintreeV.

Definition bintree_size (A : Type) (tr : bintree A) :=
  bintree_rect
    A
    (fun (_ : bintree A) => nat)
    0
    (fun (l : bintree A) (nl : nat) (a : A) (r : bintree A) (nr : nat) =>
      nl + nr)
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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
  intros. reflexivity.
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


(* --- TODO Index already existed in the old constructor, but wasn't used --- *)

(* --- TODO Index already existed in the old constructor, but was used differently --- *)

(* --- TODO weirder indexes --- *)

(* --- TODO examples from notebook etc --- *)

(* --- TODO write a test script --- *)

