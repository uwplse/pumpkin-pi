Require Import List.
Require Import Ornamental.Ornaments.

(*--- Lists and Vectors ---*)

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

Definition packed_vector (T : Type) :=
  sigT (A := nat) (fun (n : nat) => vector T n).

Find ornament list vector as orn_list_vector.

Theorem test_index:
  forall (A : Type) (l : list A),
    orn_list_vector_index A l = length l.
Proof.
  intros. auto.
Qed.

Theorem test_orn:
  forall (A : Type) (l : list A),
    vector A (length l).
Proof.
  exact orn_list_vector.
Qed.

Theorem test_orn_inv:
  forall (A : Type) (n : nat) (v : vector A n),
    list A.
Proof.
  exact orn_list_vector_inv.
Qed.

(* --- Backwards lists --- *)

Inductive rev_list (A : Type) : Type :=
| rev_nil : rev_list A
| rev_cons : rev_list A -> A -> rev_list A.

Inductive rev_vector (A : Type) : nat -> Type :=
| rev_nilV : rev_vector A 0
| rev_consV : forall (n : nat), rev_vector A n -> A -> rev_vector A (S n).

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
    rev_vector A (rev_list_length A l).
Proof.
  exact orn_rev_list_rev_vector.
Qed.

Theorem rest_orn_inv_2:
  forall (A : Type) (n : nat) (v : rev_vector A n),
    rev_list A.
Proof.
  exact orn_rev_list_rev_vector_inv.
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

Find ornament bintree bintreeV as orn_bintree_bintreeV.

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
    bintreeV A (bintree_size A tr).
Proof.
  exact orn_bintree_bintreeV.
Qed.

Theorem test_orn_inv_3:
  forall (A : Type) (n : nat) (tr : bintreeV A n),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_inv.
Qed.

(* --- Lists of values of two types (making sure parameter logic works) --- *)

Inductive list2 (A : Type) (B : Type) : Type :=
| nil2 : list2 A B
| cons2 : A -> B -> list2 A B -> list2 A B.

Inductive vector2 (A : Type) (B : Type) : nat -> Type :=
| nilV2 : vector2 A B 0
| consV2 : forall (n : nat), A -> B -> vector2 A B n -> vector2 A B (S (S n)).

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
    vector2 A B (orn_list2_vector2_index A B l).
Proof.
  exact orn_list2_vector2.
Qed.

Theorem test_orn_inv_4:
  forall (A : Type) (B : Type) (n : nat) (l : vector2 A B n),
    list2 A B.
Proof.
  exact orn_list2_vector2_inv.
Qed.

(* --- Adding a nat index to a nat list --- *)

Inductive nat_list : Type :=
| nat_nil : nat_list
| nat_cons : nat -> nat_list -> nat_list.

Inductive nat_vector : nat -> Type :=
| nat_nilV : nat_vector 0
| nat_consV : forall (n : nat), nat -> nat_vector n -> nat_vector (S n).

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
    nat_vector (nat_length l).
Proof.
  exact orn_natlist_natvector.
Qed.

Theorem test_orn_inv_5:
  forall (n : nat) (v : nat_vector n),
    nat_list.
Proof.
  exact orn_natlist_natvector_inv.
Qed.

(* --- BintreeV with nats in reverse order --- *)

Inductive bintreeV_rev (A : Type) : nat -> Type :=
| leafV_rev :
    bintreeV_rev A 0
| nodeV_rev :
    forall (n m : nat),
      bintreeV_rev A m -> A -> bintreeV_rev A n -> bintreeV_rev A (n + m).

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
    bintreeV_rev A (bintree_size_rev A tr).
Proof.
  exact orn_bintree_bintreeV_rev.
Qed.

Theorem test_orn_inv_6:
  forall (A : Type) (n : nat) (tr : bintreeV_rev A n),
    bintree A.
Proof.
  exact orn_bintree_bintreeV_rev_inv.
Qed.

(* --- Adding an index whose type that matches an already existing index --- *)

Inductive doublevector (A : Type) : nat -> nat -> Type :=
| dnilV : doublevector A 0 0
| dconsV :
    forall (n m : nat),
      A -> doublevector A n m -> doublevector A (S (S n)) (S m).

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
    doublevector A (vector_double_size A n v) n.
Proof.
  exact orn_vector_doublevector.
Qed.

Theorem test_orn_inv_7:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector A n m),
    vector A m.
Proof.
  exact orn_vector_doublevector_inv.
Qed.

(* --- Same as above, but switch the position we change --- *)

Inductive doublevector2 (A : Type) : nat -> nat -> Type :=
| dnilV2 : doublevector2 A 0 0
| dconsV2 :
    forall (n m : nat),
      A -> doublevector2 A n m -> doublevector2 A (S n) (S (S m)).

Find ornament vector doublevector2 as orn_vector_doublevector2.

Theorem test_index_8:
  forall (A : Type) (n : nat) (v : vector A n),
    orn_vector_doublevector2_index A n v = vector_double_size A n v.
Proof.
  intros. auto.
Qed.

Theorem test_orn_8:
  forall (A : Type) (n : nat) (v : vector A n),
    doublevector2 A n (vector_double_size A n v).
Proof.
  exact orn_vector_doublevector2.
Qed.

Theorem test_orn_inv_8:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector2 A n m),
    vector A n.
Proof.
  exact orn_vector_doublevector2_inv.
Qed.

(* --- Same as above, but with an identical index --- *)

Inductive doublevector3 (A : Type) : nat -> nat -> Type :=
| dnilV3 : doublevector3 A 0 0
| dconsV3 :
    forall (n m : nat),
      A -> doublevector3 A n m -> doublevector3 A (S n) (S m).

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
    doublevector3 A n (vector_size A n v).
Proof.
  exact orn_vector_doublevector3.
Qed.

Theorem test_orn_inv_9:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector3 A n m),
    vector A n.
Proof.
  exact orn_vector_doublevector3_inv.
Qed.

(* --- What if we change a base case index? --- *)

Inductive doublevector4 (A : Type) : nat -> nat -> Type :=
| dnilV4 : doublevector4 A 1 0
| dconsV4 :
    forall (n m : nat),
      A -> doublevector4 A n m -> doublevector4 A (S n) (S m).

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
    doublevector4 A (S_vector_size A n v) n.
Proof.
  exact orn_vector_doublevector4.
Qed.

Theorem test_orn_inv_10:
  forall (A : Type) (n : nat) (m : nat) (d : doublevector4 A n m),
    vector A m.
Proof.
  exact orn_vector_doublevector4_inv.
Qed.

(* --- Indices that are computed from existing hypotheses --- *)

Inductive hd_nat_list : nat -> Type :=
| hd_nat_nil : hd_nat_list 0
| hd_nat_cons :
    forall (m : nat) (n : nat),
      hd_nat_list m ->
      hd_nat_list n.

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
    hd_nat_list (nat_list_hd nl).
Proof.
  exact orn_natlist_hdnatlist.
Qed.

Theorem test_orn_inv_11:
  forall (h : nat) (hnl : hd_nat_list h),
    nat_list.
Proof.
  exact orn_natlist_hdnatlist_inv.
Qed.

(* --- Indices that depend on parameters --- *)

Inductive hd_list (A : Type) : option A -> Type :=
| hd_nil : hd_list A None
| hd_cons :
    forall (ao : option A) (a : A),
      hd_list A ao ->
      hd_list A (Some a).

Find ornament list hd_list as orn_list_hdlist.

Theorem test_orn_index_12:
  forall (A : Type) (l : list A),
    hd_error l = orn_list_hdlist_index A l.
Proof.
  intros. induction l; auto. (* not reducable because only one is a fix *)
Qed.

Theorem test_orn_12:
  forall (A : Type) (l : list A),
    hd_list A (orn_list_hdlist_index A l).
Proof.
  exact orn_list_hdlist.
Qed.

Theorem test_orn_inv_12:
  forall (A : Type) (ao : option A) (hl : hd_list A ao),
    list A.
Proof.
  exact orn_list_hdlist_inv.
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

Find ornament list_alt hd_list_alt as orn_listalt_hdlistalt.

Definition list_alt_hd (A : Type) (l : list_alt A) :=
  list_alt_rect
    (fun (A : Type) (_ : list_alt A) => option A)
    (fun (A : Type) => None) 
    (fun (A : Type) (a : A) (_ : list_alt A) (_ : option A) =>
       Some a)
    A
    l.

Theorem test_orn_index_13:
  forall (A : Type) (l : list_alt A),
    list_alt_hd A l = orn_listalt_hdlistalt_index A l.
Proof.
  intros. auto.
Qed.

Theorem test_orn_13:
  forall (A : Type) (l : list_alt A),
    hd_list_alt A (list_alt_hd A l).
Proof.
  exact orn_listalt_hdlistalt.
Qed.

Theorem test_orn_inv_13:
  forall (A : Type) (ao : option A) (l : hd_list_alt A ao),
    list_alt A.
Proof.
  exact orn_listalt_hdlistalt_inv.
Qed.

(* --- Indexing by the old type, but without making it fin-like --- *)

Inductive nat_nat : nat -> Type :=
| OO : nat_nat 0
| SS : forall (n : nat), nat_nat n -> nat_nat (S n).

Find ornament nat nat_nat as orn_nat_natnat.

Definition nat_size (n : nat) :=
  nat_rect
    (fun (_ : nat) => nat)
    O
    (fun (_ : nat) (IH : nat) =>
      S IH)
    n.

Theorem test_orn_index_14:
  forall (n : nat),
    nat_size n = orn_nat_natnat_index n.
Proof.
  intros. auto.
Qed.

Theorem test_orn_14:
  forall (n : nat),
    nat_nat (nat_size n).
Proof.
  exact orn_nat_natnat.
Qed.

Theorem test_orn_inv_14:
  forall (n : nat) (nn : nat_nat n),
    nat.
Proof.
  exact orn_nat_natnat_inv.
Qed.

(* --- TODO Index already existed in the old constructor, but wasn't used --- *)

(* --- TODO Index already existed in the old constructor, but was used differently --- *)

(* --- TODO weirder indexes --- *)

(* --- TODO examples from notebook etc --- *)

(* --- TODO write a test script --- *)

