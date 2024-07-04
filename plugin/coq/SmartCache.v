Require Import Ornamental.Ornaments.
Require Import List.
Require Import Foo.minimal_records.
Require Import Coq.Bool.Bool.

Set DEVOID search prove equivalence. (* <-- Correctness proofs for search *)
Set DEVOID lift type. (* <-- Prettier types than the ones Coq infers *)
Set Nonrecursive Elimination Schemes. (* <--- Preprocess needs induction principles for records *)
Set DEVOID smart cache.

Module leb.

Lemma leb_implb : forall b1 b2, Bool.le b1 b2 -> implb b1 b2 = true.
Proof.
  apply Bool.le_implb.
Qed.

End leb.

Preprocess Module leb as leb' { opaque Bool.le_implb }.
Definition leb_implb := leb'.leb_implb.

Definition f (b1 b2 b3 b4 : bool) (H : Bool.le true false) (H0 : leb_implb true false H = leb_implb true false H) := ifb (eqb (negb (andb b1 (orb b2 (xorb b3 b4)))) true) false b4.
Definition g (b1 b2 b3 b4 : bool) (H : Bool.le true false) (H0 : leb_implb true false H = leb_implb true false H)  := ifb (eqb (negb (orb b1 (andb b2 (xorb b3 b4)))) true) false b4.
Definition h (b1 b2 b3 b4 : bool) (H : Bool.le true false) (H0 : leb_implb true false H = leb_implb true false H)  := ifb (eqb (negb (orb (andb b1 b2) (xorb b3 b4))) true) false b4.
Definition i (b1 b2 b3 b4 : bool) (H : Bool.le true false) (H0 : leb_implb true false H = leb_implb true false H)  := ifb (eqb (negb (andb (orb b1 b2) (xorb b3 b4))) true) false b4.

Time Lift Generated'.output Handwritten'.output in f as f'.
Time Lift Generated'.output Handwritten'.output in g as g'.
Time Lift Generated'.output Handwritten'.output in h as h'.
Time Lift Generated'.output Handwritten'.output in i as i'.

Lemma test_f :
  f = f'.
Proof.
  reflexivity.
Qed.

Lemma test_g :
  g = g'.
Proof.
  reflexivity.
Qed.

Lemma test_h :
  h = h'.
Proof.
  reflexivity.
Qed.

Lemma test_i :
  i = i'.
Proof.
  reflexivity.
Qed.
