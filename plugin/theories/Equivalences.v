(*
 * This file contains useful generic equivalences that can be instantiated.
 *)

(*
 * Useful equivalence for algebraic ornaments in packed form, like
 * { s : sigT (vector T) & projT1 s = n }. See coq/examples/Example.v for use
 * of this eliminator.
 *)
Lemma unpack_generic (I_B : Type) (B : I_B -> Type):
  forall (i_b : I_B), { s : sigT B & projT1 s = i_b } -> B i_b.
Proof.
  intros i_b ss. apply (@eq_rect _ (projT1 (projT1 ss)) _  (projT2 (projT1 ss)) i_b (projT2 ss)).
Defined.

Lemma unpack_generic_inv (I_B : Type) (B : I_B -> Type):
  forall (i_b : I_B), B i_b -> { s : sigT B & projT1 s = i_b }.
Proof.
  intros i_b b. exists (existT _ i_b b). reflexivity.
Defined.

Lemma unpack_generic_section (I_B : Type) (B : I_B -> Type):
  forall i_b s, unpack_generic_inv I_B B i_b (unpack_generic I_B B i_b s) = s.
Proof.
  intros. unfold unpack_generic, unpack_generic_inv.
  induction s. induction x. simpl in *. rewrite <- p.
  reflexivity.
Defined.

Lemma unpack_generic_retraction (I_B : Type) (B : I_B -> Type):
  forall i_b b, unpack_generic I_B B i_b (unpack_generic_inv I_B B i_b b) = b.
Proof.
  intros. reflexivity.
Defined.
