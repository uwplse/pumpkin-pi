(*
 * This file contains useful custom eliminators for ornaments.
 *)

(*
 * Useful eliminator for algebraic ornaments in packed form, like
 * { l : list T & length l = n }. See coq/examples/Example.v for use
 * of this eliminator. Note that lifting assumes pa in the conclusion
 * is eta-expanded to (existT _ (projT1 pa) (projT2 pa)) for now.
 *)
Lemma packed_rect (A : Type) {I_B : Type} (indexer : A -> I_B) (exp : A -> A) (coh : forall i_b a, indexer a = i_b -> indexer (exp a) = i_b):
 forall (i_b : I_B) (P : { a : A & indexer a = i_b } -> Type),
  (forall (a : A) (H : indexer (exp a) = i_b), P (existT _ (exp a) H)) ->
  forall (pa : { a : A & indexer a = i_b }), P (existT (fun a => indexer a = i_b) (exp (projT1 pa)) (coh i_b (projT1 pa) (projT2 pa))).
Proof.
  intros i_b P pf pa. apply (pf (projT1 pa) (coh i_b (projT1 pa) (projT2 pa))).
Defined.
