Notation cast p E := (@eq_rect _ _ _ p _ E).

Lemma cast_sigma {A : Type} {B : A -> Type} {C : Type} {x y : A}
      (f : forall x, B x -> C) (E : x = y)
      (p : B x) : f y (cast p E) = f x p.
Proof.
  revert p. rewrite <- E. intro p. reflexivity.
Defined.
