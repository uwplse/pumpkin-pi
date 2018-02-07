Require Import List.
Require Import Ornamental.Ornaments.

Inductive vector (A : Type) : nat -> Type :=
| nilV : vector A 0
| consV : forall (n : nat), A -> vector A n -> vector A (S n).

Find ornament list vector as orn_list_vector.

Print orn_list_vector_index.
