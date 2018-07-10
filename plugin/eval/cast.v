Require Import Program.Equality Logic.Eqdep_dec.
Require Import Peano.
Require Import lemmas.

Module Decidable.
Structure t :=
  Pack {
    type : Type;
    eq_dec : forall (x y : type), {x = y} + {x <> y};
  }.
End Decidable.

Notation decType := Decidable.t.
Notation eq_dec := (Decidable.eq_dec _).
Coercion Decidable.type : decType >-> Sortclass.

Notation UIP A := (@Eqdep_dec.UIP_dec A eq_dec _ _ _ eq_refl).

Notation cast p E := (@eq_rect _ _ _ p _ E).

Definition cast_trivial {A : decType} {P : A -> Type} {x : A}
           (p : P x) (E : x = x) : cast p E = p.
  rewrite (UIP A). reflexivity.
Defined.

Program Canonical Structure nat_decType :=
  Decidable.Pack nat _.
Next Obligation. decide equality. Defined.

Lemma cast_sigma {A : Type} {B : A -> Type} {C : Type} {x y : A}
      (f : forall x, B x -> C) (E : x = y)
      (p : B x) : f y (cast p E) = f x p.
Proof.
  revert p. rewrite <- E. intro p. reflexivity.
Defined.

Lemma cast_functor {A : decType} {B C : A -> Type} {g : A -> A} {x y : A}
      (f : forall x, B x -> C (g x)) (E : x = y) (E' : g x = g y)
      (p : B x) : cast (f x p) E' = f y (cast p E).
Proof.
  revert p E'. rewrite <- E. intros p E'. rewrite cast_trivial. reflexivity.
Defined.

Lemma cast_contract {A : decType} {B : A -> Type}
      {f : forall x, B x} {x y : A} (E : x = y) : cast (f x) E = f y.
Proof.
  assert (E' := E). revert E. rewrite E'. intros E. rewrite cast_trivial. reflexivity.
Defined.

Module Identity.
Structure t {A : Type} :=
  Pack {
    source : A;
    target : A;
    equate : source = target;
  }.
End Identity.

Notation idType := Identity.t.
Notation source := Identity.source.
Notation target := Identity.target.
Notation equate := Identity.equate.

Notation "<| x |>" := (cast x (equate _)).

(* Let's make [n + 0 = n] and [n + S m = S (n + m)] canonical identities. *)
Canonical Structure plus_n_O_idType (n : nat) :=
  Identity.Pack nat (n + 0) n (eq_sym (plus_n_O n)).
Canonical Structure plus_n_Sm_idType (n m : nat) :=
  Identity.Pack nat (n + S m) (S (n + m)) (eq_sym (plus_n_Sm n m)).
Canonical Structure plusC_idType (n m : nat) :=
  Identity.Pack nat (n + m) (m + n) (add_comm n m).
(* NOTE: Inference of canonical instances is too shallow; we really need first-order unification. *)
