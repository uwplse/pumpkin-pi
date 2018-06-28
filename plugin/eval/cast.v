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

(* A synonym for eq_rect with implicit inference of more arguments. *)
Definition cast {A : Type} {P : A -> Type} {x y : A} (p : P x) (E : x = y) : P y :=
  @eq_rect A x P p y E.

Definition cast_trivial {A : decType} {P : A -> Type} {x : A}
           (p : P x) (E : x = x) : @cast A P x x p E = p :=
  eq_sym (@Eqdep_dec.eq_rect_eq_dec A eq_dec x P p E).

Program Canonical Structure nat_decType :=
  Decidable.Pack nat _.
Next Obligation. decide equality. Defined.

Lemma cast_struct {A : decType} {B : A -> Type} {x y : A}
      {g : A -> A} {inj : forall x y, g x = g y -> x = y}
      (E : g x = g y) (f : forall x, B x -> B (g x))
      (p : B x) : cast (f x p) E = f y (cast p (inj x y E)).
Proof.
  assert (E' := (inj x y E)). revert p E. rewrite E'. intros p E.
  repeat rewrite cast_trivial. reflexivity.
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

(* Notation "p :> P y" := (@cast _ P _ y (equate _) p) (left associativity, at level 90, P at level 1, y at level 1). *)

(* Let's make [n + 0 = n] and [n + S m = S (n + m)] canonical identities. *)
Canonical Structure plus_n_O_idType (n : nat) :=
  Identity.Pack nat (n + 0) n (eq_sym (plus_n_O n)).
Canonical Structure plus_n_Sm_idType (n m : nat) :=
  Identity.Pack nat (n + S m) (S (n + m)) (eq_sym (plus_n_Sm n m)).
Canonical Structure add_comm (n m : nat) :=
  Identity.Pack nat (n + m) (m + n) (add_comm n m).
(* FIXME: Inference of canonical instances is too shallow; we really need first-order unification. *)

Module Vector.

Inductive vector (A : Type) : nat -> Type :=
| vcons (n : nat) (x : A) : vector A n -> vector A (S n)
| vnil : vector A O.
Arguments vcons {A n}.
Arguments vnil {A}.

Fixpoint vapp {A n m} (xs : vector A n) (ys : vector A m) : vector A (n + m) :=
  match xs with
  | vcons x xs => vcons x (vapp xs ys)
  | vnil => ys
  end.

Lemma cast_vcons {A n m} (x : A) (xs : vector A n) (E : S n = S m) :
    cast (vcons x xs) E = vcons x (cast xs (eq_add_S n m E)).
Proof.
  apply (cast_struct E (fun n => @vcons A n x) xs).
Defined.

Definition bitvector := vector bool.
Definition bv1010 : bitvector 4 :=
  (vcons true (vcons false (vcons true (vcons false vnil)))).

Check (cast bv1010 (plus_n_O 4)).

Lemma vapp_vnil_r {A n} (xs : vector A n) :
  <| vapp xs vnil |> = xs.
Proof.
  simpl. generalize (eq_sym (plus_n_O n)) as E.
  induction xs; simpl; intros E.
  - rewrite cast_vcons, IHxs. reflexivity.
  - rewrite cast_trivial. reflexivity.
Qed.

End Vector.
