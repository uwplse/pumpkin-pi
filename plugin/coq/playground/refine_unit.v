(*
 * This proof shows that, given some type A, you can always prove an equivalence
 * with unit refined by A. Thus, by transitivity of equivalences (not proven here),
 * if A is equivalent to B, then so is unit refined by A.
 *
 * In the context of the paper, this gives an example of a construction that allows for
 * the formation of infinitely many (just keep adding unit) useless (subjectively, in 
 * the authors' opinions) equivalences corresponding to a change from A to B. This again
 * makes the point that choosing a useful equivalence is important and is a bit of an art.
 *)

Definition uA (A : Type) := sigT (fun u : unit => A).

Definition f (A : Type) (a : A) : uA A :=
  existT _ tt a.

Definition g (A : Type) (ua : uA A) : A :=
  projT2 ua.

Lemma section: forall A a, g A (f A a) = a.
Proof.
  intros. reflexivity.
Defined.

Lemma retraction: forall A u, f A (g A u) = u.
Proof.
  intros. induction u. induction x. reflexivity.
Defined.
