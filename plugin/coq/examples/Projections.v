(*
 * The troubles of non-primitive projections.
 *)
Require Import Example.

(*
 * This doesn't work:
 *)
Theorem convert:
  forall (T : Type) (v : sigT (vector T)),
    v = existT _ (projT1 v) (projT2 v).
Proof.
  Fail reflexivity.
Abort.

(*
 * So in general, if you want to preserve definitional equalities,
 * you need to expand every v to existT _ (projT1 v) (projT2 v).
 *)

(*
 * We can optimize some terms, though, and avoid packing in some cases, since:
 *)
Theorem convert:
  forall (T : Type) (n : nat) (v : vector T n),
    existT _ v n = existT _ (projT1 (existT _ v n)) (projT2 (existT _ v n)).
Proof.
  reflexivity.
Qed.
