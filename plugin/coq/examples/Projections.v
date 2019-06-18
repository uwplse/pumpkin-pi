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
Admitted.

(*
 * So in general, if you want to preserve definitional equalities,
 * you need to expand every v to existT _ (projT1 v) (projT2 v).
 *)