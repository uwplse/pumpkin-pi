(*
 * This file contains test infrastructure.
 *)

(*
 * Test exact equality of goals (rather than
 * definitional equality). That way, we can test
 * that a specific term is produced that is syntactically
 * friendly to the user, for example using certain
 * constants.
 *)
Ltac test_exact_equality :=
  match goal with
  | |- ?x = ?x => reflexivity
  | _ => idtac
  end.