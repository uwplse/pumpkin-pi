DECLARE PLUGIN "ornamental"

open Util
open Names
open Stdarg
open Frontend
open Utilities
open Coqterms
open Lifting

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n) ] ->
  [ find_ornament n d_old d_new ]
END

(* Lift a function along an ornament *)
VERNAC COMMAND EXTEND LiftOrnament CLASSIFIED AS SIDEFF
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ make_ornamental_command lift_by_ornament true n d_old d_orn d_orn_inv;
    Printf.printf "Defined lifted function %s.\n\n" (Id.to_string n) ]
END
