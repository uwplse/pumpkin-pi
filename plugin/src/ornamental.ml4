DECLARE PLUGIN "ornamental"

open Stdarg
open Frontend
open Tacinterp
open Tacarg
open Ltac_plugin

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n) ] ->
  [ find_ornament (Some n) d_old d_new ]
| [ "Find" "ornament" constr(d_old) constr(d_new) ] ->
  [ find_ornament None d_old d_new ]
END

(* Lift a function along an ornament *)
VERNAC COMMAND EXTEND LiftOrnament CLASSIFIED AS SIDEFF
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ lift_by_ornament n d_orn d_orn_inv d_old ]
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n)] ->
  [ lift_by_ornament ~suffix:true n d_orn d_orn_inv d_old ]
END

(* Tactic version of lifting *)
TACTIC EXTEND algebraic_ornament
| [ "algebraic_ornament" constr(d_orn) constr(d_orn_inv) ] ->
  [ lift_by_ornament_tactic d_orn d_orn_inv ]
END  

(* Register the Ltac script for sigma unpacking *)
VERNAC COMMAND EXTEND UnpackSigma CLASSIFIED AS SIDEFF
| [ "Unpack" reference(const_ref) "as" ident(id) ] ->
  [ do_unpack_constant id const_ref ]
(* | [ "Unpack" "Module" reference(mod_ref) "as" ident(id) ] ->
 *   [ do_unpack_module id mod_ref ] *)
END
