DECLARE PLUGIN "ornamental"

open Stdarg
open Frontend
open Ltac_plugin
open Tacinterp
open Tacarg

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

(* Register the Ltac script for sigma unpacking *)
VERNAC COMMAND EXTEND UnpackSigma CLASSIFIED AS SIDEFF
| [ "Unpack" reference(const_ref) "as" ident(id) ] ->
  [ do_unpack_constant id const_ref ]
(* | [ "Unpack" "Module" reference(mod_ref) "as" ident(id) ] ->
 *   [ do_unpack_module id mod_ref ] *)
END

(* Lift from records to products *)
VERNAC COMMAND EXTEND RecordToProduct CLASSIFIED AS SIDEFF
| [ "Lift" "Record" constr(def_o) constr(def_n) "in" constr(def) "as" ident(n) ] ->
  [ do_lift_record_to_product n def_o def_n def ]
END
