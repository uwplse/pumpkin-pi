DECLARE PLUGIN "ornamental"

open Stdarg
open Frontend

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

(* Desugar any/all fix/match subterms into eliminator applications *)
VERNAC COMMAND EXTEND TranslateMatch CLASSIFIED AS SIDEFF
(* TODO: Use reference for the source constant *)
| [ "Desugar" reference(const_ref) "as" ident(id)] ->
  [ do_desugar_constant id const_ref ]
| [ "Desugar" "Module" reference(mod_ref) "as" ident(id)] ->
  [ do_desugar_module id mod_ref ]
END
