DECLARE PLUGIN "ornamental"

open Stdarg
open Frontend

(* Identify an ornament given two types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n) ] ->
  [ find_ornament (Some n) d_old d_new None ]
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n) "{" "mapping" int(i) "}" ] ->
  [ find_ornament (Some n) d_old d_new (Some i) ]
| [ "Find" "ornament" constr(d_old) constr(d_new) ] ->
  [ find_ornament None d_old d_new None ]
| [ "Find" "ornament" constr(d_old) constr(d_new) "{" "mapping" int(i) "}" ] ->
  [ find_ornament None d_old d_new (Some i) ]
END

(* Save a user-supplied equivalence between two types *)
VERNAC COMMAND EXTEND SaveOrnament CLASSIFIED AS SIDEFF
| [ "Save" "ornament" constr(d_old) constr(d_new) "{" "promote" "=" constr(d_orn) ";" "forget" "=" constr(d_orn_inv) "}" ] ->
  [ save_ornament d_old d_new (Some d_orn) (Some d_orn_inv) false None ]
| [ "Save" "ornament" constr(d_old) constr(d_new) "{" "promote" "=" constr(d_orn) "}" ] ->
  [ save_ornament d_old d_new (Some d_orn) None false None ]
| [ "Save" "ornament" constr(d_old) constr(d_new) "{" "forget" "=" constr(d_orn_inv) "}" ] ->
  [ save_ornament d_old d_new None (Some d_orn_inv) false None ]
| [ "Save" "equivalence" constr(d_old) constr(d_new) "{" "promote" "=" constr(d_orn) ";" "forget" "=" constr(d_orn_inv) "}" ] ->
  [ save_ornament d_old d_new (Some d_orn) (Some d_orn_inv) true None ]
| [ "Save" "setoid" constr(d_old) constr(d_new) "{" "promote" "=" constr(d_orn) ";" "forget" "=" constr(d_orn_inv) ";" "types" "=" constr_list(types) ";" "rels" "=" constr_list(eq_rels) ";" "equiv_proofs" "=" constr_list(eq_proofs) "}" ] ->
  [ save_ornament d_old d_new (Some d_orn) (Some d_orn_inv) true (Some (types, eq_rels, eq_proofs)) ]
END

(* Lift a function along an equivalence *)
VERNAC COMMAND EXTEND LiftOrnament CLASSIFIED AS SIDEFF
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ lift_by_ornament n d_orn d_orn_inv d_old false ]
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ lift_by_ornament ~opaques:opaques n d_orn d_orn_inv d_old false ]
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n)] ->
  [ lift_by_ornament ~suffix:true n d_orn d_orn_inv d_old false ]
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ lift_by_ornament ~opaques:opaques ~suffix:true n d_orn d_orn_inv d_old false ]
| [ "Lift" "Module" constr(d_orn) constr(d_orn_inv) "in" reference(mod_ref) "as" ident(id) ] ->
  [ lift_module_by_ornament id d_orn d_orn_inv mod_ref ]
| [ "Lift" "Module" constr(d_orn) constr(d_orn_inv) "in" reference(mod_ref) "as" ident(id) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ lift_module_by_ornament ~opaques:opaques id d_orn d_orn_inv mod_ref ]
END

(* Configure lifting with some additional information *)
VERNAC COMMAND EXTEND ConfigureLift CLASSIFIED AS SIDEFF
| [ "Configure" "Lift" constr(d_orn) constr(d_orn_inv) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ add_lifting_opaques d_orn d_orn_inv opaques ]
| [ "Configure" "Lift" constr(d_orn) constr(d_orn_inv) "{" "~" "opaque" ne_reference_list(opaques) "}"] ->
  [ remove_lifting_opaques d_orn d_orn_inv opaques ]
| [ "Configure" "Lift" constr(d_orn) constr(d_orn_inv) "{" "constrs_a" "=" reference_list(constrs_a) ";" "constrs_b" "=" reference_list(constrs_b) ";" "elim_a" "=" reference(elim_a) ";" "elim_b" "=" reference(elim_b) ";" "eta_a" "=" reference(eta_a) ";" "eta_b" "=" reference(eta_b) ";" "iota_a" "=" reference_list(iota_a) ";" "iota_b" "=" reference_list(iota_b) "}" ] ->
  [ configure_manual d_orn d_orn_inv (constrs_a, constrs_b) (elim_a, elim_b) (eta_a, eta_b) (iota_a, iota_b) ]
END

(* Repair: lift (transform) and then decompile *)
VERNAC COMMAND EXTEND RepairProof CLASSIFIED AS SIDEFF
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ repair n d_orn d_orn_inv d_old false ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ repair ~opaques:opaques n d_orn d_orn_inv d_old false ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n)] ->
  [ repair ~suffix:true n d_orn d_orn_inv d_old false ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ repair ~opaques:opaques ~suffix:true n d_orn d_orn_inv d_old false ]
| [ "Repair" "Module" constr(d_orn) constr(d_orn_inv) "in" reference(mod_ref) "as" ident(id) ] ->
  [ repair_module id d_orn d_orn_inv mod_ref ]
| [ "Repair" "Module" constr(d_orn) constr(d_orn_inv) "in" reference(mod_ref) "as" ident(id) "{" "opaque" ne_reference_list(opaques) "}" ] ->
  [ repair_module ~opaques:opaques id d_orn d_orn_inv mod_ref ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n) "{" "hint" ne_string_list(hints) "}" ] ->
  [ repair ~hints:hints n d_orn d_orn_inv d_old false ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n) "{" "opaque" ne_reference_list(opaques) ";" "hint" ne_string_list(hints) "}" ] ->
  [ repair ~opaques:opaques ~hints:hints n d_orn d_orn_inv d_old false ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n) "{" "hint" ne_string_list(hints) "}" ] ->
  [ repair ~suffix:true ~hints:hints n d_orn d_orn_inv d_old false ]
| [ "Repair" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ".." ident(n) "{" "opaque" ne_reference_list(opaques) ";" "hint" ne_string_list(hints) "}" ] ->
  [ repair ~opaques:opaques ~suffix:true ~hints:hints n d_orn d_orn_inv d_old false ]
| [ "Repair" "Module" constr(d_orn) constr(d_orn_inv) "in" reference(mod_ref) "as" ident(id) "{" "hint" ne_string_list(hints) "}" ] ->
  [ repair_module ~hints:hints id d_orn d_orn_inv mod_ref ]
| [ "Repair" "Module" constr(d_orn) constr(d_orn_inv) "in" reference(mod_ref) "as" ident(id) "{" "opaque" ne_reference_list(opaques) ";" "hint" ne_string_list(hints) "}" ] ->
  [ repair_module ~opaques:opaques ~hints:hints id d_orn d_orn_inv mod_ref ]
END

(* Register the Ltac script for sigma unpacking *)
VERNAC COMMAND EXTEND UnpackSigma CLASSIFIED AS SIDEFF
| [ "Unpack" reference(const_ref) "as" ident(id) ] ->
  [ do_unpack_constant id const_ref ]
END
