DECLARE PLUGIN "ornamental"

open Term
open Names
open Environ
open Constrarg

(* --- Top-level --- *)

(* Identify an ornament *)
let find_ornament n d_old d_new =
  let (evm, env) = Lemmas.get_current_context () in
  let old_term = Constrintern.interp_constr env evm d_old in
  let new_term = Constrintern.interp_constr env evm d_new in
  (* TODO *)
  ()

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find ornament" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ find_ornament n d_old d_new ]
END
