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

VERNAC COMMAND EXTEND Ornamental CLASSIFIED AS SIDEFF
(*
 * Given an ornament and a function, derive the ornamented version that
 * doesn't internalize the ornament.
 *
 * This is equivalent to porting the hypotheses and conclusions we apply
 * the function to via the ornament, but not actually reducing the
 * result to get something of a useful type. It's the first step in
 * lifting functions, which will be chained eventually to lift
 * functions entirely.
 *)
| [ "Ornamental" "Application" ident(n) "from" constr(d_old) "using" constr(d_orn) constr(d_orn_inv) ] ->
  [ make_ornamental_command apply_ornament n d_old d_orn d_orn_inv;
    Printf.printf "Defined ornamented fuction %s.\n\n" (Id.to_string n) ]
(*
 * Meta-reduce an application of an ornament.
 * This command should always preserve the type of the argument,
 * but produce a term inducts over the new domain and reduces
 * internal application as much as possible. So for simple
 * functions, this will be enough, but for proofs, there is one more step.
 *)
| [ "Ornamental" "Reduction" ident(n) "from" constr(d_old) "using" constr(d_orn) constr(d_orn_inv) ] ->
  [ make_ornamental_command reduce_ornament n d_old d_orn d_orn_inv;
    Printf.printf "Defined reduced ornamented function %s.\n\n" (Id.to_string n) ]
(*
 * The higher-lifting step is not type-preserving, but instead
 * takes a meta-reduced application and substitutes in an already-lifted
 * type that still occurs in the meta-reduced term and type.
 *)
| [ "Ornamental" "Modularization" ident(n) "from" constr(d_old) "using" constr(d_orn) constr(d_orn_inv) ] ->
  [ make_ornamental_command modularize_ornament n d_old d_orn d_orn_inv;
    Printf.printf "Defined modularized ornamented fuction %s.\n\n" (Id.to_string n) ]
(* Do all of the above with a single command. *)
| [ "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ make_ornamental_command lift_by_ornament n d_old d_orn d_orn_inv;
    Printf.printf "Defined lifted function %s.\n\n" (Id.to_string n) ]
END
