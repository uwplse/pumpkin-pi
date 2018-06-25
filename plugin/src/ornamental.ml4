DECLARE PLUGIN "ornamental"

open Util
open Names
open Stdarg
open Frontend
open Utilities
open Coqterms
open Lifting

(* --- Top-level --- *)

let try_define_indexer evd n c_idx =
  let idx_n = with_suffix n "index" in
  let idx_s = Id.to_string idx_n in
  try
    define_term idx_n evd c_idx;
    Printf.printf "Defined indexer %s.\n\n" idx_s
  with _ ->
    Printf.printf "WARNING: Failed to define indexer %s. Ignoring for now.\n\n" idx_s

(* --- Commands --- *)

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND DefineOrnament CLASSIFIED AS SIDEFF
| [ "Ornament" ident(n) "from" constr(d_old) "to" constr(d_new)] ->
  [ find_ornament n d_old d_new ]
END

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
VERNAC COMMAND EXTEND ApplyOrnament CLASSIFIED AS SIDEFF
| [ "Apply" "Ornament" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let (c_new, _) = apply_ornament env evd c_orn c_orn_inv c_old in
    define_term n evd c_new;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined ornamented fuction %s.\n\n" (Id.to_string n) ]
END

(*
 * Meta-reduce an application of an ornament.
 * This command should always preserve the type of the argument,
 * but produce a term inducts over the new domain and reduces
 * internal application as much as possible. So for simple
 * functions, this will be enough, but for proofs, there is one more step.
 *)
VERNAC COMMAND EXTEND ReduceOrnament CLASSIFIED AS SIDEFF
| [ "Reduce" "Ornament" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let (c_new, c_idx_opt) = reduce_ornament env evd c_orn c_orn_inv c_old in
    Option.iter (try_define_indexer evd n) c_idx_opt;
    define_term n evd c_new;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined reduced ornamented function %s.\n\n" (Id.to_string n) ]
END

(*
 * The higher-lifting step is not type-preserving, but instead
 * takes a meta-reduced application and substitutes in an already-lifted
 * type that still occurs in the meta-reduced term and type.
 *)
VERNAC COMMAND EXTEND HigherLifting CLASSIFIED AS SIDEFF
| [ "Higher" "Lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n) ] ->
  [ let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let (c_new, _) = modularize_ornament env evd c_orn c_orn_inv c_old in
    define_term n evd c_new;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined higher-lifted ornamented fuction %s.\n\n" (Id.to_string n) ]
END

(* Lift and meta-reduce a term across an ornament. *)
VERNAC COMMAND EXTEND OrnamentLift CLASSIFIED AS SIDEFF
| [ "Ornamental" "Definition" ident(n) "from" constr(d_old) "using" constr(d_orn) constr(d_orn_inv)] ->
  [ let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let (c_app, _) = apply_ornament env evd c_orn c_orn_inv c_old in
    let (c_red, c_idx_opt) = reduce_ornament env evd c_orn c_orn_inv c_app in
    let (c_mod, _) = modularize_ornament env evd c_orn c_orn_inv c_red in
    Option.iter (try_define_indexer evd n) c_idx_opt;
    define_term n evd c_mod;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined reduced ornamented function %s.\n\n" (Id.to_string n) ]
END
