DECLARE PLUGIN "ornamental"

open Util
open Term
open Names
open Environ
open Stdarg
open Utilities
open Coqterms
open Printing
open Differencing
open Lifting
open Promotions
open Specialization

(* --- Top-level --- *)

(* Identify an ornament *)
let find_ornament n d_old d_new =
  let (evm, env) = Lemmas.get_current_context () in
  let trm_o = unwrap_definition env (intern env evm d_old) in
  let trm_n = unwrap_definition env (intern env evm d_new) in
  if isInd trm_o && isInd trm_n then
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env evm idx_n trm_o trm_n in
    let idx = orn.indexer in
    (if Option.has_some idx then
       let _ = define_term idx_n evm (Option.get idx) in
       Printf.printf "Defined indexing function %s.\n\n" (string_of_id idx_n);
       ()
     else
       ());
    define_term n evm orn.promote;
    Printf.printf "Defined promotion %s.\n\n" (string_of_id n);
    let inv_n = with_suffix n "inv" in
    define_term inv_n evm orn.forget;
    ()
  else
    failwith "Only inductive types are supported"


(* Apply an ornament, but don't reduce *)
let apply_ornament env evd c_orn c_orn_inv c_old =
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  apply_indexing_ornament env evd l c_old

(* Reduce an application of an ornament *)
let reduce_ornament env evd c_orn c_orn_inv c_old =
  let trm_o = unwrap_definition env c_old in
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let (trm_n, c_idx_opt) = internalize env evd l trm_o in
  let l_idx = { l with is_indexer = true } in
  let c_idx_opt' = c_idx_opt |> Option.map (internalize env evd l_idx) |> Option.map fst in
  (trm_n, c_idx_opt')

let try_define_indexer evd n c_idx =
  let idx_n = with_suffix n "index" in
  let idx_s = string_of_id idx_n in
  try
    define_term idx_n evd c_idx;
    Printf.printf "Defined indexer %s.\n\n" idx_s
  with _ ->
    Printf.printf "WARNING: Failed to define indexer %s. Ignoring for now.\n\n" idx_s

(* Higher lifting *)
let higher_lifting env evd c_orn c_orn_inv c_old =
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let (higher_lifted, _) = higher_lift env evd l c_old in
  (* TODO indexing proof *)
  higher_lifted

(* --- Commands --- *)

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND MultiOrnament CLASSIFIED AS SIDEFF
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
    let c_new = apply_ornament env evd c_orn c_orn_inv c_old in
    define_term n evd c_new;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined ornamented fuction %s.\n\n" (string_of_id n) ]
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
    Printf.printf "Defined reduced ornamented function %s.\n\n" (string_of_id n) ]
END

(*
 * The higher-lifting step is not type-preserving, but instead
 * takes a meta-reduced application and substitutes in an already-lifted
 * type that still occurs in the meta-reduced term and type.
 *)
VERNAC COMMAND EXTEND HigherLifting CLASSIFIED AS SIDEFF
| [ "Higher" "lift" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n) ] ->
  [ let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let c_new = higher_lifting env evd c_orn c_orn_inv c_old in
    define_term n evd c_new;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined higher-lifted ornamented fuction %s.\n\n" (string_of_id n) ]
END

(* Lift and meta-reduce a term across an ornament. *)
VERNAC COMMAND EXTEND OrnamentLift CLASSIFIED AS SIDEFF
| [ "Ornamental" "Definition" ident(n) "from" constr(d_old) "using" constr(d_orn) constr(d_orn_inv)] ->
  [ let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let c_app = apply_ornament env evd c_orn c_orn_inv c_old in
    let (c_red, c_idx_opt) = reduce_ornament env evd c_orn c_orn_inv c_app in
    let c_cmp = higher_lifting env evd c_orn c_orn_inv c_red in
    Option.iter (try_define_indexer evd n) c_idx_opt;
    define_term n evd c_cmp;
    declare_lifted evd c_old (make_constant n);
    Printf.printf "Defined reduced ornamented function %s.\n\n" (string_of_id n) ]
END
