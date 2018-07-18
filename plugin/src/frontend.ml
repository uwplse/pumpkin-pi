open Util
open Constrexpr (* just for [constr_expr] *)
open Constr
open Names
open Environ (* just for [env] *)
open Utilities
open Coqterms
open Differencing
open Lifting
open Promotions
open Specialization
open Zooming
open Hypotheses

type ornamental_action = env -> Evd.evar_map -> constr -> constr -> constr -> constr * constr option
type ornamental_command = Id.t -> constr_expr -> constr_expr -> constr_expr -> unit

(* Identify an algebraic ornament between two types and define its conversion functions  *)
let find_ornament n d_old d_new =
  let (evm, env) = Lemmas.get_current_context () in
  let trm_o = unwrap_definition env (intern env evm d_old) in
  let trm_n = unwrap_definition env (intern env evm d_new) in
  if isInd trm_o && isInd trm_n then
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env evm idx_n trm_o trm_n in
    begin
      match orn.indexer with
      | Some idx ->
        define_term idx_n evm idx;
        Printf.printf "Defined indexing function %s.\n\n" (Id.to_string idx_n);
      | None -> ()
    end;
    define_term n evm orn.promote;
    Printf.printf "Defined promotion %s.\n\n" (Id.to_string n);
    let inv_n = with_suffix n "inv" in
    define_term inv_n evm orn.forget
  else
    failwith "Only inductive types are supported"

(* TODO temporary: given just an application of the IP, lift it *)
let lift_induction env evd c_orn c_orn_inv c_old =
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let c_new = lift_induction_principle env evd l c_old in
  (c_new, None)

(* Apply an ornament without meta-reduction *)
let apply_ornament env evd c_orn c_orn_inv c_old =
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let c_new = apply_indexing_ornament env evd l c_old in
  (c_new, None)

(* Meta-reduce a ornamental lifting *)
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

(* Post-facto modularization of a meta-reduced ornamental lifting/application *)
let modularize_ornament env evd c_orn c_orn_inv c_old =
  let is_fwd = direction env evd c_orn in
  let (promote, forget) = map_if reverse (not is_fwd) (c_orn, c_orn_inv) in
  let orn = initialize_promotion env evd promote forget in
  let l = initialize_lifting orn is_fwd in
  let (c_new, _) = higher_lift env evd l c_old in
  (* TODO: Generate proof of indexing coherence. *)
  (c_new, None)

(* Perform application, meta-reduction, and modularization all in sequence *)
let lift_by_ornament env evd c_orn c_orn_inv c_old =
  let (c_app, c_app_idx_opt) = apply_ornament env evd c_orn c_orn_inv c_old in
  let (c_red, c_red_idx_opt) = reduce_ornament env evd c_orn c_orn_inv c_app in
  let (c_mod, c_mod_idx_opt) = modularize_ornament env evd c_orn c_orn_inv c_red in
  let c_idx_opt = Option.append c_mod_idx_opt (Option.append c_red_idx_opt c_app_idx_opt) in
  (c_mod, c_idx_opt)

let try_define_indexer evd n c_idx =
  let idx_n = with_suffix n "index" in
  let idx_s = Id.to_string idx_n in
  try
    define_term idx_n evd c_idx;
    Printf.printf "Defined indexer %s.\n\n" idx_s
  with _ ->
    Printf.printf "WARNING: Failed to define indexer %s. Ignoring for now.\n\n" idx_s

(* Transform an ornamental action into an ornamental command *)
let make_ornamental_command act =
  let cmd n d_old d_orn d_orn_inv =
    let (evd, env) = Lemmas.get_current_context () in
    let c_orn = intern env evd d_orn in
    let c_orn_inv = intern env evd d_orn_inv in
    let c_old = intern env evd d_old in
    let (c_new, c_idx_opt) = act env evd c_orn c_orn_inv c_old in
    define_term n evd c_new;
    Option.iter (try_define_indexer evd n) c_idx_opt;
    declare_lifted evd c_old (make_constant n)
  in
  cmd
