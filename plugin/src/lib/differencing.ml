(*
 * Differencing for ornamenting inductive types
 *)

open Term
open Environ
open Coqterms
open Utilities

(* --- Differencing terms --- *)

(* Check if two terms have the same type, ignoring universe inconsinstency *)
let same_type env evd o n =
  let (env_o, t_o) = o in
  let (env_n, t_n) = n in
  try
    convertible env (infer_type env_o evd t_o) (infer_type env_n evd t_n)
  with _ ->
    false

(* --- Differencing inductive types --- *)

(* is_or_applies over two terms with a different check *)
let apply_old_new (o : types * types) (n : types * types) : bool =
  let (trm_o, trm_o') = o in
  let (trm_n, trm_n') = n in
  is_or_applies trm_o trm_o' && is_or_applies trm_n trm_n'

(* Check if two terms are the same modulo a change of an inductive type *)
let same_mod_change env o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  apply_old_new o n || convertible env t_o t_n

(* Check if two terms are the same modulo an indexing of an inductive type *)
let same_mod_indexing env p_index o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  are_or_apply p_index t_o t_n || same_mod_change env o n
