open Stateutils
open Evarutil
open Envutils
open Evarconv
open Utilities

(*
 * Utilities for unification
 *)

(*
 * Make n new evars of any type
 *)
let mk_n_evars n env =
  map_state
    (fun r sigma ->
      let sigma, (earg_typ, _) = new_type_evar env sigma Evd.univ_flexible in
      let sigma, earg = new_evar env sigma earg_typ in
      sigma, EConstr.to_constr sigma earg)
    (mk_n_rels n)

(*
 * Internal call to unification that takes econstrs
 *)
let eunify env etrm1 etrm2 sigma =
  try
    the_conv_x env etrm1 etrm2 sigma, true
  with _ ->
    sigma, false
    
(*
 * Try unification, but catch errors and return the appropriate evar_map
 *)
let unify env trm1 trm2 sigma =
  eunify env (EConstr.of_constr trm1) (EConstr.of_constr trm2) sigma

(*
 * Unify and force evar resolution
 * Return None if cannot unify or cannot resolve evars
 *)
let unify_resolve_evars env trm1 trm2 sigma =
  let etrm1, etrm2 = map_tuple EConstr.of_constr (trm1, trm2) in
  let sigma, unifies = eunify env etrm1 etrm2 sigma in
  if unifies then
    try
      let sigma, etrm1 = Typing.solve_evars env sigma etrm1 in
      let sigma, etrm2 = Typing.solve_evars env sigma etrm2 in
      sigma, Some (map_tuple (EConstr.to_constr sigma) (etrm1, etrm2))
    with _ ->
      sigma, None
  else
    sigma, None
