open Names
open Constr
open Environ
open Evd
open Lifting
open Stateutils

val find_eq_rel_for_source_type :
  Lifting.lifting ->
  env ->
  evar_map ->
  Constr.t ->
  evar_map * Constr.t

val find_eq_rel_for_target_type :
  Lifting.lifting ->
  env ->
  evar_map ->
  Constr.t ->
  evar_map * Constr.t

val find_type_for_eq_rel_source_setoid :
  Lifting.lifting ->
  env ->
  evar_map ->
  Constr.t ->
  evar_map * (Constr.t option)

val find_eq_proof_for_source_type :
  Lifting.lifting ->
  env ->
  evar_map ->
  Constr.t ->
  evar_map * Constr.t

val find_eq_proof_for_target_type :
  Lifting.lifting ->
  env ->
  evar_map ->
  Constr.t ->
  evar_map * Constr.t

val start_rewrite_annotation :
  Constr.t

val rewrite_tactic_from_id :
  Id.t ->
  unit Proofview.tactic

val setoid_rewrite_tactic_from_id :
  Id.t ->
  unit Proofview.tactic
