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
