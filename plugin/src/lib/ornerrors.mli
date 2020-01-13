open CErrors
open Environ
open Evd

(*
 * Errors and error messages
 *)

(* --- Exceptions --- *)

exception NotEliminators
exception NotInductive
exception NotAlgebraic

(* --- Error descriptions --- *)

val err_unsupported_change : Pp.t
val err_new_parameter : Pp.t
val err_new_constructor : Pp.t
val err_unexpected_change : String.t -> Pp.t
val err_type : env -> evar_map -> Pretype_errors.pretype_error -> Pp.t
val err_opaque_not_constant : Libnames.qualid -> Pp.t

(* --- Possible workaround suggestions --- *)

val try_opaque : Pp.t
val try_not_opaque : Pp.t
val try_preprocess : Pp.t
val try_check_typos : Pp.t
val try_fully_qualify : Pp.t
val try_supported : Pp.t

(* --- Reasons to cut an issue --- *)

val cool_feature : Pp.t
val problematic : Pp.t
val mistake : Pp.t

(* --- Putting these together --- *)
    
(*
 * Our own user_err function to make it easier to present nice information
 * to the user
 *)
val user_err :
  String.t -> (* where you're calling it from *)
  Pp.t -> (* error description *)
  Pp.t list -> (* workaround suggestions *)
  Pp.t list -> (* reasons to cut an issue *)
  'a
