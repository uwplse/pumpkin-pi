open Constr
open Environ
open Evd
open Stateutils

(* --- Ornamental promotions --- *)

(*
 * The kind of ornament that is stored
 *)
type kind_of_orn =
  | Algebraic of constr * int
  | CurryRecord
  | SwapConstruct of (int * int) list
  | UnpackSigma
  | Custom of (types * types)

(*
 * An ornamental promotion is a function from T1 -> T2,
 * a function from T2 -> T1, and a kind of ornament.
 *)
type promotion =
  {
    promote : types;
    forget : types;
    kind : kind_of_orn;
  }

(* --- Useful function for finding swaps from promotion function --- *)

(*
 * This assumes exactly one of promote or forget is present
 *)
val swap_map_of_promote_or_forget :
  env ->
  types -> (* a *)
  types -> (* b *)
  constr option -> (* promote, if present *)
  constr option -> (* forget, if present *)
  evar_map ->
  ((pconstructor * pconstructor) list) state
