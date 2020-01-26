open Constr
open Envutils

(* --- Utilities for delta reduction --- *)

(*
 * Delta-reduce until we hit an inductive type, or otherwise return the original
 *)
let try_delta_inductive env trm =
  let unr = unwrap_definition env trm in
  if isInd unr then unr else trm
