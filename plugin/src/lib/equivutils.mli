(*
 * Utilities for the Equivalence typeclass
 *)

open Constr
open Names

(* Getter for the proof of reflexivity from a proof of equivalence *)
val equiv_refl_getter : constr

(* Getter for the proof of symmetry from a proof of equivalence *)
val equiv_sym_getter : constr

(* Getter for the proof of transitivity from a proof of equivalence *)
val equiv_trans_getter : constr
