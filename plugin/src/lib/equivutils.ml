(*
 * Utilities for the Equivalence typeclass
 *)

open Constr
open Names

let coq_classes_relationclasses =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["RelationClasses" ; "Classes" ; "Coq"]))

(* Getter for the proof of reflexivity from a proof of equivalence *)
let equiv_refl_getter : constr =
  mkConst (Constant.make2 coq_classes_relationclasses (Label.make "Equivalence_Reflexive"))

(* Getter for the proof of symmetry from a proof of equivalence *)
let equiv_sym_getter : constr =
  mkConst (Constant.make2 coq_classes_relationclasses (Label.make "Equivalence_Symmetric"))

(* Getter for the proof of transitivity from a proof of equivalence *)
let equiv_trans_getter : constr =
  mkConst (Constant.make2 coq_classes_relationclasses (Label.make "Equivalence_Transitive"))
