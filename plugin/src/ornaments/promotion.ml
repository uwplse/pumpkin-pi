open Constr

(* --- Ornamental promotions --- *)

(*
 * The kind of ornament that is stored
 *)
type kind_of_orn = Algebraic of constr * int | CurryRecord

(*
 * An ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, and a function from T2 -> T1.
 *)
type promotion =
  {
    promote : types;
    forget : types;
    kind : kind_of_orn;
  }
