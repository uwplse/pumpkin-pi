open Constr

(* --- Ornamental promotions --- *)

(*
 * The kind of ornament that is stored
 *)
type kind_of_orn =
  | Algebraic of constr * int
  | CurryRecord
  | SwapConstruct of (int * int) list

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
