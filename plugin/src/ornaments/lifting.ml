(*
 * Datatypes for promotions and lifting
 *)

open Utilities
open Term
open Environ

(* --- Datatypes --- *)

(*
 * For now, an ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, a function from T2 -> T1. Later, it will also contain
 * patches and extra premises, and these will be present both in the top-level
 * type and as premises to the functions in both directions.
 *
 * We don't represent ornaments directly, yet, but this may also be useful.
 *)
type promotion =
  {
    index_i : int option;
    indexer : types option;
    promote : types;
    forget : types;
  }

(*
 * A lifting is an ornamental promotion between types, a direction,
 * a hint whether it corresponds to an indexing function for an outer lifting,
 * and an optional indexer for the promoted function.
 *
 * I may add more things here later. This is just a convenient configuration
 * for promoting functions.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
    is_indexer : bool;
    lifted_indexer : types option;
  }

(*
 * A composition is a pair of functions and environments with
 * a corresponding lifting. It also contains a hint is_g, which says
 * whether lifting is applied to g or to f. This represents a single (factored)
 * applied but not simplified ornamentation.
 *)
type composition =
  {
    l : lifting;
    g : env * types;
    f : env * types;
    is_g : bool;
  }

(* --- Initialization --- *)

(*
 * Initialize a lifting
 *)
let initialize_lifting orn is_fwd =
  let lifted_indexer = None in
  let is_indexer = false in
  { orn ; is_fwd ; lifted_indexer ; is_indexer }

(* --- Control structures --- *)
    
(*
 * These two functions determine what function to use to go back to
 * an old type or get to a new type when lifting
 *)
let lift_back (l : lifting) = if l.is_fwd then l.orn.forget else l.orn.promote
let lift_to (l : lifting) = if l.is_fwd then l.orn.promote else l.orn.forget

(* Other control structures *)
let directional l a b = if l.is_fwd then a else b
let if_indexer l a b = if l.is_indexer then a else b
let map_directional f g l x = map_if_else f g l.is_fwd x
let map_indexer f g l x = map_if_else f g l.is_indexer x
let map_forward f l x = map_if f l.is_fwd x
let map_if_indexer f l x = map_if f l.is_indexer x
