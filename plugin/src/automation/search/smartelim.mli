open Environ
open Evd
open Constr
open Stateutils
open Lifting
open Names

(*
 * If the appropriate option is set, CARROT generates useful "smart eliminators"
 * in addition to the equivalences it discovers. For example, for algebraic
 * ornaments, it generates and automatically lifts a useful eliminator over
 * { a : A & indexer a = i_b } that helps the user combine proofs about A and
 * proofs about the index of a, so that later the user can get proofs about
 * unpacked B after lifting.
 *)

(*
 * Generate the list of smart eliminators
 *)
val find_smart_elims :
  lifting -> env -> evar_map -> ((Id.t * constr * types) list) state
