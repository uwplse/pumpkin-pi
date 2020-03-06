(*
 * If the appropriate option is set, DEVOID generates useful "smart eliminators"
 * in addition to the equivalences it discovers. For example, for algebraic
 * ornaments, it generates and automatically lifts a useful eliminator over
 * { a : A & indexer a = i_b } that helps the user combine proofs about A and
 * proofs about the index of a, so that later the user can get proofs about
 * unpacked B.
 *)

(*
 * Generate the list of smart eliminators
 *)
let find_smart_elims l env sigma =
  sigma, []
