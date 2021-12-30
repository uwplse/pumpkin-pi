(* --- Options for PUMPKIN Pi --- *)

       
(*
 * Prove the coherence property of the algebraic promotion isomorphism
 * (disabled by default)
 *)
val is_search_coh : unit -> bool

(*
 * Generate an unpacked version of the algebraic promotion isomorphism
 * (disabled by default)
 *)
val is_unpack_algebraic : unit -> bool
  
(*
 * Prove section and retraction for the algebraic promotion isomorphism
 * (disabled by default)
 *)
val is_search_equiv : unit -> bool

(*
 * Generate useful eliminators in addition to the discovered equivalence
 * (disabled by default)
 *)
val is_smart_elim : unit -> bool

(*
 * Lift the type too, rather than letting Coq infer the type of a lifted term
 * (disabled by default)
 *)
val is_lift_type : unit -> bool

(*
 * Add unchanged lifted constants to the global lifting cache automatically
 * (enabled by default)
 *)
val is_smart_cache : unit -> bool
