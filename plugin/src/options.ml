
(* --- Options for PUMPKIN Pi (these refer to DEVOID for legacy reasons) --- *)

(*
 * Prove the coherence property of the algebraic promotion isomorphism
 * (disabled by default)
 *)
let opt_search_coh = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate a proof of coherence in search for algebraic ornaments";
  Goptions.optkey = ["DEVOID"; "search"; "prove"; "coherence"];
  Goptions.optread = (fun () -> !opt_search_coh);
  Goptions.optwrite = (fun b -> opt_search_coh := b);
}

let is_search_coh () = !opt_search_coh

(*
 * Prove an unpacked version of the ornamental promotion isomorphism
 * (disabled by default)
 *)
let opt_unpack_algebraic = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate unpacked equivalence in search for algebraic ornaments";
  Goptions.optkey = ["DEVOID"; "search"; "unpack"; "algebraic"];
  Goptions.optread = (fun () -> !opt_unpack_algebraic);
  Goptions.optwrite = (fun b -> opt_unpack_algebraic := b);
}

let is_unpack_algebraic () = !opt_unpack_algebraic

(*
 * Prove section and retraction
 * (disabled by default)
 *)
let opt_search_equiv = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate proof of equivalence";
  Goptions.optkey = ["DEVOID"; "search"; "prove"; "equivalence"];
  Goptions.optread = (fun () -> !opt_search_equiv);
  Goptions.optwrite = (fun b -> opt_search_equiv := b);
}

let is_search_equiv () = !opt_search_equiv

(*
 * Generate useful eliminators in addition to the discovered equivalence
 * (disabled by default)
 *)
let opt_smart_elim = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate useful eliminators for reasoning about algebraic ornaments";
  Goptions.optkey = ["DEVOID"; "search"; "smart"; "eliminators"];
  Goptions.optread = (fun () -> !opt_smart_elim);
  Goptions.optwrite = (fun b -> opt_smart_elim := b);
}

let is_smart_elim () = !opt_smart_elim

(*
 * Lift the type as well, rather than using the automatically inferred type
 * (disabled by default)
 *)
let opt_lift_type = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Use lifted rather than inferred types";
  Goptions.optkey = ["DEVOID"; "lift"; "type"];
  Goptions.optread = (fun () -> !opt_lift_type);
  Goptions.optwrite = (fun b -> opt_lift_type := b);
}

let is_lift_type () = !opt_lift_type

(*
 * If lifting a constant across an ornament does not change
 * the term, add that term to the global cache for later
 * (enabled by default)
 *)
let opt_smart_cache = ref (true)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Automatically cache unchanged lifted constants";
  Goptions.optkey = ["DEVOID"; "smart"; "cache"];
  Goptions.optread = (fun () -> !opt_smart_cache);
  Goptions.optwrite = (fun b -> opt_smart_cache := b);
}

let is_smart_cache () = !opt_smart_cache
