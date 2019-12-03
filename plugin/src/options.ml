open Ltac_plugin

(* --- Options for DEVOID --- *)

(*
 * Prove the coherence property of the algebraic promotion isomorphism
 *)
let opt_search_coh = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate a proof of coherence in search for DEVOID";
  Goptions.optkey = ["DEVOID"; "search"; "prove"; "coherence"];
  Goptions.optread = (fun () -> !opt_search_coh);
  Goptions.optwrite = (fun b -> opt_search_coh := b);
}

let is_search_coh () = !opt_search_coh

(*
 * Prove section and retraction
 *)
let opt_search_equiv = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Generate proof of equivalence in search for DEVOID";
  Goptions.optkey = ["DEVOID"; "search"; "prove"; "equivalence"];
  Goptions.optread = (fun () -> !opt_search_equiv);
  Goptions.optwrite = (fun b -> opt_search_equiv := b);
}

let is_search_equiv () = !opt_search_equiv

(*
 * Lift the type as well, rather than using the automatically inferred type
 *)
let opt_lift_type = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optdepr = false;
  Goptions.optname = "Use lifted rather than inferred types in DEVOID";
  Goptions.optkey = ["DEVOID"; "lift"; "type"];
  Goptions.optread = (fun () -> !opt_lift_type);
  Goptions.optwrite = (fun b -> opt_lift_type := b);
}

let is_lift_type () = !opt_lift_type
