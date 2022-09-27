open Util
open Libnames
open Ltac_plugin

let tactic_script =
  qualid_of_string "Ornamental.Unpack.unpack"

(* Evaluate a tactic on no goals and return any proofs constructed *)
let eval_tactic env sigma ?goal tac =
  let (_, (typ, _)) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let sigma_ref = ref sigma in
  let (ent, pv) = Proofview.init !sigma_ref [(env, typ)] in
  let sigma0 = !sigma_ref in
  let (_, pv, (unsafe, shelved, obliged), _) = Proofview.apply ~name:tac ~poly:true env (Proofview.tclUNIT tac) pv in
  sigma_ref := Proofview.proofview pv |> snd;
  (* NOTE: Technically our current examples/tests do not require this post-processing
   * unification step, but I suspect that it may sometimes be necessary to ensure that
   * Coq handles any lingering typeclass/implicit argument inference in the usual way. *)
  sigma_ref := Pretyping.solve_remaining_evars (Pretyping.default_inference_flags true) env !sigma_ref ?initial:(Some sigma0);
  let proofs = Proofview.partial_proof ent pv |> List.map (EConstr.to_constr !sigma_ref) in
  List.hd proofs

let call_tactic env sigma tac args =
  let open Tacexpr in
  let args = List.map (fun e -> ConstrMayEval (Genredexpr.ConstrTerm e)) args in
  TacArg (Loc.tag (TacCall (Loc.tag (tac, args)))) |> Tacinterp.interp |>
  eval_tactic env sigma

let unpack_constant env sigma const =
  let term = Evarutil.e_new_global sigma (Names.GlobRef.ConstRef const) in
  call_tactic env sigma tactic_script [Constrextern.extern_constr false env !sigma term]
