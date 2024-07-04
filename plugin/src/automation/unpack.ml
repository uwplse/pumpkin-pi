open Util
open Libnames
open Ltac_plugin

let tactic_script =
  qualid_of_string "Ornamental.Unpack.unpack"

(* Evaluate a tactic on no goals and return any proofs constructed *)
let eval_tactic env sigma ?goal tac =
  let (sigma, (typ, _)) = Evarutil.new_type_evar env sigma Evd.univ_flexible_alg in
  let (ent, pv) = Proofview.init sigma [(env, typ)] in
  let sigma0 = sigma in
  let ((), pv, unsafe, _) = Proofview.apply ~name:(qualid_basename tactic_script) ~poly:true env tac pv in
  let sigma = Proofview.return pv in
  (* NOTE: Technically our current examples/tests do not require this post-processing
   * unification step, but I suspect that it may sometimes be necessary to ensure that
   * Coq handles any lingering typeclass/implicit argument inference in the usual way. *)
  let sigma = Pretyping.solve_remaining_evars (Pretyping.default_inference_flags true) env ~initial:sigma0 sigma  in
  let proofs = Proofview.partial_proof ent pv |> List.map (EConstr.to_constr ~abort_on_undefined_evars:false sigma) in
  sigma, List.hd proofs

let call_tactic env sigma tac args =
  let open Tacexpr in
  let args = List.map (fun e -> ConstrMayEval (Genredexpr.ConstrTerm e)) args in
  CAst.make (TacArg  (TacCall (CAst.make (tac, args)))) |> Tacinterp.interp |>
  eval_tactic env sigma

let unpack_constant env sigma const =
  let sigma, term = Evarutil.new_global sigma (Names.GlobRef.ConstRef const) in
  call_tactic env sigma tactic_script [Constrextern.extern_constr ~lax:false env sigma term]
