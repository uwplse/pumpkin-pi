open Util
open Libnames
open Ltac_plugin

let tactic_script =
  qualid_of_string "Ornamental.Unpack.unpack"

(* Evaluate a tactic on no goals and return any proofs constructed *)
let eval_tactic env sigma ?goal tac =
  let (_, (typ, _)) = Evarutil.new_type_evar env !sigma Evd.univ_flexible_alg in
  let (ent, pv) = Proofview.init !sigma [(env, typ)] in
  let sigma0 = !sigma in
  let (_, pv, (unsafe, shelved, obliged), _) = Proofview.apply ~name:(qualid_basename tactic_script) ~poly:true env (Proofview.tclUNIT tac) pv in
  sigma := Proofview.proofview pv |> snd;
  (* NOTE: Technically our current examples/tests do not require this post-processing
   * unification step, but I suspect that it may sometimes be necessary to ensure that
   * Coq handles any lingering typeclass/implicit argument inference in the usual way. *)
  sigma := Pretyping.solve_remaining_evars (Pretyping.default_inference_flags true) env !sigma ?initial:(Some sigma0);
  let proofs = Proofview.partial_proof ent pv |> List.map (EConstr.to_constr !sigma) in
  List.hd proofs

let call_tactic env sigma tac args =
  let open Tacexpr in
  let args = List.map (fun e -> ConstrMayEval (Genredexpr.ConstrTerm e)) args in
  let tac = Tacinterp.interp (TacArg (CAst.make (TacCall (CAst.make (tac, args))))) in
  eval_tactic env sigma tac

let unpack_constant env sigma const =
  let (_, (constr, _)) = Evarutil.new_type_evar env !sigma Evd.univ_rigid in
  call_tactic env sigma tactic_script [Constrextern.extern_constr false env !sigma constr]
