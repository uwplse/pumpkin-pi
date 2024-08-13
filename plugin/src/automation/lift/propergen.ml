(*
 * Functions for generating proofs that a term is Proper
 * when doing setoid repair.
 *)

open Constr
open Names
open Apputils

(* The number of seconds solve_proper can run for before timing out. *)
let solve_proper_timeout = 10

let coq_init_logic =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["Logic"; "Init"; "Coq"]))

let iff =
  mkConst (Constant.make2 coq_init_logic (Label.make "iff"))

let coq_classes_morphisms =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["Morphisms"; "Classes"; "Coq"]))

let respectful_evaluable_glob_ref =
  Names.EvalConstRef (Constant.make2 coq_classes_morphisms (Label.make "respectful"))

let respectful =
  mkConst (Constant.make2 coq_classes_morphisms (Label.make "respectful"))

let proper_glob_ref =
  Names.GlobRef.ConstRef (Constant.make2 coq_classes_morphisms (Label.make "Proper"))

let proper =
  mkConst (Constant.make2 coq_classes_morphisms (Label.make "Proper"))

let solve_proper_tac = fun () ->
  Decompiler.parse_tac_str (Format.asprintf "%a" Pp.pp_with (Pp.str "solve_proper2"))

let solve_elim_proper_tac = fun () ->
  Decompiler.parse_tac_str (Format.asprintf "%a" Pp.pp_with (Pp.str "solve_elim_proper"))

(* Returns true if trm has no relative variables in it. *)
let rec no_rels trm =
  let kind_trm = Constr.kind trm in
  match kind_trm with
  | Rel _ -> false
  | _ -> Constr.fold (fun b t -> b && (no_rels t)) true trm

(* Returns true if typ is a non-dependent function type. *)
let is_simple_fun_type typ =
  Constr.isProd typ && no_rels typ

(*
 * If typ is a (possibly 0-ary) function type and is not a 
 * dependent type, return Some (l, o), where l is list of 
 * the input types with the first input type at the head 
 * and o is the output type. 
 * Undefined if typ is not a non-dependent function type. 
 *)
let rec types_from_simple_fun_type env sigma typ =
  let kind_typ = Constr.kind typ in
  match kind_typ with
  | Prod (n, t, b) ->
     (let sigma, o = types_from_simple_fun_type env sigma b in
     match o with
     | None -> sigma, None
     | Some (l, t2) -> sigma, Some (t :: l, t2))
  | _ -> sigma, Some ([], typ)

let rec fun_type_from_type_list env typ_list =
  match typ_list with
  | [] -> failwith "Cannot construct a function type with no types."
  | h :: [] -> h
  | h1 :: h2 :: t ->
     (let fresh_var = Name (Envutils.fresh_name env Anonymous) in
      mkProd (fresh_var, h1, fun_type_from_type_list env (h2 :: t)))

let rec resp_from_typ_list c env sigma l =
  let eq_rel_for_type sigma typ =
    let sigma, sort_family = Inference.infer_type env sigma typ in
      if is_Prop typ then
         sigma, iff
      else
         Lift.find_eq_rel_for_type c env sigma typ in
  match l with
  | [] -> failwith "Undefined."
  | h :: [] -> eq_rel_for_type sigma h
  | h1 :: h2 :: t ->
     (Feedback.msg_warning (Pp.str "1");
      let sigma, eq_rel = eq_rel_for_type sigma h1 in
      Feedback.msg_warning (Pp.str "2");
      let sigma, tail = resp_from_typ_list c env sigma (h2 :: t) in
      Feedback.msg_warning (Pp.str "3");
      let f = (fun_type_from_type_list env (h2 :: t)) in
      Feedback.msg_warning (Pp.str "4");
      let x = mkAppl (respectful, [h1 ; f ; eq_rel ; tail]) in
      Feedback.msg_warning (Pp.str "5");
      (sigma, x))

(* typ is the intended type of trm *)
let proper_from_type_list c env sigma typ_list typ trm =
  let sigma, x = resp_from_typ_list c env sigma typ_list in
  Feedback.msg_warning (Pp.str "h");
  sigma, Some (mkAppl (proper, [typ ; x ; trm]))

let generate_proper_goal_from_trm c env sigma trm =
  let sigma, typ = Inference.infer_type env sigma trm in
  let sigma, reduced_typ = Reducers.reduce_nf env sigma typ in
  Feedback.msg_warning (Pp.str "f");
  if not (is_simple_fun_type reduced_typ) then
    let _ = Feedback.msg_warning (Pp.str "i") in
    sigma, None
  else 
    let sigma, o = types_from_simple_fun_type env sigma reduced_typ in
    Feedback.msg_warning (Pp.str "g");
    match o with
    | None -> sigma, None
    | Some (typ_list, out_typ) ->
       proper_from_type_list c env sigma (List.append typ_list [out_typ]) typ trm

let rec abstract_term_over_types env sigma types trm =
  match types with
  | [] -> trm
  | h :: t ->
     let fresh_var = Name (Envutils.fresh_name env Anonymous) in
     mkLambda (fresh_var, h, abstract_term_over_types env sigma t trm)

let resp_from_typ c env sigma typ =
  let _ = Feedback.msg_warning (Pp.str "resp from typ 1") in
  let sigma, reduced_typ = Reducers.reduce_nf env sigma typ in
  let sigma, typ_list_o = types_from_simple_fun_type env sigma reduced_typ in
  let _ = Feedback.msg_warning (Pp.str "resp from typ 2") in
  if not (Option.has_some typ_list_o) then
    sigma, None
  else
    let (typ_list, out_type) = Option.get typ_list_o in
    let _ = Feedback.msg_warning (Pp.str "resp from typ 3") in
    let _ = List.map (fun x -> Feedback.msg_warning (Printer.pr_constr_env env sigma x)) (List.append typ_list [out_type]) in
    let sigma, resp = resp_from_typ_list c env sigma (List.append typ_list [out_type]) in
    let _ = Feedback.msg_warning (Pp.str "resp from typ 4") in
    let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma resp) in
    sigma, Some resp

let nparams_of_elim env elim =
  let maybe_ind = Indutils.inductive_of_elim env (Constr.destConst elim) in
  if Option.has_some maybe_ind then
    let ind = Option.get maybe_ind in
    Some (Inductive.inductive_params (Inductive.lookup_mind_specif env (ind, 0)))
  else
    None

let proper_goal_for_elim c env sigma elim out_typ =
  let _ = Feedback.msg_warning (Pp.str "proper proof for elim 01") in
  let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma elim) in
  let maybe_ind = Indutils.inductive_of_elim env (Constr.destConst elim) in
  let _ = Feedback.msg_warning (Pp.str "proper proof for elim 02") in
  if not (Option.has_some maybe_ind) then
    sigma, None
  else
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 03") in
    let ind = Option.get maybe_ind in
    let ind_typ = mkInd (ind, 0) in
    let nparams = Inductive.inductive_params (Inductive.lookup_mind_specif env (ind, 0)) in
    let _ = Feedback.msg_warning (Pp.int nparams) in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 04") in
    let param_rel_list = List.rev (List.init nparams (fun x -> mkRel (x + 1))) in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 04.5") in
    (* construct constant function to out_type *)
    let fresh_var = Name (Envutils.fresh_name env Anonymous) in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 05") in
    let const_fn = mkLambda (fresh_var, ind_typ, out_typ) in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 06") in
    (* apply elim to constant function *)
    let zoomed_env, zoomed_elim = Zooming.zoom_n_lambda env nparams elim in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 07") in
    let _ = Feedback.msg_warning (Printer.pr_constr_env zoomed_env sigma zoomed_elim) in
    let elim_motive_app = mkAppl (zoomed_elim, [const_fn]) in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 08") in
    let _ = Feedback.msg_warning (Printer.pr_constr_env zoomed_env sigma elim_motive_app) in
    let sigma, elim_motive_app_type = Inference.infer_type zoomed_env sigma elim_motive_app in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 09") in
    (* parse list to get ind hyps and base cases *)
    let sigma, o = types_from_simple_fun_type zoomed_env sigma elim_motive_app_type in
    let _ = Feedback.msg_warning (Pp.str "proper proof for elim 1") in
    if not (Option.has_some o) then
      sigma, None
    else
      let (typ_list, _) = Option.get o in
      if typ_list = [] then
        sigma, None
      else
        let hyp_list = List.rev (List.tl (List.rev typ_list)) in
        let _ = List.map (fun x -> Feedback.msg_warning (Printer.pr_constr_env zoomed_env sigma x)) hyp_list in
        let _ = Feedback.msg_warning (Pp.int (List.length hyp_list)) in
        let sort_hyps (sigma, (base, inds)) typ =
          let sigma, test = Convertibility.convertible zoomed_env sigma typ out_typ in
          if test then
            sigma, (typ :: base, inds)
          else
            sigma, (base, typ :: inds) in
        let sigma, (base_list, ind_list) =
          List.fold_left sort_hyps (sigma, ([],[])) hyp_list in
        let sigma, ind_proper_goals =
          Stateutils.map_state
            (fun typ sigma ->
              let sigma, resp_o = resp_from_typ c zoomed_env sigma typ in
              sigma, Option.map (fun x -> mkAppl (proper, [typ ; x ; mkRel 1])) resp_o)
            ind_list
            sigma in
        let _ = List.map (fun x -> Feedback.msg_warning (Printer.pr_constr_env zoomed_env sigma x)) ind_list in
        let _ = Feedback.msg_warning (Pp.int (List.length ind_list)) in
        let zzz = Option.get (List.hd ind_proper_goals) in
        let _ = Feedback.msg_warning (Printer.pr_constr_env zoomed_env sigma zzz) in
        (* construct function type from proofs ind hyps are proper to that base cases are proper *)
        let num_base_cases = List.length base_list in
        let num_ind_cases = List.length ind_list in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 2") in
        let sigma, elim_args =
          (* Construct a list of DeBruijn indices for the final goal.
             The order of the indices to the final function is:
             - the type being eliminated
             - each inductive hypothesis, followed by a proof that hypothesis is proper
             - (inside Proper) each base case
           *)
          let rec elim_args_help sigma num_base_seen num_ind_seen l1 l2 =
            match l1 with
            | [] -> sigma, l2
            | h :: t ->
               let _ = Feedback.msg_warning (Pp.str "elim_args_help call") in
               let sigma, eq = Convertibility.convertible zoomed_env sigma h out_typ in
               if eq then
                 (* this is a base case *)
                 let _ = Feedback.msg_warning (Pp.str "elim_args_help base case") in
                 let num_of_var = num_base_cases - num_base_seen in
                 elim_args_help sigma (num_base_seen + 1) num_ind_seen t ((mkRel num_of_var) :: l2)
               else
                 (* this is an inductive case *)
                 let _ = Feedback.msg_warning (Pp.str "elim_args_help ind case") in
                 let num_of_var = num_base_cases + 2 * (num_ind_cases - num_ind_seen) in
                 elim_args_help sigma num_base_seen (num_ind_seen + 1) t ((mkRel num_of_var) :: l2) in
          let sigma, l = elim_args_help sigma 0 0 hyp_list [] in
          sigma, List.rev ((mkRel (num_base_cases + 2 * num_ind_cases + 1)) :: l) in
        let _ = List.map (fun x -> Feedback.msg_warning (Printer.pr_constr_env zoomed_env sigma x)) elim_args in
        let shifted_param_elim_args =
          List.map (Debruijn.shift_by_unconditional (num_base_cases + 2*num_ind_cases)) param_rel_list in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3") in
        let elim_args = List.append shifted_param_elim_args (const_fn :: elim_args) in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.1") in
        let applied_elim = mkAppl (elim, elim_args) in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.2") in
        let abstracted_elim =
          abstract_term_over_types zoomed_env sigma base_list applied_elim in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.3") in
        let base_list_and_out_type = List.append base_list [out_typ] in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.4") in
        let type_of_abstracted_elim =
          fun_type_from_type_list zoomed_env base_list_and_out_type in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.5") in
        let sigma, unabstracted_proper_goal =
          (proper_from_type_list c zoomed_env sigma base_list_and_out_type
             type_of_abstracted_elim abstracted_elim) in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.6") in
        let inds_with_proper_goals =
          List.fold_left2
            (fun acc a b ->
              if (Option.has_some b && Option.has_some acc) then
                Some (a :: (Option.get b) :: (Option.get acc))
              else
                None)   
            (Some [])
            ind_list
            ind_proper_goals in
        let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.7") in
        if not (Option.has_some unabstracted_proper_goal
                || Option.has_some inds_with_proper_goals) then
          sigma, None
        else
          let ind_typ_app =
            if nparams > 0 then
              mkAppl (ind_typ, param_rel_list)
            else
              ind_typ in
          let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.8") in
          let _ = Feedback.msg_warning (Pp.bool (Option.has_some inds_with_proper_goals)) in
          let _ = Feedback.msg_warning (Pp.bool (Option.has_some unabstracted_proper_goal)) in
          let final_goal_types =
            List.append
              (ind_typ_app :: (Option.get inds_with_proper_goals))
              ([Option.get unabstracted_proper_goal]) in
          let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.9") in
          let proper_goal = Zooming.reconstruct_product_n env (fun_type_from_type_list zoomed_env final_goal_types) (Environ.nb_rel env - nparams) in
          let _ = Feedback.msg_warning (Pp.str "proper proof for elim 3.10") in
          let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma proper_goal) in
          let _ = Feedback.msg_warning (Pp.str "proper proof for elim 4") in
          sigma, Some proper_goal

let generate_proper_goal_from_def c env sigma def =
  let trmref = Globnames.destConstRef def in
  let const = mkConst trmref in
  generate_proper_goal_from_trm c env sigma const

(* Given a proof, run intro and return the updated proof and the name.
   Undefined if intro isn't possible.
 *)
let intro_in_proof proof env =
  let (current_goal_list, _, _, _, sigma) = Proof.proof proof in
  let current_goal = List.hd current_goal_list in
  let proof_env = Goal.V82.env sigma current_goal in
  let name = Envutils.fresh_name proof_env Anonymous in
  let _ = Feedback.msg_warning (Pp.str "pre intro using") in
  let (proof, pvm) = Proof.run_tactic env (Tactics.intro_using name) proof in
  (proof, pvm), name

let intro_in_proof_n_times env proof pvm n =
  let rec intro_in_proof_n_times_help env proof pvm n l =
    if n <= 0 then
      (proof, pvm), l
    else
      let (proof, pvm), name = intro_in_proof proof env in
      intro_in_proof_n_times_help env proof pvm (n - 1) (name :: l) in
  intro_in_proof_n_times_help env proof pvm n []

(* Given a proof with focused goal being an application of respectful,
   intro the two elements of the type and the proof of equivalence, 
   and return the proof, the proofview monad tree, and the names of 
   the introed terms.
 *)
let intro_respectful proof env =
  let _ = Feedback.msg_warning (Pp.str "intro 1") in
  let (proof, _), name1 = intro_in_proof proof env in
  let _ = Feedback.msg_warning (Pp.str "intro 2") in
  let (proof, _), name2 = intro_in_proof proof env in
  let _ = Feedback.msg_warning (Pp.str "intro 3") in
  let (proof, pvm), eqName = intro_in_proof proof env in
  let _ = Feedback.msg_warning (Pp.str "intro done") in
  (proof, pvm), (name1, name2, eqName)

let goal_constr_from_proof proof =
  let (current_goal_list, _, _, _, sigma) = Proof.proof proof in
  let current_goal = List.hd current_goal_list in
  let proof_env = Goal.V82.env sigma current_goal in
  proof_env, sigma, EConstr.to_constr sigma (Goal.V82.concl sigma current_goal)

let goal_econstr_from_proof proof =
  let (current_goal_list, _, _, _, sigma) = Proof.proof proof in
  let current_goal = List.hd current_goal_list in
  let proof_env = Goal.V82.env sigma current_goal in
  proof_env, sigma, (Goal.V82.concl sigma current_goal)

let try_tactical t =
  Proofview.tclOR t (fun _ -> Proofview.tclUNIT ())

let unfold_first_respectful proof env =
  Proof.run_tactic
    env
     (Tactics.unfold_in_concl [(Locus.OnlyOccurrences [1]), respectful_evaluable_glob_ref])
    proof

let intro_all_respectfuls proof pvm env =
  let rec help proof pvm env l =
    let (proof_env, sigma, goal_concl) = goal_constr_from_proof proof in
    if not (isApp goal_concl) then
      (proof, pvm), l
    else
      let _ = Feedback.msg_warning (Printer.pr_constr_env proof_env sigma (Apputils.first_fun goal_concl)) in
      if equal (Apputils.first_fun goal_concl) respectful then
        let _ = Feedback.msg_warning (Pp.str "respectful") in
        let (proof, pvm) = unfold_first_respectful proof env in
        let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
        let (proof, pvm), (name1, name2, eqName) = intro_respectful proof env in
        let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
        help proof pvm env ((name1, name2, eqName) :: l)
      else
        (proof, pvm), l in
  let _ = Feedback.msg_warning (Pp.str "introing respectfuls") in
  help proof pvm env []

let unfold_proper proof env =
  Proof.run_tactic env (Tactics.unfold_constr proper_glob_ref) proof

let rewrite_tactic_from_id id =
  let s = Pp.str ("rewrite " ^ (Names.Id.to_string id)) in
  let s' = Format.asprintf "%a" Pp.pp_with s in
  Decompiler.parse_tac_str s'

let rewrite_equalities env proof pvm l =
  let rec help proof pvm l1 l2 =
    match l1 with
    | [] -> (proof, pvm), l2
    | (n1, n2, h) :: t -> 
       let (current_goal_list, _, _, _, sigma) = Proof.proof proof in
       let current_goal = List.hd current_goal_list in
       let proof_env = Goal.V82.env sigma current_goal in
       let trm = mkVar h in
       let sigma', typ = Inference.infer_type proof_env sigma trm in
       let f = Apputils.first_fun typ in
       if (equal Equtils.eq f) && (List.length (unfold_args typ) = 3) then
         let (proof, pvm) = Proof.run_tactic env (rewrite_tactic_from_id h) proof in
         let (proof, pvm) = Proof.run_tactic env (Tactics.clear [h; n1]) proof in
         help proof pvm t l2
       else
         help proof pvm t ((n1, n2, h) :: l2) in
  help proof pvm l []

let setoid_rewrite_tactic_from_id id =
  let s = Pp.str ("setoid_rewrite " ^ (Names.Id.to_string id)) in
  let s' = Format.asprintf "%a" Pp.pp_with s in
  Decompiler.parse_tac_str s'

let rec try_setoid_rewrite_equalities env proof pvm l =
  match l with
  | [] -> (proof, pvm)
  | (n1, n2, h) :: t -> 
      let (proof, pvm) = Proof.run_tactic env (try_tactical (setoid_rewrite_tactic_from_id h)) proof in
      let (proof, pvm) = Proof.run_tactic env (Tactics.clear [h; n1]) proof in
      try_setoid_rewrite_equalities env proof pvm t

let prove_proper_for_elim c env sigma elim out_typ =
  let sigma, goal_o = proper_goal_for_elim c env sigma elim out_typ in
  let _ = Feedback.msg_warning (Pp.bool (Option.has_some goal_o)) in
  let _ = Feedback.msg_warning (Pp.str "prove_proper_for_elim 1") in
  let nparams_o = nparams_of_elim env elim in
  let _ = Feedback.msg_warning (Pp.bool (Option.has_some nparams_o)) in
  let _ = Feedback.msg_warning (Pp.str "prove_proper_for_elim 2") in
  if not ((Option.has_some goal_o) && (Option.has_some nparams_o)) then
    sigma, None
  else
    let _ = Feedback.msg_warning (Pp.str "prove_proper_for_elim 2.5") in
    let goal = Option.get goal_o in
    let nparams = Option.get nparams_o in
    let proof = Proof.start sigma [(env, EConstr.of_constr goal)] in
    let _ = Feedback.msg_warning (Pp.str "prove_proper_for_elim 3") in
    let (proof, pvm) = Proof.run_tactic env (Proofview.tclUNIT ()) proof in
    let _ = Feedback.msg_warning (Pp.str "prove_proper_for_elim 4") in
    let (proof, pvm), _ = intro_in_proof_n_times env proof pvm nparams in
    let _ = Feedback.msg_warning (Pp.str "prove_proper_for_elim 5") in
    let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
    let (proof, pvm) = Proof.run_tactic env (solve_elim_proper_tac ()) proof in
    let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
    if (Proof.is_done proof) then
      match Proof.partial_proof proof with
      | [] -> Proof.return proof, None
      | h :: t -> Proof.return proof, Some h
    else
      sigma, None

let num_focused_goals proof =
  let (goals, _, _, _, _) = Proof.proof proof in
  List.length goals

let letin_tac id trm =
  Tactics.letin_tac None (Names.Name.Name id) trm None Locusops.nowhere

let pose_tac proof trm =
  let (proof_env, proof_sigma, concl) = goal_constr_from_proof proof in
  let letin_id = Envutils.fresh_name proof_env Anonymous in
  letin_id, letin_tac letin_id trm

let solve_current_proper_subgoal c env sigma proof pvm eqs_to_rewrite =
  let focus_kind = Proof.new_focus_kind () in
  let focus_cond = Proof.done_cond focus_kind in
  let proof = Proof.focus focus_cond () 1 proof in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 1") in
  (*let (proof_env, proof_sigma, current_goal) = goal_econstr_from_proof proof in*)
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 2") in
  (*let proof_subgoal = Proof.start sigma [(proof_env, current_goal)] in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof_subgoal) in*)
  (*let proof_subgoal =
    (try Control.timeout 10 (fun x -> fst (Proof.run_tactic env (solve_proper_tac ()) x)) proof (Failure "Timeout")
     with e -> Feedback.msg_warning (Pp.str "Timeout"); proof_subgoal) in*)
  let (proof, pvm) = unfold_proper proof env in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm), eqs_to_rewrite_2 = intro_all_respectfuls proof pvm env in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm) = try_setoid_rewrite_equalities env proof pvm (List.append eqs_to_rewrite_2 eqs_to_rewrite) in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm) = Proof.run_tactic env Tactics.reflexivity proof in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  (*let _, result =
    if (Proof.is_done proof) then
      match Proof.partial_proof proof with
      | [] -> Proof.return proof_subgoal, None
      | h :: t -> Proof.return proof_subgoal, Some h
    else
      raise (Failure "Failed to solve subgoal") in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 3") in
  let id, tac = pose_tac proof (Option.get result) in
  let (proof, pvm) = Proof.run_tactic env tac proof in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 4") in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm) = Proof.run_tactic env (try_tactical Tactics.assumption) proof in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 5") in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in*)
  let proof = Proof.unfocus focus_kind proof () in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 6") in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  (proof, pvm)
  (*let resp_glob_ref =
  Names.GlobRef.ConstRef (Constant.make2 coq_classes_morphisms (Label.make "respectful")) in
  let (proof, pvm) = unfold_proper proof env in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  (*unfold_constr resp_glob_ref runs, but unfold_first_respectful doesn't; why? looks like it has to be the locus?*)
  let (proof, pvm) = Proof.run_tactic
    env
     (Tactics.unfold_in_concl [(Locus.OnlyOccurrences [1]), respectful_evaluable_glob_ref])
     proof in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm) = Proof.run_tactic env (Tactics.unfold_constr resp_glob_ref) proof in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 3") in
  let (proof, pvm), eq_rel_proofs = intro_all_respectfuls proof pvm env in
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let new_num_goals = num_focused_goals proof in
  let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 4") in
  if num_goals != new_num_goals then
    (proof, pvm)
  else
    let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 5") in
    let (proof, pvm) = try_setoid_rewrite_equalities env proof pvm eqs_to_rewrite in
    let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 6") in
    let (proof, pvm) = Proof.run_tactic env Tactics.reflexivity proof in
    let _ = Feedback.msg_warning (Pp.str "solve_current_proper_subgoal 7") in
    (proof, pvm)*)
    
    
let solve_proper_goal c env sigma goal def =
  let proof = Proof.start sigma [(env, EConstr.of_constr goal)] in
  let (proof, pvm) = Proof.run_tactic env (Tactics.unfold_constr def) proof in
  Feedback.msg_warning (Pp.str "c");
  let (proof, pvm) = Proof.run_tactic env Tactics.intros proof in
  Feedback.msg_warning (Pp.str "d");
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm) =
    (try Control.timeout 10 (Proof.run_tactic env (solve_proper_tac ())) proof (Failure "Timeout")
     with e -> Feedback.msg_warning (Pp.str "Timeout"); (proof, pvm)) in
  Feedback.msg_warning (Pp.str "e");
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  if (Proof.is_done proof) then
    match Proof.partial_proof proof with
    | [] -> Proof.return proof, None
    | h :: t -> Proof.return proof, Some (EConstr.to_constr sigma h)
  else
    let (current_goal_list, _, _, _, proof_sigma) = Proof.proof proof in
    Feedback.msg_warning (Pp.str "match on proof");
    if current_goal_list = [] then
      sigma, None
    else
      let current_goal = List.hd current_goal_list in
      Feedback.msg_warning (Pp.str "get current goal");
      Feedback.msg_warning (Goal.pr_goal current_goal);
      let (current_goal, proof_sigma) = Goal.V82.nf_evar proof_sigma current_goal in
      let goal_concl = Goal.V82.concl proof_sigma current_goal in
      Feedback.msg_warning (Pp.str "get goal conclusion");
      let proof_env = Goal.V82.env proof_sigma current_goal in
      Feedback.msg_warning (Pp.str "get goal env");
      let _ = Feedback.msg_warning (Printer.pr_constr_env proof_env proof_sigma (EConstr.to_constr proof_sigma goal_concl)) in
      let proof_env, proof_sigma, goal_constr = goal_constr_from_proof proof in
      if Constr.isApp goal_constr then (
        let _ = Feedback.msg_warning (Pp.str "goal is an app") in
        let f = Apputils.first_fun goal_constr in
        if equal f proper then 
          let (proof, pvm) = unfold_proper proof env in
          let (proof, pvm), eq_rel_proofs = intro_all_respectfuls proof pvm env in
          let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
          let (proof, pvm), eq_rel_proofs = rewrite_equalities env proof pvm eq_rel_proofs in
          let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
          let (proof_env, proof_sigma, concl) = goal_constr_from_proof proof in
          let compared_term = Apputils.last_arg concl in
          if Constr.isApp compared_term then
            let _ = Feedback.msg_warning (Pp.str "last term is an app") in
            let (trm, _) = Constr.destApp compared_term in
            Feedback.msg_warning (Pp.str "dest app last term");
            (*get out type from equiv rel not from inference*)
            let eq_rel = Apputils.first_fun concl in
            let proof_sigma, eq_rel_type = Inference.infer_type proof_env proof_sigma eq_rel in
            let proof_sigma, o = types_from_simple_fun_type proof_env proof_sigma eq_rel_type in
            if Option.has_some o then
              let (eq_rel_type_list, _) = Option.get o in
              let out_type = List.hd (List.rev eq_rel_type_list) in
              let _ = Feedback.msg_warning (Printer.pr_constr_env proof_env proof_sigma out_type) in
              Feedback.msg_warning (Pp.str "proper_proof_for_elim call");
              let sigma, o = prove_proper_for_elim c env sigma trm out_type in
              if Option.has_some o then
                let elim_proper_proof = Option.get o in
                let (proof_env, proof_sigma, concl) = goal_constr_from_proof proof in
                let _ = Feedback.msg_warning (Pp.str "run let in") in
                let letin_id = Envutils.fresh_name proof_env Anonymous in
                let (proof, pvm) = Proof.run_tactic env (letin_tac letin_id elim_proper_proof) proof in
                let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
                let _ = Feedback.msg_warning (Pp.str "run apply") in
                let (proof, pvm) = Proof.run_tactic env (Tactics.apply (EConstr.mkVar letin_id)) proof in
                let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
                let rec solve_subgoals proof pvm =
                  let num_goals = num_focused_goals proof in
                  let (proof, pvm) = solve_current_proper_subgoal c env sigma proof pvm eq_rel_proofs in
                  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
                  let new_num_goals = num_focused_goals proof in
                  if new_num_goals < num_goals && 0 < new_num_goals then
                    solve_subgoals proof pvm
                  else
                    (proof, pvm) in
                let (proof, pvm) = solve_subgoals proof pvm in
                if (Proof.is_done proof) then
                  match Proof.partial_proof proof with
                  | [] -> Proof.return proof, None
                  | h :: t -> Proof.return proof, Some (EConstr.to_constr sigma h)
                else
                  sigma, None
              else  
                sigma, None
            else
              sigma, None
          else
            sigma, None
        else
          sigma, None)
      else
        sigma, None                  

let generate_proper_proof l env sigma n def =
  if (not Sys.unix) then
    sigma, None
  else
    let sigma, goal = generate_proper_goal_from_def l env sigma def in
    Feedback.msg_warning (Pp.str "a");
    match goal with
    | None -> sigma, None
    | Some g -> (
        let sigma, generated_proof = solve_proper_goal l env sigma g def in
        let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma g) in
        Feedback.msg_warning (Pp.str "b");
        match generated_proof with
        | None -> Feedback.msg_warning (Pp.str "Failed to generate a proof that the lifted function is a proper morphism. You should prove this manually if necessary.");
                  sigma, None
        | Some proof ->
           (let n_new = Nameutils.with_suffix n "proper" in
            let def = Defutils.define_term n_new sigma proof true in
            let proper_ref = Names.GlobRef.ConstRef (fst (destConst proper)) in
            let proper_class = Typeclasses.class_info proper_ref in
            let proper_instance = Typeclasses.new_instance
                                    proper_class Hints.empty_hint_info true def in
            Typeclasses.add_instance proper_instance;
            sigma, Some def))
