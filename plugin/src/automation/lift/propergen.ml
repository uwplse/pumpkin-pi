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

let respectful =
  mkConst (Constant.make2 coq_classes_morphisms (Label.make "respectful"))

let proper =
  mkConst (Constant.make2 coq_classes_morphisms (Label.make "Proper"))

let solve_proper_tac = fun () ->
  Decompiler.parse_tac_str (Format.asprintf "%a" Pp.pp_with (Pp.str "solve_proper"))

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

let generate_proper_goal c env sigma def =
  let trmref = Globnames.destConstRef def in
  let const = mkConst trmref in
  let env, trm = Constutils.open_constant env trmref in
  let sigma, typ = Inference.infer_type env sigma trm in
  let sigma, reduced1 = Reducers.delta env sigma typ in
  let sigma, reduced2 = Reducers.whd env sigma typ in
  let sigma, reduced3 = Reducers.reduce_nf env sigma typ in
  let sigma, reduced4 = Reducers.reduce_term env sigma typ in
  let sigma, reduced5 = Reducers.reduce_unfold_whd env sigma typ in
  let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma reduced1) in
  let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma reduced2) in
  let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma reduced3) in
  let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma reduced4) in
  let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma reduced5) in
  let eq_rel_for_type sigma typ =
    let sigma, sort_family = Inference.infer_type env sigma typ in
      if is_Prop typ then
         sigma, iff
      else
         Lift.find_eq_rel_for_type c env sigma typ in
  Feedback.msg_warning (Pp.str "f");
  if not (is_simple_fun_type typ) then
    let _ = Feedback.msg_warning (Pp.str "i") in
    sigma, None
  else 
    let sigma, o = types_from_simple_fun_type env sigma typ in
    Feedback.msg_warning (Pp.str "g");
    match o with
    | None -> sigma, None
    | Some (typ_list, out_typ) ->
       let rec resp_from_typ_list c env sigma l =
         match l with
         | [] -> failwith "Undefined."
         | h :: [] -> eq_rel_for_type sigma h
         | h1 :: h2 :: t ->
            (let sigma, eq_rel = eq_rel_for_type sigma h1 in
             let sigma, tail = resp_from_typ_list c env sigma (h2 :: t) in
             let f = (fun_type_from_type_list env (h2 :: t)) in
             let x = mkAppl (respectful, [h1 ; f ; eq_rel ; tail]) in
             (sigma, x)) in
       let sigma, x = resp_from_typ_list c env sigma (List.append typ_list [out_typ]) in
       Feedback.msg_warning (Pp.str "h");
       Util.on_snd (fun x -> Some (mkAppl (proper, [typ ; x ; const]))) (sigma, x)
     

let solve_proper_goal env sigma goal def =
  let proof = Proof.start sigma [(env, EConstr.of_constr goal)] in
  let (proof, pvm) = Proof.run_tactic env (Tactics.unfold_constr def) proof in
  Feedback.msg_warning (Pp.str "c");
  let (proof, pvm) = Proof.run_tactic env Tactics.intros proof in
  Feedback.msg_warning (Pp.str "d");
  let _ = Feedback.msg_warning (Printer.pr_open_subgoals ~proof:proof) in
  let (proof, pvm) = Proof.run_tactic env (solve_proper_tac ()) proof in
  Feedback.msg_warning (Pp.str "e");
  if (Proof.is_done proof) then
    match Proof.partial_proof proof with
    | [] -> None
    | h :: t -> Some (EConstr.to_constr sigma h)
  else
    None

let generate_proper_proof l env sigma n def =
  if (not Sys.unix) then
    sigma, None
  else
    let sigma, goal = generate_proper_goal l env sigma def in
    Feedback.msg_warning (Pp.str "a");
    match goal with
    | None -> sigma, None
    | Some g -> (
        let generated_proof =
          (try Control.timeout 10 (solve_proper_goal env sigma g) def (Failure "Timeout")
          with e -> None) in
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
