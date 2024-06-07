(*
 * Functions for generating proofs that a term is Proper
 * when doing setoid repair.
 *)

open Constr
open Names
open Apputils

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

(*
 * If typ is a (possibly 0-ary) function type and is not a 
 * dependent type, return Some (l, o), where l is list of 
 * the input types with the first input type at the head 
 * and o is the output type. 
 * Otherwise, return None.
 *)
let rec types_from_simple_fun_type env sigma typ =
  if no_rels typ then
    let kind_typ = Constr.kind typ in
    match kind_typ with
    | Prod (n, t, b) ->
       (let sigma, o = types_from_simple_fun_type env sigma b in
       match o with
       | None -> sigma, None
       | Some (l, t2) -> sigma, Some (t :: l, t2))
    | _ -> sigma, Some ([], typ)
  else sigma, None

let rec fun_type_from_type_list env typ_list =
  let _ = Feedback.msg_warning (Pp.str "make fun type") in
  match typ_list with
  | [] -> (let _ = Feedback.msg_warning (Pp.str "fun type from type list base case") in failwith "Cannot construct a function type with no types.")
  | h :: [] -> h
  | h1 :: h2 :: t ->
     (let fresh_var = Name (Envutils.fresh_name env Anonymous) in
     mkProd (fresh_var, h1, fun_type_from_type_list env (h2 :: t)))

let generate_proper_goal c env sigma trm =
  let sigma, typ = Inference.infer_type env sigma trm in
  Feedback.msg_warning (Pp.str "infer type");
  let sigma, o = types_from_simple_fun_type env sigma typ in
  Feedback.msg_warning (Pp.str "decompose type");
  match o with
  | None -> sigma, None
  | Some (typ_list, out_typ) ->
     let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma out_typ) in
     let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma (snd (Lift.find_eq_rel_for_type c env sigma out_typ))) in
     let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma (List.hd typ_list)) in
     let rec resp_from_typ_list c env sigma l =
       match l with
       | [] -> failwith "Undefined."
       | h :: [] -> Lift.find_eq_rel_for_type c env sigma h
       | h1 :: h2 :: t ->
          (let sigma, eq_rel = Lift.find_eq_rel_for_type c env sigma h1 in
           let _ = Feedback.msg_warning (Pp.str "eq rel h") in
           let sigma, tail = resp_from_typ_list c env sigma (h2 :: t) in
           let _ = Feedback.msg_warning (Pp.str "recurse") in
           let f = (fun_type_from_type_list env (h2 :: t)) in
           let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma f) in
           let x = mkAppl (respectful, [h1 ; f ; eq_rel ; tail]) in
           let _ = Feedback.msg_warning (Pp.str "make app") in
           let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma x) in
           (sigma, x)) in
     let _ = Feedback.msg_warning (Pp.int (List.length typ_list)) in
     let sigma, x = resp_from_typ_list c env sigma (List.append typ_list [out_typ]) in
     let _ = Feedback.msg_warning (Pp.str "resp from type list") in
     Util.on_snd (fun x -> Some (mkAppl (proper, [typ ; x ; trm]))) (sigma, x)
     

let solve_proper_goal env sigma goal =
  let proof = Proof.start sigma [(env, EConstr.of_constr goal)] in
  let (proof, pvm) = Proof.run_tactic env (solve_proper_tac ()) proof in
  if (Proof.is_done proof) then
    match Proof.partial_proof proof with
    | [] -> failwith "No proof of proper found."
    | h :: t -> Some h
  else
    None

let generate_proper_proof l env sigma n trm =
  let sigma, goal = generate_proper_goal l env sigma trm in
  Feedback.msg_info (Pp.str "generated");
  match goal with
  | None -> failwith "Could not generate a Proper goal to prove."
  | Some g ->
     (let _ = Feedback.msg_warning (Printer.pr_constr_env env sigma g) in
      let generated_proof = solve_proper_goal env sigma g in
      Feedback.msg_info (Pp.str "solved");
      match generated_proof with
      | None -> failwith "handle this better"
      | Some proof ->
         (let n_new = Nameutils.with_suffix n "proper" in
          let def = Defutils.define_term n_new sigma trm true in
          let proper_ref = Names.GlobRef.ConstRef (fst (destConst proper)) in
          let proper_class = Typeclasses.class_info proper_ref in
          let proper_instance = Typeclasses.new_instance
                                  proper_class Hints.empty_hint_info true def in
          Typeclasses.add_instance proper_instance;
          sigma, def))
