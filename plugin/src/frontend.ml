open Constr
open Names
open Globnames
open Lifting
open Caching
open Search
open Lift
open Unpack
open Utilities
open Pp
open Printer
open Printing
open Coherence
open Equivalence
open Options
open Typehofs
open Constutils
open Nameutils
open Defutils
open Modutils
open Envutils
open Stateutils
open Environ
open Inference
open Ornerrors
open Pretype_errors
open Promotion
open Deltautils

(* --- Utilities --- *)

(*
 * Refresh an environment and get the corresponding state after defining
 * a term
 *)
let refresh_env () : env state =
  let env = Global.env () in
  Evd.from_env env, env

let define_print ?typ n trm sigma =
  let def = define_term ?typ n sigma trm true in
  Feedback.msg_info
    (str (Printf.sprintf "DEVOID generated %s" (Id.to_string n)));
  def
                      
(* --- Commands --- *)

(*
 * If the option is enabled, then prove coherence after find_ornament is called.
 * Otherwise, do nothing.
 *)
let maybe_prove_coherence n inv_n kind : unit =
  match kind with
  | Algebraic _ ->
     if is_search_coh () then
       let sigma, env = refresh_env () in
       let (promote, forget) = map_tuple make_constant (n, inv_n) in
       let orn = { promote; forget; kind } in
       let coh, coh_typ = prove_coherence env sigma orn in
       let coh_n = with_suffix n "coh" in
       ignore (define_print ~typ:coh_typ coh_n coh sigma)
     else
       ()
  | _ ->
     ()

(*
 * If the option is enabled, then prove section, retraction, and adjunction after
 * find_ornament is called. Otherwise, do nothing.
 *)
let maybe_prove_equivalence n inv_n : unit =
  let define_proof suffix ?(adjective=suffix) sigma term =
    let ident = with_suffix n suffix in
    define_print ident term sigma |> destConstRef
  in
  if is_search_equiv () then
    let sigma, env = refresh_env () in
    let (promote, forget) = map_tuple make_constant (n, inv_n) in
    let l = initialize_lifting env sigma promote forget in
    let (section, retraction) = prove_equivalence env sigma l in
    let sect = define_proof "section" sigma section in
    let retr0 = define_proof "retraction" sigma retraction in
    let pre_adj = { orn = l; sect; retr0 } in
    let _ =
      let sigma, env = refresh_env () in
      let (sigma, retraction_adj) = adjointify_retraction env pre_adj sigma in
      define_proof "retraction_adjoint" sigma retraction_adj ~adjective:"adjoint retraction"
    in
    let _ =
      let sigma, env = refresh_env () in
      let (sigma, adjunction) = prove_adjunction env pre_adj sigma in
      define_proof "adjunction" sigma adjunction
    in ()
  else
    ()

(*
 * Identify an ornament between two types
 * Define the components of the corresponding equivalence
 * If the appropriate option is set, prove these components form an equivalence
 *)
let find_ornament n_o d_old d_new =
  try
    let (sigma, env) = Pfedit.get_current_context () in
    let sigma, def_o = intern env sigma d_old in
    let sigma, def_n = intern env sigma d_new in
    let trm_o, trm_n = map_tuple (try_delta_inductive env) (def_o, def_n) in
    let n, idx_n =
      match map_tuple kind (trm_o, trm_n) with
      | Ind ((m_o, _), _), Ind ((m_n, _), _) ->
         (* Algebraic ornament *)
         let (_, _, lab_o) = KerName.repr (MutInd.canonical m_o) in
         let (_, _, lab_n) = KerName.repr (MutInd.canonical m_n) in
         let name_o = Label.to_id lab_o in
         let name_n = Label.to_string lab_n in
         let auto_n = with_suffix (with_suffix name_o "to") name_n in
         let n = Option.default auto_n n_o in
         let idx_n = with_suffix n "index" in
         n, Some idx_n
      |_ ->
        if isInd trm_o || isInd trm_n then
          (* Curry record *)
          let ind = if isInd trm_o then trm_o else trm_n in
          let ((m, _), _) = destInd ind in
          let (_, _, lab) = KerName.repr (MutInd.canonical m) in
          let name = Label.to_id lab in
          let auto_n = with_suffix name "curry" in
          let n = Option.default auto_n n_o in
          n, None
        else      
          user_err
            "find_ornament"
            err_unsupported_change
            [try_supported; try_provide]
            [cool_feature; mistake]
    in
    let sigma, orn = search_orn env sigma idx_n trm_o trm_n in
    let orn =
      match orn.kind with
      | Algebraic (indexer, off) ->
         (* Substitute the defined indexer constant for the raw term *)
         let indexer = define_print (Option.get idx_n) indexer sigma in
         { orn with kind = Algebraic (Universes.constr_of_global indexer, off) }
      | _ ->
         orn
    in
    let promote = define_print n orn.promote sigma in
    let inv_n = with_suffix n "inv" in
    let forget = define_print inv_n orn.forget sigma in
    maybe_prove_coherence n inv_n orn.kind;
    maybe_prove_equivalence n inv_n;
    (try
       let promote, forget = map_tuple Universes.constr_of_global (promote, forget) in
       save_ornament (trm_o, trm_n) (promote, forget, orn.kind)
     with _ ->
       Feedback.msg_warning err_save_ornament);
  with
  | PretypeError (env, sigma, err) ->
    user_err
      "find_ornament"
      (err_type env sigma err)
      [try_supported; try_provide]
      [problematic]
  | NotAlgebraic ->
     user_err
       "find_ornament"
       (err_unexpected_change "algebraic ornament")
       [try_supported; try_provide]
       [problematic]

(*
 * Save a user-provided ornament
 *)
let save_ornament d_old d_new d_orn d_orn_inv =
  Feedback.msg_warning (Pp.str "Custom equivalences are experimental. Use at your own risk!");
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, promote = intern env sigma d_orn in
  let sigma, forget = intern env sigma d_orn_inv in
  let sigma, def_o = intern env sigma d_old in
  let sigma, def_n = intern env sigma d_new in
  let trm_o, trm_n = map_tuple (try_delta_inductive env) (def_o, def_n) in
  try
    let l = initialize_lifting env sigma promote forget in
    save_ornament (trm_o, trm_n) (promote, forget, l.orn.kind)
  with _ ->
    user_err
      "save_ornament"
      err_save_ornament
      [try_supported; try_provide]
      [problematic]

(*
 * Lift a definition according to a lifting configuration, defining the lifted
 * definition and declaring it as a lifting of the original definition.
 *)
let lift_definition_by_ornament env sigma n l c_old ignores =
  let sigma, lifted = do_lift_defn env sigma l c_old ignores in
  try
    ignore
      (if is_lift_type () then
         (* Lift the type as well *)
         let sigma, typ = infer_type env sigma c_old in
         let sigma, lifted_typ = do_lift_defn env sigma l typ ignores in
         define_print ~typ:lifted_typ n lifted sigma 
       else
         (* Let Coq infer the type *)
         define_print n lifted sigma);
    try
      let c_new = mkConst (Constant.make1 (Lib.make_kn n)) in
      save_lifting (lift_to l, lift_back l, c_old) c_new;
      save_lifting (lift_back l, lift_to l, c_new) c_old
    with _ ->
      Feedback.msg_warning (Pp.str "Failed to cache lifting.")
  with
  | PretypeError (env, sigma, err) ->
     user_err
       "lift_definition_by_ornament"
       (err_type env sigma err)
       [try_supported]
       [problematic]
  | NotAlgebraic ->
     user_err
       "lift_definition_by_ornament"
       (err_unexpected_change "algebraic ornament")
       [try_supported]
       [problematic]

(*
 * Lift an inductive type according to a lifting configuration, defining the
 * new lifted version and declaring type-to-type, constructor-to-constructor,
 * and eliminator-to-eliminator liftings.
 *)
let lift_inductive_by_ornament env sigma n s l c_old ignores =
  try
    let ind, _ = destInd c_old in
    let ind' = do_lift_ind env sigma l n s ind ignores in
    let env' = Global.env () in
    Feedback.msg_info (str "DEVOID generated " ++ pr_inductive env' ind')
  with
  | PretypeError (env, sigma, err) ->
     user_err
       "lift_inductive_by_ornament"
       (err_type env sigma err)
       [try_supported]
       [problematic]
  | NotAlgebraic ->
     user_err
       "lift_inductive_by_ornament"
       (err_unexpected_change "algebraic ornament")
       [try_supported]
       [problematic]

(*
 * Common configuration for several commands
 *)
let init_lift env d_orn d_orn_inv sigma =
  let sigma, c_orn = intern env sigma d_orn in
  let sigma, c_orn_inv = intern env sigma d_orn_inv in
  let (o, n) = map_tuple (try_delta_inductive env) (c_orn, c_orn_inv) in
  let sigma, env =
    let orn_opt = lookup_ornament (o, n) in
    if not (Option.has_some orn_opt) then
      (* The user never ran Find ornament *)
      let _ = Feedback.msg_info (str "Searching for ornament first") in
      let _ = find_ornament None d_orn d_orn_inv in
      refresh_env ()
    else
      (* The ornament is cached *)
      sigma, env
  in
  let l = initialize_lifting env sigma o n in
  sigma, (env, l)

(*
 * Lift the supplied definition or inductive type along the supplied ornament
 * Define the lifted version
 *)
let lift_by_ornament ?(suffix=false) ?(opaques=[]) n d_orn d_orn_inv d_old =
  let (sigma, env) = Pfedit.get_current_context () in
  let opaque_terms =
    List.map
      (fun r ->
        match Nametab.locate (qualid_of_reference r) with
        | VarRef v ->
           mkVar v
        | ConstRef c ->
           mkConst c
        | IndRef ind ->
           mkInd ind
        | ConstructRef c ->
           mkConstruct c)
      opaques
  in
  let sigma, c_old = intern env sigma d_old in
  let n_new = if suffix then suffix_term_name c_old n else n in
  let s = if suffix then Id.to_string n else "_" ^ Id.to_string n in
  let sigma, (env, l) = init_lift env d_orn d_orn_inv sigma in 
  let u_old = unwrap_definition env c_old in
  if isInd u_old then
    let from_typ = fst (on_red_type_default (fun _ _ -> promotion_type_to_types) env sigma l.orn.promote) in
    if not (equal u_old from_typ) then
      lift_inductive_by_ornament env sigma n_new s l c_old opaque_terms
    else
      lift_definition_by_ornament env sigma n_new l c_old opaque_terms
  else
    lift_definition_by_ornament env sigma n_new l c_old opaque_terms

(*
  * Lift each module element (constant and inductive definitions) along the given
  * ornament, defining a new module with all the transformed module elements.
  *)
let lift_module_by_ornament ?(opaques=[]) ident d_orn d_orn_inv mod_ref =
  let mod_body =
    qualid_of_reference mod_ref |> Nametab.locate_module |> Global.lookup_module
  in
  let lift_global gref =
    let ident = Nametab.basename_of_global gref in
    try
      lift_by_ornament ~opaques:opaques ident d_orn d_orn_inv (expr_of_global gref)
    with _ ->
      Feedback.msg_warning (str "Failed to lift " ++ pr_global_as_constr gref)
  in
  let _ =
    declare_module_structure
      ident
      (fun _ -> iter_module_structure_by_glob lift_global mod_body)
  in
  Feedback.msg_info (str "Defined lifted module " ++ Id.print ident)

(*
 * Add terms to the globally opaque lifting cache at a particular ornament
 *)
let add_lifting_opaques d_orn d_orn_inv opaques =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, (env, l) = init_lift env d_orn d_orn_inv sigma in
  List.iter
    (fun r ->
      let qid = qualid_of_reference r in
      Feedback.msg_info
        (Pp.seq [Pp.str "Adding opaque lifting "; Libnames.pr_qualid qid]);
      try
        let c = mkConst (Nametab.locate_constant qid) in
        save_opaque (lift_to l, lift_back l, c);
        save_opaque (lift_back l, lift_to l, c)
      with Not_found ->
        user_err
          "add_lifting_opaques"
          (err_opaque_not_constant qid)
          [try_check_typos; try_fully_qualify]
          [problematic; mistake])
    opaques

(*
 * Remove terms from the globally opaque lifting cache at a particular ornament
 *)
let remove_lifting_opaques d_orn d_orn_inv opaques =
  let (sigma, env) = Pfedit.get_current_context () in
  let sigma, (env, l) = init_lift env d_orn d_orn_inv sigma in
  List.iter
    (fun r ->
      let qid = qualid_of_reference r in
      Feedback.msg_info
        (Pp.seq [Pp.str "Removing opaque lifting "; Libnames.pr_qualid qid]);
      try
        let c = mkConst (Nametab.locate_constant qid) in
        remove_opaque (lift_to l, lift_back l, c);
        remove_opaque (lift_back l, lift_to l, c)
      with Not_found ->
        user_err
          "remove_lifting_opaques"
          (err_opaque_not_constant qid)
          [try_check_typos; try_fully_qualify]
          [problematic; mistake])
    opaques

(*
 * Unpack sigma types in the functional signature of a constant.
 *
 * This transformation assumes that the input constant was generated by
 * ornamental lifting.
 *)
let do_unpack_constant ident const_ref =
  let env = Global.env () in
  let sigma = ref (Evd.from_env env) in
  let term =
    qualid_of_reference const_ref |> Nametab.locate_constant |>
    unpack_constant env sigma
  in ignore (define_print ident term !sigma)
