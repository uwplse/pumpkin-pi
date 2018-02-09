DECLARE PLUGIN "ornamental"

open Term
open Names
open Environ
open Constrarg
open Format
open Univ
open Printer
open Declarations
open Command

module CRD = Context.Rel.Declaration

(* --- Auxiliary functions, mostly from PUMPKIN PATCH --- *)

(* Take n elements of a list *)
let rec take (i : int) (l : 'a list) : 'a list =
  if i = 0 then
    []
  else
    match l with
    | [] ->
       []
    | h :: tl ->
       h :: (take (i - 1) tl)

(* Take all but n elements of a list *)
let take_except (i : int) (l : 'a list) : 'a list =
  take (List.length l - i) l

(* Map f over a tuple *)
let map_tuple (f : 'a -> 'b) ((a1, a2) : ('a * 'a)) : ('b * 'b) =
  (f a1, f a2)

(* Map3 *)
let rec map3 (f : 'a -> 'b -> 'c -> 'd) l1 l2 l3 : 'd list =
  match (l1, l2, l3) with
  | ([], [], []) ->
     []
  | (h1 :: t1, h2 :: t2, h3 :: t3) ->
     let r = f h1 h2 h3 in r :: map3 f t1 t2 t3

(*
 * Creates a list of the range of min to max, excluding max
 * This is an auxiliary function renamed from seq in template-coq
 *)
let rec range (min : int) (max : int) : int list =
  if min < max then
    min :: range (min + 1) max
  else
    []

(* Creates a list from the index 1 to max, inclusive *)
let from_one_to (max : int) : int list =
  range 1 (max + 1)

(* Return a list of all indexes in env, starting with 1 *)
let all_rel_indexes (env : env) : int list =
  from_one_to (nb_rel env)

(* Intern a term *)
let intern env evm t : types =
  let (trm, _) = Constrintern.interp_constr env evm t in
  trm

(* Extern a term *)
let extern env evm t : Constrexpr.constr_expr =
  Constrextern.extern_constr true env evm t

(* Lookup a definition *)
let lookup_definition (env : env) (def : types) : types =
  match kind_of_term def with
  | Const (c, u) ->
     let c_body = (lookup_constant c env).const_body in
     (match c_body with
      | Def cs -> Mod_subst.force_constr cs
      | OpaqueDef o -> Opaqueproof.force_proof (Global.opaque_tables ()) o
      | _ -> failwith "an axiom has no definition")
  | Ind _ -> def
  | _ -> failwith "not a definition"

(* Fully lookup a def in env, but return the term if it is not a definition *)
let rec unwrap_definition (env : env) (trm : types) : types =
  try
    unwrap_definition env (lookup_definition env trm)
  with _ ->
    trm

(* Don't support mutually inductive or coinductive types yet *)
let check_inductive_supported mutind_body : unit =
  let ind_bodies = mutind_body.mind_packets in
  if not (Array.length ind_bodies = 1) then
    failwith "mutually inductive types not yet supported"
  else
    if (mutind_body.mind_finite = Decl_kinds.CoFinite) then
      failwith "coinductive types not yet supported"
    else
      ()

(* Get the type of an inductive type *)
let type_of_inductive env index mutind_body : types =
  let ind_bodies = mutind_body.mind_packets in
  let ind_body = Array.get ind_bodies index in
  let univ_context = mutind_body.mind_universes in
  let univ_instance = UContext.instance univ_context in
  let mutind_spec = (mutind_body, ind_body) in
  Inductive.type_of_inductive env (mutind_spec, univ_instance)

(*
 * Inductive types create bindings that we need to push to the environment
 * This function gets those bindings
 *)
let bindings_for_inductive env mutind_body ind_bodies : CRD.t list =
  Array.to_list
    (Array.mapi
       (fun i ind_body ->
         let name_id = ind_body.mind_typename in
         let typ = type_of_inductive env i mutind_body in
         CRD.LocalAssum (Names.Name name_id, typ))
       ind_bodies)

(*
 * Similarly but for fixpoints
 *)
let bindings_for_fix (names : name array) (typs : types array) : CRD.t list =
  Array.to_list
    (CArray.map2_i
       (fun i name typ -> CRD.LocalAssum (name, Vars.lift i typ))
       names typs)

(* Get the arity of a function or function type *)
let rec arity p =
  match kind_of_term p with
  | Lambda (_, _, b) ->
     1 + arity b
  | Prod (_, _, b) ->
     1 + arity b
  | _ ->
     0

(* Infer the type of trm in env *)
let infer_type (env : env) (trm : types) : types =
  let jmt = Typeops.infer env trm in
  j_type jmt

(* Check whether two terms are convertible, ignoring universe inconsistency *)
let conv_ignoring_univ_inconsistency env evm trm1 trm2 : bool =
  try
    Reductionops.is_conv env evm trm1 trm2
  with _ ->
    match map_tuple kind_of_term (trm1, trm2) with
    | (Sort (Type u1), Sort (Type u2)) -> true
    | _ -> false

(* Checks whether two terms are convertible in env with no evars *)
let convertible (env : env) (trm1 : types) (trm2 : types) : bool =
  conv_ignoring_univ_inconsistency env Evd.empty trm1 trm2

(* Check whether a term is a certain debruijn index *)
let is_rel (trm : types) (i : int) : bool =
  eq_constr trm (mkRel i)

(* Lookup the eliminator over the type sort *)
let type_eliminator (env : env) (ind : inductive) =
  Universes.constr_of_global (Indrec.lookup_eliminator ind InType)

(* Zoom into a term *)
let rec zoom_n_prod env npm typ : env * types =
  if npm = 0 then
    (env, typ)
  else
    match kind_of_term typ with
    | Prod (n1, t1, b1) ->
       zoom_n_prod (push_rel CRD.(LocalAssum (n1, t1)) env) (npm - 1) b1
    | _ ->
       failwith "more parameters expected"

(* Zoom all the way into a lambda term *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_rel CRD.(LocalAssum(n, t)) env) b
  | _ ->
     (env, trm)

(* Zoom all the way into a product type *)
let rec zoom_product_type (env : env) (typ : types) : env * types =
  match kind_of_term typ with
  | Prod (n, t, b) ->
     zoom_product_type (push_rel CRD.(LocalAssum(n, t)) env) b
  | _ ->
     (env, typ)

(* Reconstruct a lambda from an environment, but stop when i are left *)
let rec reconstruct_lambda_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_lambda_n env' (mkLambda (n, t, b)) i

(* Reconstruct a lambda from an environment *)
let reconstruct_lambda (env : env) (b : types) : types =
  reconstruct_lambda_n env b 0

(* Apply a function twice with a directionality indicator *)
let twice (f : 'a -> 'a -> bool -> 'b) (a1 : 'a) (a2 : 'a) : 'b * 'b  =
  let forward = f a1 a2 true in
  let backward = f a2 a1 false in
  (forward, backward)

(* Reverse a tuple *)
let reverse ((a, b) : 'a * 'b) : 'b * 'a =
  (b, a)

(*
 * Recurse on a mapping function with an environment for a fixpoint
 *)
let map_rec_env_fix map_rec d env a (ns : name array) (ts : types array) =
  let fix_bindings = bindings_for_fix ns ts in
  let env_fix = push_rel_context fix_bindings env in
  let n = List.length fix_bindings in
  let d_n = List.fold_left (fun a' _ -> d a') a (range 0 n) in
  map_rec env_fix d_n

(*
 * Map a function over a term in an environment
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env f d in
  match kind_of_term trm with
  | Cast (c, k, t) ->
     let c' = map_rec env a c in
     let t' = map_rec env a t in
     mkCast (c', k, t')
  | Prod (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
     mkProd (n, t', b')
  | Lambda (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_rel CRD.(LocalAssum(n, t)) env) (d a) b in
     mkLambda (n, t', b')
  | LetIn (n, trm, typ, e) ->
     let trm' = map_rec env a trm in
     let typ' = map_rec env a typ in
     let e' = map_rec (push_rel CRD.(LocalDef(n, e, typ)) env) (d a) e in
     mkLetIn (n, trm', typ', e')
  | App (fu, args) ->
     let fu' = map_rec env a fu in
     let args' = Array.map (map_rec env a) args in
     mkApp (fu', args')
  | Case (ci, ct, m, bs) ->
     let ct' = map_rec env a ct in
     let m' = map_rec env a m in
     let bs' = Array.map (map_rec env a) bs in
     mkCase (ci, ct', m', bs')
  | Fix ((is, i), (ns, ts, ds)) ->
     let ts' = Array.map (map_rec env a) ts in
     let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
     mkFix ((is, i), (ns, ts', ds'))
  | CoFix (i, (ns, ts, ds)) ->
     let ts' = Array.map (map_rec env a) ts in
     let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
     mkCoFix (i, (ns, ts', ds'))
  | Proj (p, c) ->
     let c' = map_rec env a c in
     mkProj (p, c')
  | _ ->
     f env a trm

(*
 * Map a function over a term, when the environment doesn't matter
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let map_term f d (a : 'a) (trm : types) : types =
  map_term_env (fun _ a t -> f a t) d empty_env a trm

(* Unshift an index by n *)
let unshift_i_by (n : int) (i : int) : int =
  i - n

(* Shift an index by n *)
let shift_i_by (n : int) (i : int) : int =
  unshift_i_by (- n) i

(* Unshift an index *)
let unshift_i (i : int) : int =
  unshift_i_by 1 i

(* Shift an index *)
let shift_i (i : int) : int =
  shift_i_by 1 i

(*
 * Unshifts a term by n if it is greater than the maximum index
 * max of a local binding
 *)
let unshift_local (max : int) (n : int) (trm : types) : types =
  map_term
    (fun (m, adj) t ->
      match kind_of_term t with
      | Rel i ->
         let i' = if i > m then unshift_i_by adj i else i in
         mkRel i'
      | _ ->
         t)
    (fun (m, adj) -> (shift_i m, adj))
    (max, n)
    trm

(*
 * Shifts a term by n if it is greater than the maximum index
 * max of a local binding
 *)
let shift_local (max : int) (n : int) (trm : types) : types =
  unshift_local max (- n) trm

(* Decrement the relative indexes of a term t by n *)
let unshift_by (n : int) (trm : types) : types =
  unshift_local 0 n trm

(* Increment the relative indexes of a term t by n *)
let shift_by (n : int) (t : types) : types  =
  unshift_by (- n) t

(* Increment the relative indexes of a term t by one *)
let shift (t : types) : types  =
  shift_by 1 t

(* Decrement the relative indexes of a term t by one *)
let unshift (t : types) : types =
  unshift_by 1 t

(*
 * Map a function over a term in an environment
 * Only apply the function when a proposition is true
 * Apply the function eagerly
 * Update the environment as you go
 * Update the argument of type 'a using the a supplied update function
 * Return a new term
 *)
let rec map_term_env_if p f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if p f d in
  if p env a trm then
    f env a trm
  else
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_rel CRD.(LocalAssum(n, t')) env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_rel CRD.(LocalDef(n, e, typ')) env) (d a) e in
       mkLetIn (n, trm', typ', e')
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' = Array.map (map_rec env a) args in
       mkApp (fu', args')
    | Case (ci, ct, m, bs) ->
       let ct' = map_rec env a ct in
       let m' = map_rec env a m in
       let bs' = Array.map (map_rec env a) bs in
       mkCase (ci, ct', m', bs')
    | Fix ((is, i), (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       mkFix ((is, i), (ns, ts', ds'))
    | CoFix (i, (ns, ts, ds)) ->
       let ts' = Array.map (map_rec env a) ts in
       let ds' = Array.map (map_rec_env_fix map_rec d env a ns ts) ds in
       mkCoFix (i, (ns, ts', ds'))
    | Proj (pr, c) ->
       let c' = map_rec env a c in
       mkProj (pr, c')
    | _ ->
       trm

(* Map a substitution over a term *)
let all_substs p env (src, dst) trm : types =
  map_term_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs =
  all_substs convertible

(* Define a new Coq term *)
let define_term (n : Id.t) (env : env) evm (trm : types) : unit =
  do_definition
    n
    (Global, false, Definition)
    None
    []
    None
    (extern env evm trm)
    None
    (Lemmas.mk_hook (fun _ _ -> ()))

(* --- Debugging, from PUMPKIN PATCH --- *)

(* Using pp, prints directly to a string *)
let print_to_string (pp : formatter -> 'a -> unit) (trm : 'a) : string =
  Format.asprintf "%a" pp trm

(* Gets n as a string *)
let name_as_string (n : name) : string =
  match n with
  | Name id -> string_of_id id
  | Anonymous -> "_"

(* Pretty prints a term using Coq's pretty printer *)
let print_constr (fmt : formatter) (c : constr) : unit  =
  Pp.pp_with fmt (Printer.pr_constr c)

(* Pretty prints a universe level *)
let print_univ_level (fmt : formatter) (l : Level.t) =
  Pp.pp_with fmt (Level.pr l)

(* Prints a universe *)
let universe_as_string u =
  match Universe.level u with
  | Some l ->
     print_to_string print_univ_level l
  | None ->
     Printf.sprintf
       "Max{%s}"
       (String.concat
          ", "
          (List.map
             (print_to_string print_univ_level)
             (LSet.elements (Universe.levels u))))

(* Gets a sort as a string *)
let sort_as_string s =
  match s with
  | Prop _ -> if s = prop_sort then "Prop" else "Set"
  | Type u -> Printf.sprintf "Type %s" (universe_as_string u)

(* Prints a term *)
(* TODO this is better than the old one, merge back in with existing code! *)
let rec term_as_string (env : env) (trm : types) =
  match kind_of_term trm with
  | Rel i ->
     (try
       let (n, _, _) = CRD.to_tuple @@ lookup_rel i env in
       Printf.sprintf "(%s [Rel %d])" (name_as_string n) i
     with
       Not_found -> Printf.sprintf "(Unbound_Rel %d)" i)
  | Var v ->
     string_of_id v
  | Evar (k, cs) ->
     Printf.sprintf "??"
  | Sort s ->
     sort_as_string s
  | Cast (c, k, t) ->
     Printf.sprintf "(%s : %s)" (term_as_string env c) (term_as_string env t)
  | Prod (n, t, b) ->
     Printf.sprintf
       "(Π (%s : %s) . %s)"
       (name_as_string n)
       (term_as_string env t)
       (term_as_string (push_rel CRD.(LocalAssum(n, t)) env) b)
  | Lambda (n, t, b) ->
     Printf.sprintf
       "(λ (%s : %s) . %s)"
       (name_as_string n)
       (term_as_string env t)
       (term_as_string (push_rel CRD.(LocalAssum(n, t)) env) b)
  | LetIn (n, trm, typ, e) ->
     Printf.sprintf
       "(let (%s : %s) := %s in %s)"
       (name_as_string n)
       (term_as_string env typ)
       (term_as_string env typ)
       (term_as_string (push_rel CRD.(LocalDef(n, e, typ)) env) e)
  | App (f, xs) ->
     Printf.sprintf
       "(%s %s)"
       (term_as_string env f)
       (String.concat " " (List.map (term_as_string env) (Array.to_list xs)))
  | Const (c, u) ->
     let ker_name = Constant.canonical c in
     string_of_kn ker_name
  | Construct (((i, i_index), c_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     let constr_name_id = ind_body.mind_consnames.(c_index - 1) in
     string_of_id constr_name_id
  | Ind ((i, i_index), u) ->
     let mutind_body = lookup_mind i env in
     let ind_bodies = mutind_body.mind_packets in
     let name_id = (ind_bodies.(i_index)).mind_typename in
     string_of_id name_id
  | Fix ((is, i), (ns, ts, ds)) ->
     let env_fix = push_rel_context (bindings_for_fix ns ds) env in
     String.concat
       " with "
       (map3
          (fun n t d ->
            Printf.sprintf
             "(Fix %s : %s := %s)"
             (name_as_string n)
             (term_as_string env t)
             (term_as_string env_fix d))
          (Array.to_list ns)
          (Array.to_list ts)
          (Array.to_list ds))
  | Case (ci, ct, m, bs) ->
     let (i, i_index) = ci.ci_ind in
     let mutind_body = lookup_mind i env in
     let ind_body = mutind_body.mind_packets.(i_index) in
     Printf.sprintf
       "(match %s : %s with %s)"
       (term_as_string env m)
       (term_as_string env ct)
       (String.concat
          " "
          (Array.to_list
             (Array.mapi
                (fun c_i b ->
                  Printf.sprintf
                    "(case %s => %s)"
                    (string_of_id (ind_body.mind_consnames.(c_i)))
                    (term_as_string env b))
                bs)))
  | Meta mv -> (* TODO *)
     Printf.sprintf "(%s)" (print_to_string print_constr trm)
  | CoFix (i, (ns, ts, ds)) -> (* TODO *)
     Printf.sprintf "(%s)" (print_to_string print_constr trm)
  | Proj (p, c) -> (* TODO *)
     Printf.sprintf "(%s)" (print_to_string print_constr trm)

(* Print a separator string *)
let print_separator unit : unit =
  Printf.printf "%s\n\n" "-----------------"

(* Debug a term *)
let debug_term (env : env) (trm : types) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (term_as_string env trm)

(* Debug a list of terms *)
let debug_terms (env : env) (trms : types list) (descriptor : string) : unit =
  List.iter (fun t -> debug_term env t descriptor) trms

(* --- Coq environments --- *)

(* Gets env as a string *)
let env_as_string (env : env) : string =
  let all_relis = all_rel_indexes env in
  String.concat
    ",\n"
    (List.map
       (fun i ->
         let (n, b, t) = CRD.to_tuple @@ lookup_rel i env in
         Printf.sprintf
           "%s (Rel %d): %s"
           (name_as_string n)
           i
           (term_as_string (pop_rel_context i env) t))
       all_relis)

(* Debug an environment *)
let debug_env (env : env) (descriptor : string) : unit =
  Printf.printf "%s: %s\n\n" descriptor (env_as_string env)

(* --- Search --- *)

(* Search two inductive types for a parameterizing ornament *)
let search_orn_params env (ind_o : inductive) (ind_n : inductive) is_fwd : types =
  failwith "parameterization is not yet supported"

(* Get the index type, assuming we've added just one *)
let rec index_type env p_o p_n =
  match map_tuple kind_of_term (p_o, p_n) with
  | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
     if convertible env t_o t_n then
       let env_t = push_rel CRD.(LocalAssum (n_o, t_o)) env in
       index_type env_t b_o b_n
     else
       t_n
  | _ ->
     failwith "could not find indexer property"

(* Destruct the type of an induction principle into its cases *)
let rec destruct_cases elim_b : types list =
  match kind_of_term elim_b with
  | Prod (n, t, b) ->
     t :: destruct_cases (unshift b)
  | _ ->
     []

(* TODO explain *)
let properties i t_o t_n =
  match map_tuple kind_of_term (t_o, t_n) with
  | (App (f_o, args_o), App (f_n, args_n)) ->
     is_rel f_o i && is_rel f_n i
  | _ ->
     is_rel t_o i && is_rel t_n i

(* TODO explain *)
let old_new pind_o pind_n e_o e_n t_o t_n =
  let old_new_terms t_o t_n =
    match map_tuple kind_of_term (t_o, t_n) with
    | (App (f_o, args_o), App (f_n, args_n)) ->
       eq_constr f_o pind_o && eq_constr f_n pind_n
    | _ ->
       eq_constr t_o pind_o && eq_constr t_n pind_n
  in
  old_new_terms t_o t_n ||
  old_new_terms (infer_type e_o t_o) (infer_type e_n t_n)

(* Get a single case for the indexer *)
(* TODO need to generalize this logic better, try sub & check approach *)
(* TODO clean *)
let index_case index_t prop_index env_o env_n pind_o pind_n c_o c_n : types =
  let conv_modulo_change i e_o e_n t_o t_n =
    properties i t_o t_n || old_new pind_o pind_n e_o e_n t_o t_n || convertible env_o t_o t_n
  in
  let rec diff_index i o n =
    match map_tuple kind_of_term (o, n) with
    | (App (f_o, args_o), App (f_n, args_n)) when properties i f_o f_n ->
       Array.get args_n 0 (* TODO assumes index is first *)
    | _ ->
       failwith "not an application of a property"
  in let rec diff_case pil iil i_t i e_o e_n o n =
    match map_tuple kind_of_term (o, n) with
    | (App (f_o, args_o), App (f_n, args_n)) when properties i f_o f_n ->
       List.fold_left2
         (fun idx p_i i_i ->
           let sub_p = (i_i, mkRel p_i) in
           let idx' = all_substs (fun _ -> eq_constr) e_o sub_p idx in
           let i_i' = unshift i_i in
           idx')
         (diff_index i o n) (* TODO assumes index is first *)
         pil
         iil
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let e_b_n = push_rel CRD.(LocalAssum (n_n, t_n)) e_n in
       let i_b = shift_i i in
       let i_t_b = shift i_t in
       if not (conv_modulo_change i e_o e_n t_o t_n) then
         let e_b_o = push_rel CRD.(LocalAssum (n_n, t_n)) e_o in
         let pil' = List.map shift_i pil in
         let iil' = List.map shift iil in
         unshift (diff_case pil' iil' i_t_b i_b e_b_o e_b_n (shift o) b_n)
       else
         let e_b_o = push_rel CRD.(LocalAssum (n_o, t_o)) e_o in
         if properties i t_o t_n then
           let pil' = 1 :: List.map shift_i pil in
           let iil' = List.map shift (diff_index i t_o t_n :: iil) in
           mkLambda (n_o, i_t, diff_case pil' iil' i_t_b i_b e_b_o e_b_n b_o b_n)
         else
           let pil' = List.map shift_i pil in
           let iil' = List.map shift iil in
           mkLambda (n_o, t_o, diff_case pil' iil' i_t_b i_b e_b_o e_b_n b_o b_n)
    | _ ->
       failwith "unxpected case"
  in diff_case [] [] index_t prop_index env_o env_n c_o c_n

(* Get the cases for the indexer *)
let indexer_cases env_o env_n index_t o n : types list =
  let (pind_o, arity_o, elim_t_o) = o in
  let (pind_n, arity_n, elim_t_n) = n in
  let (n_o, p_o, b_o) = destProd elim_t_o in
  let (n_n, p_n, b_n) = destProd elim_t_n in
  let env_p_o = push_rel CRD.(LocalAssum (n_o, p_o)) env_o in
  let env_p_n = push_rel CRD.(LocalAssum (n_n, p_n)) env_n in
  let cs_o_ext = destruct_cases b_o in
  let cs_n_ext = destruct_cases b_n in
  let cs_o = take_except 1 cs_o_ext in
  let cs_n = take_except (1 + (arity_n - arity_o)) cs_n_ext in
  List.map2 (index_case index_t 1 env_p_o env_p_n pind_o pind_n) cs_o cs_n

(* TODO explain, move *)
let mk_n_rels arity =
  List.map mkRel (List.rev (from_one_to arity))

(* Search for an indexing function *)
let search_for_indexer env_o env_n npm elim_o o n is_fwd : types option =
  if is_fwd then
    let (pind_o, arity_o, elim_t_o) = o in
    let (pind_n, arity_n, elim_t_n) = n in
    let (_, p_o, b_o) = destProd elim_t_o in
    let (_, p_n, b_n) = destProd elim_t_n in
    let (env_indexer, _) = zoom_product_type env_o p_o in
    let index_t = index_type env_n p_o p_n in
    let off = nb_rel env_indexer - npm in
    let indexer_pms = List.map shift (mk_n_rels npm) in
    let indexer_p = shift_by off (reconstruct_lambda_n env_indexer index_t npm) in
    let indexer_cs = indexer_cases env_o env_n index_t o n in
    let indexer_args = Array.of_list (List.append indexer_pms (indexer_p :: indexer_cs)) in
    let indexer = mkApp (mkApp (elim_o, indexer_args), Array.make 1 (mkRel 1)) in
    Some (reconstruct_lambda env_indexer indexer)
  else
    None

(* TODO explain *)
let orn_p env pind arity npm =
  let off = nb_rel env - npm in
  let shift_off = shift_by off in
  let pargs = List.map shift_off (mk_n_rels arity) in
  shift_off
    (reconstruct_lambda_n
       env
       (mkApp (pind, Array.of_list pargs))
       npm) (* TODO apply indexer if exists *)

(* Search two inductive types for an indexing ornament, using eliminators *)
let search_orn_index_elim env_o env_n npm elim_o o n is_fwd : (types option * types) =
  let indexer = search_for_indexer env_o env_n npm elim_o o n is_fwd in
  let (pind_o, arity_o, elim_t_o) = o in
  let (pind_n, arity_n, elim_t_n) = n in
  let (_, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, b_n) = destProd elim_t_n in
  let (env_ornament, _) = zoom_product_type env_o p_o in
  let pms = List.map shift (mk_n_rels npm) in
  debug_term env_o p_o "p_o";
  debug_term env_n p_n "p_n";
  let (pind, arity) = if is_fwd then (pind_n, arity_o) else (pind_n, arity_n) in
  let orn_p = orn_p env_ornament pind arity npm in
  debug_term env_ornament orn_p "orn_p";
 (* 
    let indexer_cs = indexer_cases env_o env_n index_t o n in
    let indexer_args = Array.of_list (List.append indexer_pms (indexer_p :: indexer_cs)) in
    let indexer = mkApp (mkApp (elim_o, indexer_args), Array.make 1 (mkRel 1)) in
    Some (reconstruct_lambda env_indexer indexer)*)

  let ornament = reconstruct_lambda env_ornament elim_o in (* TODO apply to things *)
  (indexer, ornament)

(* Search two inductive types for an indexing ornament *)
let search_orn_index env npm o n is_fwd : (types option * types) =
  let (pind_o, arity_o) = o in
  let (pind_n, arity_n) = n in
  let (ind_o, _) = destInd pind_o in
  let (ind_n, _) = destInd pind_n in
  let (elim_o, elim_n) = map_tuple (type_eliminator env) (ind_o, ind_n) in
  let (elim_t_o, elim_t_n) = map_tuple (infer_type env) (elim_o, elim_n) in
  let (env_o, elim_t_o') = zoom_n_prod env npm elim_t_o in
  let (env_n, elim_t_n') = zoom_n_prod env npm elim_t_n in
  let o = (pind_o, arity_o, elim_t_o') in
  let n = (pind_n, arity_n, elim_t_n') in
  search_orn_index_elim env_o env_n npm elim_o o n is_fwd

(* Search two inductive types for an ornament between them *)
(* TODO eventually, when supporting many changes, will want to chain these *)
(* When we do that, we'll also want better detection. For now, we just
 * assume only one at a time
 * We also assume same order for now, of parameters and constructors and so on
 * TODO better data representations for return types etc.
 * TODO what happens when an indexed type isn't a measure, so you can't
 * extract the index from the old type? When does that happen?
 * TODO figuring out when we need more premises, too, as in bal_bintrees
 * TODO figuring out when we have extra premises, too (separate concerns,
 * but makes indexing function ill-defined right now because we assume
 * every nat is an index regardless of constructor arity, see vector3)
 *)
let search_orn_inductive (env : env) (o : types) (n : types) : (types option) * types * types =
  match map_tuple kind_of_term (o, n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if npm_o < npm_n then
       let (orn_o, orn_n) = twice (search_orn_params env) (i_o, ii_o) (i_n, ii_n) in
       (None, orn_o, orn_n)
     else if npm_n < npm_o then
       let (orn_o, orn_n) = reverse (twice (search_orn_params env) (i_n, ii_n) (i_o, ii_o)) in
       (None, orn_o, orn_n)
     else
       let npm = npm_o in
       let (typ_o, typ_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
       let (arity_o, arity_n) = map_tuple arity (typ_o, typ_n) in
       let search_o = (o, arity_o) in
       let search_n = (n, arity_n) in
       let search = twice (search_orn_index env npm) in
       if arity_o < arity_n then
         let ((idx, orn_o), (_, orn_n)) = search search_o search_n in
         (idx, orn_o, orn_n)
       else if arity_n < arity_o then
         let ((_, orn_o), (idx, orn_n)) = reverse (search search_n search_o) in
         (idx, orn_o, orn_n)
       else
         failwith "not supported"
  | _ ->
     failwith "not supported"

(* --- Top-level --- *)

(* Identify an ornament *)
let find_ornament n d_old d_new =
  let (evm, env) = Lemmas.get_current_context () in
  let old_term = unwrap_definition env (intern env evm d_old) in
  let new_term = unwrap_definition env (intern env evm d_new) in
  if isInd old_term && isInd new_term then
    let prefix = Id.to_string n in
    let (idx, orn_o_n, orn_n_o) = search_orn_inductive env old_term new_term in
    (if Option.has_some idx then
       let idx_n_string = String.concat "_" [prefix; "index"] in
       let idx_n = Id.of_string idx_n_string in
       define_term idx_n env evm (Option.get idx);
       Printf.printf "Defined indexing function %s.\n\n" idx_n_string;
     else
       ());
    (*debug_term env orn_o_n "orn_o_n";
    debug_term env orn_n_o "orn_n_o";*)
    (* TODO define and so on *)
    ()
  else
    failwith "Only inductive types are supported"

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ find_ornament n d_old d_new ]
END
