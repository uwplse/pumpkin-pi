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

(* --- Ornaments --- *)

(*
 * For now, an ornamental promotion is an optional indexing function, a function
 * from T1 -> T2, a function from T2 -> T1. Later, it will also contain
 * patches and extra premises, and these will be present both in the top-level
 * type and as premises to the functions in both directions.
 *
 * We don't represent ornaments directly, yet, but this may also be useful.
 *)
type promotion =
  {
    indexer : types option;
    promote : types;
    forget : types;
  }

(* --- Auxiliary functions, mostly from PUMPKIN PATCH --- *)

(* Take the union of two lists, maintaining order *)
let rec union (c : 'a -> 'a -> int) (l1 : 'a list) (l2 : 'a list) : 'a list =
  match (l1, l2) with
  | (h1 :: t1, h2 :: t2) ->
     let ch = c h1 h2 in
     if ch = 0 then
       h1 :: union c t1 t2
     else if ch > 0 then
       h1 :: union c t1 l2
     else
       h2 :: union c l1 t2
  | (h1 :: t1, _) ->
     l1
  | (_, _) ->
     l2

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

(* Like take, but return the remainder too *)
let rec take_split (i : int) (l : 'a list) : ('a list * 'a list) =
  if i = 0 then
    ([], l)
  else
    match l with
    | [] ->
       ([], [])
    | h :: tl ->
       let (before, after) = take_split (i - 1) tl in
       (h :: before, after)

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

(* Push a local binding to an environment *)
let push_local (n, t) = push_rel CRD.(LocalAssum (n, t))

(* Push a let-in definition to an environment *)
let push_local_in (n, e, t) = push_rel CRD.(LocalDef(n, e, t))

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

(* Check whether trm applies f (using eq_constr for equality) *)
let applies (f : types) (trm : types) =
  match kind_of_term trm with
  | App (g, _) ->
     eq_constr f g
  | _ ->
     false

(* Check whether trm is trm' or applies trm', using eq_constr *)
let is_or_applies (trm' : types) (trm : types) : bool =
  applies trm' trm || eq_constr trm' trm

(* Check that p a and p b are both true *)
let and_p (p : 'a -> bool) (o : 'a) (n : 'a) : bool =
  p o && p n

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
       zoom_n_prod (push_local (n1, t1) env) (npm - 1) b1
    | _ ->
       failwith "more parameters expected"

(* Zoom all the way into a lambda term *)
let rec zoom_lambda_term (env : env) (trm : types) : env * types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     zoom_lambda_term (push_local (n, t) env) b
  | _ ->
     (env, trm)

(* Zoom all the way into a product type *)
let rec zoom_product_type (env : env) (typ : types) : env * types =
  match kind_of_term typ with
  | Prod (n, t, b) ->
     zoom_product_type (push_local (n, t) env) b
  | _ ->
     (env, typ)

(* Zoom into the environment *)
let zoom_env zoom (env : env) (trm : types) : env =
  fst (zoom env trm)

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

(* Reconstruct a product from an environment, but stop when i are left *)
let rec reconstruct_product_n (env : env) (b : types) (i : int) : types =
  if nb_rel env = i then
    b
  else
    let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
    let env' = pop_rel_context 1 env in
    reconstruct_product_n env' (mkProd (n, t, b)) i

(* Reconstruct a product from an environment *)
let reconstruct_product (env : env) (b : types) : types =
  reconstruct_product_n env b 0

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
     let b' = map_rec (push_local (n, t) env) (d a) b in
     mkProd (n, t', b')
  | Lambda (n, t, b) ->
     let t' = map_rec env a t in
     let b' = map_rec (push_local (n, t) env) (d a) b in
     mkLambda (n, t', b')
  | LetIn (n, trm, typ, e) ->
     let trm' = map_rec env a trm in
     let typ' = map_rec env a typ in
     let e' = map_rec (push_local_in (n, e, typ) env) (d a) e in
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
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_local_in (n, e, typ') env) (d a) e in
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

(*
 * Like map_term_env_if, but just return true if the proposition is satisfied,
 * and false otherwise.
 *
 * We can make this even more general and just take a combinator
 * and a mapping function and so on, in the future.
 *)
let rec exists_subterm_env p d (env : env) (a : 'a) (trm : types) : bool =
  let exists p a = List.exists p (Array.to_list a) in
  let map_rec = exists_subterm_env p d in
  if p env a trm then
    true
  else
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       c' || t'
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       t' || b'
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t) env) (d a) b in
       t' || b'
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_local_in (n, e, typ) env) (d a) e in
       trm' || typ' || e'
    | App (fu, args) ->
       let fu' = map_rec env a fu in
       let args' = exists (map_rec env a) args in
       fu' || args'
    | Case (ci, ct, m, bs) ->
       let ct' = map_rec env a ct in
       let m' = map_rec env a m in
       let bs' = exists (map_rec env a) bs in
       ct' || m' || bs'
    | Fix ((is, i), (ns, ts, ds)) ->
       let ts' = exists (map_rec env a) ts in
       let ds' = exists (map_rec_env_fix map_rec d env a ns ts) ds in
       ts' || ds'
    | CoFix (i, (ns, ts, ds)) ->
       let ts' = exists (map_rec env a) ts in
       let ds' = exists (map_rec_env_fix map_rec d env a ns ts) ds in
       ts' || ds'
    | Proj (pr, c) ->
       map_rec env a c
    | _ ->
       false

(*
 * Lazy version
 *)
let rec map_term_env_if_lazy p f d (env : env) (a : 'a) (trm : types) : types =
  let map_rec = map_term_env_if_lazy p f d in
  let trm' =
    match kind_of_term trm with
    | Cast (c, k, t) ->
       let c' = map_rec env a c in
       let t' = map_rec env a t in
       mkCast (c', k, t')
    | Prod (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkProd (n, t', b')
    | Lambda (n, t, b) ->
       let t' = map_rec env a t in
       let b' = map_rec (push_local (n, t') env) (d a) b in
       mkLambda (n, t', b')
    | LetIn (n, trm, typ, e) ->
       let trm' = map_rec env a trm in
       let typ' = map_rec env a typ in
       let e' = map_rec (push_local_in (n, e, typ') env) (d a) e in
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
  in if p env a trm' then f env a trm' else trm'

(* Map a substitution over a term *)
let all_substs p env (src, dst) trm : types =
  map_term_env_if
    (fun en (s, _) t -> p en s t)
    (fun _ (_, d) _ -> d)
    (fun (s, d) -> (shift s, shift d))
    env
    (src, dst)
    trm

(* Locally empty environment *)
let empty = Global.env ()

(* Map_term_env_if with an empty environment *)
let map_term_if p f d =
  map_term_env_if
    (fun _ a t -> p a t)
    (fun _ a t -> f a t)
    d
    empty

(* Lazy version *)
let map_term_if_lazy p f d =
  map_term_env_if_lazy
    (fun _ a t -> p a t)
    (fun _ a t -> f a t)
    d
    empty

(* exists_subterm_env with an empty environment *)
let exists_subterm p d =
  exists_subterm_env
    (fun _ a t -> p a t)
    d
    empty

(* map and track with environments *)
let map_track_env mapper p f d env a trm =
  let occ = ref 0 in
  let f_track en a t = occ := !occ + 1; f en a t in
  (!occ, mapper p f_track d env a trm)

(* map and track *)
let map_track mapper p f d a trm =
  let occ = ref 0 in
  let f_track a t = occ := !occ + 1; f a t in
  (!occ, mapper p f_track d a trm)

(* In env, substitute all subterms of trm that are convertible to src with dst *)
let all_conv_substs =
  all_substs convertible

(* Same, but eq_constr *)
let all_eq_substs =
  all_substs (fun _ -> eq_constr) empty

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

(* Make n relative indices, from highest to lowest *)
let mk_n_rels n =
  List.map mkRel (List.rev (from_one_to n))

(* The current path *)
let current_path = ModPath.MPfile (Global.current_dirpath ())

(* Define a constant from an ID in the current path *)
let make_constant id =
  mkConst (Constant.make2 current_path (Label.of_id id))

(* Add a suffix to a name identifier *)
let with_suffix id suffix =
  let prefix = Id.to_string id in
  Id.of_string (String.concat "_" [prefix; suffix])

(* Default reducer *)
let reduce_term (trm : types) : types =
  Reductionops.nf_betaiotazeta Evd.empty trm

(* Reduce the type *)
let reduce_type (env : env) (trm : types) : types =
  reduce_term (infer_type env trm)

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
       (term_as_string (push_local (n, t) env) b)
  | Lambda (n, t, b) ->
     Printf.sprintf
       "(λ (%s : %s) . %s)"
       (name_as_string n)
       (term_as_string env t)
       (term_as_string (push_local (n, t) env) b)
  | LetIn (n, trm, typ, e) ->
     Printf.sprintf
       "(let (%s : %s) := %s in %s)"
       (name_as_string n)
       (term_as_string env typ)
       (term_as_string env typ)
       (term_as_string (push_local_in (n, e, typ) env) e)
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

(* --- Factoring, from PUMPKIN PATCH --- *)

type factors = (env * types) list
type factor_tree = Unit | Factor of (env * types) * factor_tree list

let assumption : types = mkRel 1

(* Debug dependent factors *)
let debug_factors_dep (fs : factor_tree) : unit =
  let rec as_string fs =
    match fs with
    | Factor ((en, t), cn) ->
       Printf.sprintf
         "Factor %s [%s]"
         (term_as_string en t)
         (String.concat "; " (List.map as_string cn))
    | Unit ->
       "Unit"
  in Printf.printf "%s\n\n" (as_string fs)

(*
 * Apply the assumption (last term in the environment) in the term
 *)
let apply_assumption (fs : factors) (trm : types) : types =
  if List.length fs > 0 then
    assumption
  else
    trm

(*
 * Apply the assumption in the dependent version
 *)
let apply_assumption_dep (i : int) (fs : factor_tree) (trm : types) : types * int =
  match fs with
  | Factor (_, _) ->
     (mkRel i, i - 1)
  | Unit ->
     (shift_by (i - 1) trm, i)

(*
 * Check if the term is the assumption (last term in the environment)
 *)
let is_assumption (env : env) (trm : types) : bool =
  convertible env trm assumption

(*
 * Assume a term of type typ in an environment
 *)
let assume (env : env) (n : name) (typ : types) : env =
  let env_pop = pop_rel_context 1 env in
  push_rel CRD.(LocalAssum(n, typ)) env_pop

(*
 * Auxiliary path-finding function, once we are zoomed into a lambda
 * and the hypothesis we care about is the assumption (first term
 * in the environment).
 *
 * The type path is in reverse order for efficiency, and is really
 * a list of environments (assumptions) and terms. When we refer to
 * "the end" it is the head of the list.
 *
 * The algorithm is as follows:
 * 1. If a term is the assumption, return a single path with
 *    the environment and term, which is the identity path.
 * 2. Otherwise, if it is an application:
 *    a. Recursively get the type path for each argument.
 *    b. If there are multiple nonempty type paths, then we cannot abstract out
 *       the assumption in a single function, so return the identity path.
 *    c. Otherwise, get the only non-empty path, then:
 *       i. Zoom in on each argument with the current assumption
 *       ii. Assume the conclusion of the element at the end of the path
 *       ii. Apply the function to the zoomed arguments in the environment
 *            with the new assumption, and add that to the end of the path
 *       iv. If applying the assumption at any point fails, return the empty
 *           path
 *
 * In other words, this is going as deep into the term as possible and
 * finding some Y for which X -> Y. It is then assuming Y,
 * and asking if there is some path from Y to the conclusion.
 *
 * It does not yet handle when Y depends on X. That case should
 * fail for inveresion, but we might want it if we use factoring for other
 * purposes, like to simplify abstraction.
 *)
let rec find_path (env : env) (trm : types) : factors =
  if is_assumption env trm then
    [(env, trm)]
  else
    match kind_of_term trm with
    | App (f, args) ->
       let paths = Array.map (find_path env) args in
       let nonempty_paths = List.filter (fun l -> List.length l > 0) (Array.to_list paths) in
       if List.length nonempty_paths > 1 then
	 [(env, trm)]
       else if List.length nonempty_paths = 1 then
	 let path = List.hd nonempty_paths in
	 let (env_arg, arg) = List.hd path in
         let assume_arg i a = apply_assumption (Array.get paths i) a in
         let args_assumed = Array.mapi assume_arg args in
	 try
           let t = unshift (reduce_type env_arg arg) in
	   (assume env Anonymous t, mkApp (f, args_assumed)) :: path
	 with _ ->
	   []
       else
	 []
    | _ -> (* other terms not yet implemented *)
       []

(*
 * Dependent version of the above
 *)
let rec find_path_dep (env : env) (trm : types) : factor_tree =
  if is_assumption env trm then
    Factor ((env, trm), [])
  else
    match kind_of_term trm with
    | App (f, args) ->
       let trees = Array.map (find_path_dep env) args in
       let filter_nonunit = List.filter (fun t -> not (t = Unit)) in
       let nonempty_trees = filter_nonunit (Array.to_list trees) in
       let num_trees = List.length nonempty_trees in
       let rec assume_args i j args =
         match args with
         | h :: tl ->
            let (h', j') = apply_assumption_dep j (Array.get trees i) h in
            h' :: (assume_args (i + 1) j' tl)
         | [] ->
            []
       in
       let assumed = Array.of_list (assume_args 0 num_trees (Array.to_list args)) in
       if num_trees > 0 then
         let (env, children) =
           List.fold_left
             (fun ((en, cn) : env * factor_tree list) (tr : factor_tree) ->
               let (Factor ((env_arg, arg), children)) = tr in
               try
                 if List.length cn > 0 then
                   let (Factor ((en_prev, prev), _)) = List.hd cn in
                   let t = reduce_type env_arg arg in
                   let t = all_conv_substs env_arg (prev, mkRel 1) t in
                   let en_t = push_local (Anonymous, t) en in
                   (en_t, ((Factor ((env_arg, arg), children)) :: cn))
                 else
                   let t = unshift (reduce_type env_arg arg) in
                   let en_t = assume env_arg Anonymous t in
                   (en_t, [((Factor ((env_arg, arg), children)))])
               with _ ->
                 (en, [Unit]))
             (env, [])
             nonempty_trees
         in Factor ((env, mkApp (f, assumed)), List.rev children)
       else
	 Unit
    | _ -> (* other terms not yet implemented *)
       Unit

(*
 * Given a term trm, if the type of trm is a function type
 * X -> Z, find factors through which it passes
 * (e.g., [H : X, F : X -> Y, G : Y -> Z] where trm = G o F)
 *
 * First zoom in all the way, then use the auxiliary path-finding
 * function.
 *)
let factor_term (env : env) (trm : types) : factors =
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (reduce_term trm) in
  let path_body = find_path env_zoomed trm_zoomed in
  List.map
    (fun (env, body) ->
      if is_assumption env body then
	(env, body)
      else
	let (n, _, t) = CRD.to_tuple @@ lookup_rel 1 env in
	(pop_rel_context 1 env, mkLambda (n, t, body)))
    path_body

(*
 * Dependent version
 *)
let factor_term_dep (env : env) (trm : types) : factor_tree =
  let (env_zoomed, trm_zoomed) = zoom_lambda_term env (reduce_term trm) in
  let tree_body = find_path_dep env_zoomed trm_zoomed in
  let rec factor_dep t =
    match t with
    | Factor ((env, body), children) ->
       let children = List.map factor_dep children in
       if is_assumption env body then
         Factor ((env, body), children)
       else
         let num_old_rels = nb_rel env_zoomed in
         let num_new_rels = nb_rel env - num_old_rels in
         let lambda = reconstruct_lambda_n env body (num_old_rels - 1) in
         let env_lambda = pop_rel_context (num_new_rels + 1) env in
         Factor ((env_lambda, lambda), children)
    | Unit ->
       Unit
  in factor_dep tree_body

(*
 * Reconstruct factors as terms using hypotheses from the environment.
 *
 * This basically produces a friendly external form in the correct order,
 * and using functions instead of closures. Inversion doesn't use this
 * for efficiency, but top-level functions probably want to.
 *)
let reconstruct_factors (fs : factors) : types list =
  List.map
    (fun (en, t) -> reconstruct_lambda en t)
    (List.tl (List.rev fs))

(* Apply factors to reconstruct a single term *)
let apply_factors (fs : factors) : types =
  let (env, base) = List.hd fs in
  let body =
    List.fold_right
      (fun (_, t) t_app ->
        mkApp (shift t, Array.make 1 t_app))
      (List.tl fs)
      base
  in reconstruct_lambda env body

(* --- Utilities that might not generalize outside of this tool --- *)

let are_or_apply (trm : types) = and_p (is_or_applies trm)
let apply (trm : types) = and_p (applies trm)

(* is_or_applies over two terms with a different check *)
let apply_old_new (o : types * types) (n : types * types) : bool =
  let (trm_o, trm_o') = o in
  let (trm_n, trm_n') = n in
  is_or_applies trm_o trm_o' && is_or_applies trm_n trm_n'

(* Deconstruct a product type (A -> B -> ... -> D) into A, B, ..., D *)
let rec deconstruct_product (trm : types) : types list =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     t :: deconstruct_product (unshift b)
  | _ ->
     []

(* Check if two terms are the same modulo a change of an inductive type *)
let same_mod_change env o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  apply_old_new o n || convertible env t_o t_n

(* Check if two terms are the same modulo an indexing of an inductive type *)
let same_mod_indexing env p_index o n =
  let (t_o, t_n) = map_tuple snd (o, n) in
  are_or_apply p_index t_o t_n || same_mod_change env o n

(* Check if two terms have the same type, ignoring universe inconsinstency *)
let same_type o n =
  let (env_o, t_o) = o in
  let (env_n, t_n) = n in
  try
    convertible env_o (infer_type env_o t_o) (infer_type env_n t_n)
  with _ ->
    false

(* Shift substitutions *)
let shift_subs = List.map (map_tuple shift)

(* Shift from substitutions *)
let shift_from = List.map (fun (s, d) -> (shift s, d))

(* Shift to substitutions *)
let shift_to = List.map (fun (s, d) -> (s, shift d))

(* Shift a list *)
let shift_all = List.map shift

(* Shift all elements of a list by n *)
let shift_all_by n = List.map (shift_by n)

(* Apply an eliminator *)
let apply_eliminator elim pms p cs final_args =
  let args = Array.of_list (List.append pms (p :: cs)) in
  mkApp (mkApp (elim, args), final_args)

(* Apply an eliminator and reconstruct it from an environment *)
let apply_eliminator_recons env elim pms p cs final_args =
  reconstruct_lambda env (apply_eliminator elim pms p cs final_args)

(* Get the first function of an application *)
let rec first_fun t =
  match kind_of_term t with
  | App (f, args) ->
     first_fun f
  | _ ->
     t

(* Get the inductive types applied in a hypothesis or conclusion *)
let rec ind_of (trm : types) : types =
  match kind_of_term trm with
  | App (f, args) ->
     ind_of f
  | Ind (_, _) ->
     trm
  | _ ->
     failwith "not an inductive type"

(* Get the inductive types an ornament maps between, including their arguments *)
let rec ind_of_orn (orn_type : types) : types * types =
  match kind_of_term orn_type with
  | Prod (n, t, b) when isProd b ->
     ind_of_orn b
  | Prod (n, t, b) ->
     (t, b)
  | _ ->
     failwith "not an ornament"

(* Get a list of all arguments, fully unfolded at the head *)
let unfold_args_app trm =
  let (f, args) = destApp trm in
  let rec unfold trm =
    match kind_of_term trm with
    | App (f, args) ->
       List.append (unfold f) (Array.to_list args)
    | _ ->
       [trm]
  in List.append (List.tl (unfold f)) (Array.to_list args)

(* Like unfold_args_app, but return empty if it's not an application *)
let unfold_args trm =
  if isApp trm then unfold_args_app trm else []

(*
 * Get the argument to an application of a property at argument position i.
 * This unfolds all arguments first.
 *)
let get_arg i trm =
  match kind_of_term trm with
  | App (_, _) ->
     let args = Array.of_list (unfold_args trm) in
     Array.get args i
  | _ ->
     failwith "not an application"

(*
 * Deconstruct an eliminator application.
 *
 * Assumes the inductive type is not mutually inductive.
 *)
let deconstruct_eliminator env app =
  let ip = first_fun app in
  let ip_args = unfold_args app in
  let ip_typ = reduce_type env ip in
  let from_typ =  first_fun (fst (ind_of_orn ip_typ)) in
  let ((from_i, _), _) = destInd from_typ in
  let from_m = lookup_mind from_i env in
  let npms = from_m.mind_nparams in
  let from_arity = arity (type_of_inductive env 0 from_m) in
  let num_indices = from_arity - npms in
  let num_props = 1 in
  let num_constrs = arity ip_typ - npms - num_props - num_indices - 1 in
  let (pms, pmd_args) = take_split npms ip_args in
  let (p :: cs_and_args) = pmd_args in
  let (cs, args) = take_split num_constrs cs_and_args in
  (ip, pms, p, cs, Array.of_list args)

(* Find the offset of some environment from some number of parameters *)
let offset env npm = nb_rel env - npm

(* Recursively turn a product into a function *)
let rec prod_to_lambda trm =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     mkLambda (n, t, prod_to_lambda b)
  | _ ->
     trm

(* Recursively turn a function into a product *)
let rec lambda_to_prod trm =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     mkProd (n, t, lambda_to_prod b)
  | _ ->
     trm

(*
 * Modify a case of an eliminator application to use
 * the new property p in its hypotheses
 *)
let with_new_p p c : types =
  let rec sub_p sub trm =
    let (p_o, p_n) = sub in
    match kind_of_term trm with
    | Prod (n, t, b) ->
       let sub_b = map_tuple shift sub in
       if applies p_o t then
         let (_, args) = destApp t in
         mkProd (n, mkApp (p_n, args), sub_p sub_b b)
       else
         mkProd (n, t, sub_p sub_b b)
    | _ ->
       trm
  in sub_p (mkRel 1, p) c

(*
 * Check recursively whether a term contains another term
 *)
let contains_term c trm =
  exists_subterm eq_constr shift c trm

(*
 * This function removes any terms from the hypothesis of a lambda
 * that are not referenced in the body, so that the term
 * has only hypotheses that are referenced.
 *
 * It's different from the version in PUMPKIN PATCH because it ignores
 * possible universe inconsistency.
 *)
let rec remove_unused_hypos (trm : types) : types =
  match kind_of_term trm with
  | Lambda (n, t, b) ->
     let b' = remove_unused_hypos b in
     if contains_term (mkRel 1) b' then
       mkLambda (n, t, b')
     else
       remove_unused_hypos (unshift b')
  | _ ->
     trm

(*
 * Get only the hypos that are used in the body,
 * but in the order they appear in the lambda
 *)
let get_used_hypos (trm : types) : types list =
  let rec get_used trm i =
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       let b' = remove_unused_hypos b in
       let bs = get_used b (unshift_i i) in
       if contains_term (mkRel 1) b' then
         mkRel i :: bs
       else
         bs
    | _ ->
       []
  in get_used trm (arity trm)

(*
 * Get the hypos that are used in the body, or that match
 * a certain predicate on the type
 *)
let get_used_or_p_hypos (p : types -> bool) (trm : types) : types list =
  let rec get_used trm i =
    match kind_of_term trm with
    | Lambda (n, t, b) ->
       let bs = get_used b (unshift_i i) in
       if p t then
         mkRel i :: bs
       else
         let b' = remove_unused_hypos b in
         if contains_term (mkRel 1) b' then
           mkRel i :: bs
         else
           bs
    | _ ->
       []
  in get_used trm (arity trm)

(*
 * Returns true if two applications contain have a different
 * argument at index i.
 *
 * For now, this uses precise equality, but we can loosen this
 * to convertibility if desirable.
 *)
let diff_arg i trm_o trm_n =
  try
    let arg_o = get_arg i trm_o in
    let arg_n = get_arg i trm_n in
    not (eq_constr arg_o arg_n)
  with _ ->
    true

(* Remove the final hypothesis of a lambda *)
let rec remove_final_hypo trm =
  match kind_of_term trm with
  | Lambda (n, t, b) when isLambda b ->
     mkLambda (n, t, remove_final_hypo b)
  | Lambda (n, t, b) ->
     unshift b
  | _ ->
     failwith "not a lambda"

(*
 * Substitute all applications of an indexer with a temporary index,
 * so that other functions can ignore indices.
 *
 * This is kind of gross, so hopefully we don't need it eventually.
 *)
let temporary_index orn trm =
  if Option.has_some orn.indexer then
    let indexer = Option.get orn.indexer in
    map_term_if
      (fun _ t -> applies indexer t)
      (fun _ t -> mkRel 0)
      (fun _ -> ())
      ()
      trm
  else
    trm

(*
 * Swap back in a real index, assuming the index is temporary.
 *)
let reindex index trm =
  map_term_if
    (fun _ trm -> eq_constr trm (mkRel 0))
    (fun idx trm -> idx)
    shift
    index
    trm

(* --- Differencing and identifying indices --- *)

(*
 * Insert an index into a list of terms in the location index_i
 *)
let insert_index index_i index args =
  let (before, after) = take_split index_i args in
  List.append before (index :: after)

(*
 * Insert an index and shift the arguments before and after it by n
 *)
let insert_index_shift index_i index args n =
  let (before, after) = take_split index_i (shift_all_by n args) in
  List.append before (index :: after)

(*
 * Remove an index from a list of terms in the location index_i
 *)
let remove_index index_i args =
  let (before, after) = take_split index_i args in
  List.append before (List.tl after)

(*
 * Unshift arguments after index_i, since the index is no longer in
 * the hypotheses
 *)
let adjust_no_index index_i args =
  let (before, after) = take_split index_i args in
  List.append before (shift_all_by (- 1) after)

(*
 * Returns true if the argument at index i to property p is
 * an index in trm_n that was not an index in trm_o.
 *
 * In other words, this looks for applications of the property p
 * in the induction principle type, checks the argument at index i,
 * and determines whether they were equal. If they are ever not equal,
 * then the index is considered to be new.
 *)
let new_index i trm_o trm_n =
  let rec is_new_index p trm_o trm_n =
    match map_tuple kind_of_term (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       if applies p t_o && not (applies p t_n) then
         is_new_index p_b (shift trm_o) b_n
       else
         is_new_index p t_o t_n || is_new_index p_b b_o b_n
    | (App (_, _), App (_, _)) when applies p trm_o && applies p trm_n ->
       let args_o = List.rev (List.tl (List.rev (unfold_args trm_o))) in
       let args_n = List.rev (List.tl (List.rev (unfold_args trm_n))) in
       diff_arg
         i
         (mkApp (p, Array.of_list args_o))
         (mkApp (p, Array.of_list args_n))
    | _ ->
       false
  in is_new_index (mkRel 1) trm_o trm_n

(*
 * Returns true if the hypothesis i is used to compute the index at position
 * index_i in any application of a property p in the eliminator type trm.
 *)
let rec computes_index index_i p i trm =
  match kind_of_term trm with
  | Prod (n, t, b) ->
     let p_b = shift p in
     let i_b = shift i in
     if applies p t then
       contains_term i (get_arg index_i t) || computes_index index_i p_b i_b b
     else
       computes_index index_i p_b i_b b
  | App (_, _) ->
     contains_term i (get_arg index_i trm)
  | _ ->
     failwith "unexpected"

(*
 * Returns true if the hypothesis i is _only_ used to compute the index
 * at index_i, and is not used to compute any other indices
 *)
let computes_only_index env index_i p i trm =
  let indices = List.map unshift_i (from_one_to (arity (infer_type env p) - 1)) in
  if computes_index index_i p i trm then
    let indices_not_i = remove_index index_i indices in
    List.for_all (fun j -> not (computes_index j p i trm)) indices_not_i
  else
    false

(*
 * Get the index type and location (index of the index).
 * This doesn't yet handle adding multiple indices.
 *
 * If indices depend on earlier types, the types may be dependent;
 * the client needs to shift by the appropriate offset.
 *)
let index_type env elim_t_o elim_t_n =
  let (_, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, b_n) = destProd elim_t_n in
  let rec poss_indices e p_o p_n =
    match map_tuple kind_of_term (p_o, p_n) with
    | (Prod (n_o, t_o, b_o), Prod (_, t_n, b_n)) ->
       if isProd b_o && convertible e t_o t_n then
         let e_b = push_local (n_o, t_o) e in
         let same = poss_indices e_b b_o b_n in
         let different = (0, t_n) in
         different :: (List.map (fun (i, i_t) -> (shift_i i, i_t)) same)
       else
         [(0, t_n)]
    | _ ->
       failwith "could not find indexer property"
  in List.find (fun (i, _) -> new_index i b_o b_n) (poss_indices env p_o p_n)

(*
 * Given an old and new application of a property, find the new index.
 * This also assumes there is only one new index.
 *)
let get_new_index index_i p o n =
  match map_tuple kind_of_term (o, n) with
  | (App (f_o, _), App (f_n, _)) when are_or_apply p f_o f_n ->
     get_arg index_i n
  | _ ->
     failwith "not an application of a property"

(* --- Search --- *)

(* Search two inductive types for a parameterizing ornament *)
let search_orn_params env (ind_o : inductive) (ind_n : inductive) is_fwd : types =
  failwith "parameterization is not yet supported"

(*
 * Get a single case for the indexer, given:
 * 1. index_i, the location of the new index in the property
 * 2. index_t, the type of the new index in the property
 * 3. o, the old environment, inductive type, and constructor
 * 4. n, the new environment, inductive type, and constructor
 *
 * Eventually, it would be good to make this logic less ad-hoc,
 * though the terms we are looking at here are type signatures of
 * induction principles, and so should be very predictable.
 *)
let index_case index_i p o n : types =
  let get_index = get_new_index index_i in
  let rec diff_case p_i p subs o n =
    let (e_o, ind_o, trm_o) = o in
    let (e_n, ind_n, trm_n) = n in
    match map_tuple kind_of_term (trm_o, trm_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       (* premises *)
       let p_b = shift p in
       let diff_b = diff_case (shift p_i) p_b in
       let e_n_b = push_local (n_n, t_n) e_n in
       let n_b = (e_n_b, shift ind_n, b_n) in
       let same = same_mod_indexing e_o p in
       let same_arity = arity b_o = arity b_n in
       let false_lead b_n = not same_arity && (computes_only_index e_n_b index_i p_b (mkRel 1)) b_n in
       if (not (same (ind_o, t_o) (ind_n, t_n))) || false_lead b_n then
         (* index *)
         let e_o_b = push_local (n_n, t_n) e_o in
         let subs_b = shift_subs subs in
         let o_b = (e_o_b, shift ind_o, shift trm_o) in
         unshift (diff_b subs_b o_b n_b)
       else
         let e_o_b = push_local (n_o, t_o) e_o in
         let o_b = (e_o_b, shift ind_o, b_o) in
         if apply p t_o t_n then
           (* inductive hypothesis *)
           let sub_index = (shift (get_index p t_o t_n), mkRel 1) in
           let subs_b = sub_index :: shift_subs subs in
           mkLambda (n_o, mkApp (p_i, Array.of_list (unfold_args t_o)), diff_b subs_b o_b n_b)
         else
           (* no change *)
           let subs_b = shift_subs subs in
           mkLambda (n_o, t_o, diff_b subs_b o_b n_b)
    | (App (f_o, _), App (f_n, _)) ->
       (* conclusion *)
       let index = get_index p trm_o trm_n in
       List.fold_right all_eq_substs subs index
    | _ ->
       failwith "unexpected case"
  in diff_case p (mkRel 1) [] o n

(* Get the cases for the indexer *)
let indexer_cases index_i p npm o n : types list =
  let (env_o, ind_o, arity_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elim_t_n) = n in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
  | (Prod (n_o, p_o, b_o), Prod (n_n, p_n, b_n)) ->
     let env_p_o = push_local (n_o, p_o) env_o in
     let env_p_n = push_local (n_n, p_n) env_n in
     let o c = (env_p_o, ind_o, c) in
     let n c = (env_p_n, ind_n, c) in
     List.map2
       (fun c_o c_n ->
         shift_by
           (arity_o - npm)
           (index_case index_i p (o c_o) (n c_n)))
       (take_except (arity_o - npm + 1) (deconstruct_product b_o))
       (take_except (arity_n - npm + 1) (deconstruct_product b_n))
  | _ ->
     failwith "not eliminators"

(* Search for an indexing function *)
let search_for_indexer index_i index_t npm elim_o o n is_fwd : types option =
  if is_fwd then
    let (env_o, _, arity_o, elim_t_o) = o in
    let (env_n, _, _, elim_t_n) = n in
    let index_t = shift_by npm index_t in
    match map_tuple kind_of_term (elim_t_o, elim_t_n) with
    | (Prod (_, p_o, b_o), Prod (_, p_n, b_n)) ->
       let env_ind = zoom_env zoom_product_type env_o p_o in
       let off = offset env_ind npm in
       let pms = shift_all_by (arity_o - npm + 1) (mk_n_rels npm) in
       let index_t_p = shift_by index_i index_t in
       let p = reconstruct_lambda_n env_ind index_t_p npm in
       let cs = indexer_cases index_i (shift p) npm o n in
       let final_args = Array.of_list (mk_n_rels off) in
       let p_elim = shift_by off p in
       Some (apply_eliminator_recons env_ind elim_o pms p_elim cs final_args)
    | _ ->
       failwith "not eliminators"
  else
    None

(* Find the property that the ornament proves *)
let ornament_p index_i env ind arity npm indexer_opt =
  let off = offset env npm in
  let off_args = off - (arity - npm) in
  let args = shift_all_by off_args (mk_n_rels arity) in
  let index_i_npm = npm + index_i in
  let concl =
    match indexer_opt with
    | Some indexer ->
       (* forward (indexing) direction *)
       let indexer = Option.get indexer_opt in
       let index = mkApp (indexer, Array.of_list (List.append args [mkRel 1])) in
       mkApp (ind, Array.of_list (insert_index index_i_npm index args))
    | None ->
       (* backward (deindexing) direction *)
       mkApp (ind, Array.of_list (adjust_no_index index_i_npm args))
  in shift_by off (reconstruct_lambda_n env concl npm)

(*
 * Stretch the old property type to match the new one
 * That is, add indices where they are missing in the old property
 * For now just supports one index
 *)
let rec stretch_property_type index_i env o n =
  let (ind_o, p_o) = o in
  let (ind_n, p_n) = n in
  match map_tuple kind_of_term (p_o, p_n) with
  | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
     let n_b = (shift ind_n, b_n) in
     if index_i = 0 then
       let env_b = push_local (n_n, t_n) env in
       let o_b = (shift ind_o, shift p_o) in
       mkProd (n_n, t_n, shift p_o)
     else
       let env_b = push_local (n_o, t_o) env in
       let o_b = (shift ind_o, b_o) in
       mkProd (n_o, t_o, stretch_property_type (index_i - 1) env_b o_b n_b)
  | _ ->
     p_o

(*
 * Stretch the old property to match the new one at the term level
 *
 * Hilariously, this function is defined as an ornamented
 * version of stretch_property_type.
 *)
let stretch_property index_i env o n =
  let (ind_o, p_o) = o in
  let o = (ind_o, lambda_to_prod p_o) in
  prod_to_lambda (stretch_property_type index_i env o n)

(*
 * Stretch out the old eliminator type to match the new one
 * That is, add indexes to the old one to match new
 *)
let stretch index_i env indexer pms o n =
  let (ind_o, elim_t_o) = o in
  let (ind_n, elim_t_n) = n in
  let (n_exp, p_o, b_o) = destProd elim_t_o in
  let (_, p_n, _) = destProd elim_t_n in
  let p_exp = stretch_property_type index_i env (ind_o, p_o) (ind_n, p_n) in
  let b_exp =
    map_term_if
      (fun (p, _) t -> applies p t)
      (fun (p, pms) t ->
        let non_pms = unfold_args t in
        let index = mkApp (indexer, Array.append pms (Array.of_list non_pms)) in
        mkApp (p, Array.of_list (insert_index index_i index non_pms)))
      (fun (p, pms) -> (shift p, Array.map shift pms))
      (mkRel 1, pms)
      b_o
  in mkProd (n_exp, p_exp, b_exp)

(*
 * Given terms that apply properties, update the
 * substitution list to include the corresponding new index
 *
 * This may be wrong for dependent indices (may need some kind of fold,
 * or the order may be incorrect). We'll need to see when we test that case.
 *)
let sub_index f_indexer subs o n =
  let (env_o, app_o) = o in
  let (env_n, app_n) = n in
  let (args_o, args_n) = map_tuple unfold_args (app_o, app_n) in
  let args = List.combine args_o args_n in
  let new_subs =
    List.map
      (fun (a_o, a_n) ->
        if applies f_indexer a_o then
          (* substitute the inductive hypothesis *)
          (shift a_n, shift a_o)
        else
          (* substitute the index *)
          (shift a_n, mkRel 1))
      (List.filter
         (fun (a_o, a_n) ->
           applies f_indexer a_o || not (same_type (env_o, a_o) (env_n, a_n)))
         args)
  in List.append new_subs subs

(* In the conclusion of each case, return c_n with c_o's indices *)
(* TODO clean again, see if any of these checks are redundant *)
let sub_indexes index_i is_fwd f_indexer p subs o n : types =
  let directional a b = if is_fwd then a else b in
  let rec sub p subs o n =
    let (env_o, ind_o, c_o) = o in
    let (env_n, ind_n, c_n) = n in
    match map_tuple kind_of_term (c_o, c_n) with
    | (Prod (n_o, t_o, b_o), Prod (n_n, t_n, b_n)) ->
       let p_b = shift p in
       let same = same_mod_indexing env_o p (ind_o, t_o) (ind_n, t_n) in
       let env_o_b = push_local (n_o, t_o) env_o in
       let env_n_b = push_local (n_n, t_n) env_n in
       let false_lead_fwd _ b_n = computes_only_index env_n_b index_i p_b (mkRel 1) b_n in
       let false_lead_bwd b_o _ = computes_only_index env_o_b index_i p_b (mkRel 1) b_o in
       let same_arity b_o b_n = (arity b_o = arity b_n) in
       let false_lead b_o b_n = (not (same_arity b_o b_n)) && (directional false_lead_fwd false_lead_bwd) b_o b_n in
       if applies p t_n || (same && not (false_lead b_o b_n)) then
         let o_b = (env_o_b, shift ind_o, b_o) in
         let n_b = (env_n_b, shift ind_n, b_n) in
         let subs_b = shift_subs subs in
         if applies p t_n then
           (* inductive hypothesis, get the index *)
           let subs_b = sub_index f_indexer subs_b (env_o, t_o) (env_n, t_n) in
           mkProd (n_o, t_o, sub p_b subs_b o_b n_b)
         else
           (* no index, keep recursing *)
           mkProd (n_o, t_o, sub p_b subs_b o_b n_b)
       else
         (* new hypothesis from which the index is computed *)
         let subs_b = directional (shift_to subs) (shift_from subs) in
         let new_index = directional (n_n, t_n) (n_o, t_o) in
         let (b_o_b, b_n_b) = directional (shift c_o, b_n) (b_o, shift c_n) in
         let env_o_b = push_local new_index env_o in
         let env_n_b = push_local new_index env_n in
         let o_b = (env_o_b, shift ind_o, b_o_b) in
         let n_b = (env_n_b, shift ind_n, b_n_b) in
         let subbed_b = sub p_b subs_b o_b n_b in
         directional (unshift subbed_b) (mkProd (n_o, t_o, subbed_b))
    | (App (f_o, args_o), App (f_n, args_n)) ->
       let args_n = List.rev (unfold_args c_n) in
       List.fold_right all_eq_substs subs (List.hd args_n)
    | _ ->
       failwith "unexpected case substituting index"
  in sub p subs o n

(*
 * Get a case for an indexing ornament.
 *
 * This currently works in the following way:
 * 1. If it's forwards, then adjust the property to have the index
 * 2. Substitute in the property to the old case
 * 3. Substitute in the indexes (or lack thereof, if backwards)
 *
 * Eventually, we might want to think of this as (or rewrite this to)
 * abstracting the indexed type to take an indexing function, then
 * deriving the result through specialization.
 *)
let orn_index_case index_i is_fwd indexer_f orn_p o n : types =
  let when_forward f a = if is_fwd then f a else a in
  let (env_o, arity_o, ind_o, _, c_o) = o in
  let (env_n, arity_n, ind_n, p_n, c_n) = n in
  let d_arity = arity_n - arity_o in
  let adjust p = stretch_property index_i env_o (ind_o, p) (ind_n, p_n) in
  let p_o = when_forward (fun p -> adjust (unshift_by d_arity p)) orn_p in
  let c_o = with_new_p (shift_by d_arity p_o) c_o in
  let o = (env_o, ind_o, c_o) in
  let n = (env_n, ind_n, c_n) in
  prod_to_lambda (sub_indexes index_i is_fwd indexer_f (mkRel 1) [] o n)

(* Get the cases for the ornament *)
let orn_index_cases index_i npm is_fwd indexer_f orn_p o n : types list =
  let (env_o, pind_o, arity_o, elim_t_o) = o in
  let (env_n, pind_n, arity_n, elim_t_n) = n in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
  | (Prod (_, p_o, b_o), Prod (_, p_n, b_n)) ->
     let o c = (env_o, arity_o, pind_o, p_o, c) in
     let n c = (env_n, arity_n, pind_n, p_n, c) in
     let arity = if is_fwd then arity_o else arity_n in
     List.map2
       (fun c_o c_n ->
         shift_by
           (arity - npm)
           (orn_index_case index_i is_fwd indexer_f orn_p (o c_o) (n c_n)))
       (take_except (arity_o - npm + 1) (deconstruct_product b_o))
       (take_except (arity_n - npm + 1) (deconstruct_product b_n))
  | _ ->
     failwith "not an eliminator"

(* Search two inductive types for an indexing ornament, using eliminators *)
let search_orn_index_elim npm idx_n elim_o o n is_fwd : (types option * types) =
  let directional a b = if is_fwd then a else b in
  let call_directional f a b = if is_fwd then f a b else f b a in
  let (env_o, ind_o, arity_o, elim_t_o) = o in
  let (env_n, ind_n, arity_n, elim_t_n) = n in
  let (index_i, index_t) = call_directional (index_type env_n) elim_t_o elim_t_n in
  let indexer = search_for_indexer index_i index_t npm elim_o o n is_fwd in
  let f_indexer = make_constant idx_n in
  let f_indexer_opt = directional (Some f_indexer) None in
  match map_tuple kind_of_term (elim_t_o, elim_t_n) with
  | (Prod (n_o, p_o, b_o), Prod (n_n, p_n, b_n)) ->
     let env_ornament = zoom_env zoom_product_type env_o p_o in
     let env_o_b = push_local (n_o, p_o) env_o in
     let env_n_b = push_local (n_n, p_n) env_n in
     let off = offset env_ornament npm in
     let pms = shift_all_by off (mk_n_rels npm) in
     let (ind, arity) = directional (ind_n, arity_o) (ind_n, arity_n) in
     let align_pms = Array.of_list (List.map (unshift_by (arity - npm)) pms) in
     let align = stretch index_i env_o f_indexer align_pms in
     let elim_t = call_directional align (ind_o, elim_t_o) (ind_n, elim_t_n) in
     let elim_t_o = directional elim_t elim_t_o in
     let elim_t_n = directional elim_t_n elim_t in
     let o = (env_o_b, ind_o, arity_o, elim_t_o) in
     let n = (env_n_b, ind_n, arity_n, elim_t_n) in
     let off_b = offset env_ornament (nb_rel env_o_b) - (arity - npm) in
     let p = ornament_p index_i env_ornament ind arity npm f_indexer_opt in
     let p_cs = unshift_by (arity - npm) p in
     let cs = shift_all_by off_b (orn_index_cases index_i npm is_fwd f_indexer p_cs o n) in
     let final_args = Array.of_list (mk_n_rels off) in
     let ornament = apply_eliminator_recons env_ornament elim_o pms p cs final_args in
     (indexer, ornament)
  | _ ->
     failwith "not eliminators"

(* Search two inductive types for an indexing ornament *)
let search_orn_index env npm idx_n o n is_fwd : (types option * types) =
  let (pind_o, arity_o) = o in
  let (pind_n, arity_n) = n in
  let (ind_o, _) = destInd pind_o in
  let (ind_n, _) = destInd pind_n in
  let (elim_o, elim_n) = map_tuple (type_eliminator env) (ind_o, ind_n) in
  let (elim_t_o, elim_t_n) = map_tuple (infer_type env) (elim_o, elim_n) in
  let (env_o, elim_t_o') = zoom_n_prod env npm elim_t_o in
  let (env_n, elim_t_n') = zoom_n_prod env npm elim_t_n in
  let o = (env_o, pind_o, arity_o, elim_t_o') in
  let n = (env_n, pind_n, arity_n, elim_t_n') in
  search_orn_index_elim npm idx_n elim_o o n is_fwd

(* Search two inductive types for an ornament between them *)
let search_orn_inductive (env : env) (idx_n : Id.t) (trm_o : types) (trm_n : types) : promotion =
  match map_tuple kind_of_term (trm_o, trm_n) with
  | (Ind ((i_o, ii_o), u_o), Ind ((i_n, ii_n), u_n)) ->
     let (m_o, m_n) = map_tuple (fun i -> lookup_mind i env) (i_o, i_n) in
     check_inductive_supported m_o;
     check_inductive_supported m_n;
     let (npm_o, npm_n) = map_tuple (fun m -> m.mind_nparams) (m_o, m_n) in
     if not (npm_o = npm_n) then
       (* new parameter *)
       let search_params = twice (search_orn_params env) in
       let indexer = None in
       if npm_o < npm_n then
         let (promote, forget) = search_params (i_o, ii_o) (i_n, ii_n) in
         { indexer; promote; forget }
       else
         let (promote, forget) = search_params (i_n, ii_n) (i_o, ii_o) in
         { indexer; promote; forget }
     else
       let npm = npm_o in
       let (typ_o, typ_n) = map_tuple (type_of_inductive env 0) (m_o, m_n) in
       let (arity_o, arity_n) = map_tuple arity (typ_o, typ_n) in
       if not (arity_o = arity_n) then
         let o = (trm_o, arity_o) in
         let n = (trm_n, arity_n) in
         let search_indices = twice (search_orn_index env npm idx_n) in
         if arity_o < arity_n then
           let ((indexer, promote), (_, forget)) = search_indices o n in
           { indexer; promote; forget }
         else
           let ((indexer, promote), (_, forget)) = search_indices n o in
           { indexer; promote; forget }
       else
         failwith "this kind of change is not yet supported"
  | _ ->
     failwith "this kind of change is not yet supported"

(* --- Application --- *)

(*
 * Substitute the ornamented type in the hypotheses.
 * Return both the term with ornamented hypotheses and the number
 * of substitutions that occurred.
 *)
let sub_in_hypos (index_i : int) (index_lam : types) (from_ind : types) (to_ind : types) (hypos : types) (is_fwd : bool) =
  map_term_if_lazy
    (fun _ trm ->
      match kind_of_term trm with
      | Lambda (_, t, _) -> is_or_applies from_ind t
      | _ -> false)
    (fun _ trm ->
      let (n, t, b) = destLambda trm in
      let args = unfold_args t in
      if is_fwd then
        let (before, after) = take_split index_i args in
        let index_type = reduce_term (mkApp (index_lam, Array.of_list before)) in
        let t_args = insert_index_shift index_i (mkRel 1) args 1 in
        let t_ind = mkApp (to_ind, Array.of_list t_args) in
        let sub_ind = all_eq_substs (mkRel 2, mkRel 1) in
        mkLambda (Anonymous, index_type, mkLambda (n, t_ind, sub_ind (shift b)))
      else
        let t_args = remove_index index_i args in
        let t_ind = mkApp (to_ind, Array.of_list t_args) in
        mkLambda (n, t_ind, b))
    (fun _ -> ())
    ()
    hypos

(*
 * Apply the ornament to the arguments
 * TODO clean this
 *)
let ornament_args env index_i (from_ind, to_ind) orn is_fwd (trm, indices) =
  let orn_f = if is_fwd then orn.forget else orn.promote in
  let indexer = Option.get orn.indexer in
  let (trm, _, indices) =
    List.fold_left
       (fun (trm, hypos, indices) i ->
         match kind_of_term hypos with
         | Lambda (n, t, b) ->
            let (_, _, h) = CRD.to_tuple @@ lookup_rel i env in
            if is_or_applies from_ind t then
              if is_fwd then
                let nind = List.length indices in
                let index = mkRel (i - nind) in
                let args = insert_index_shift index_i index (unfold_args t) i in
                let indexed = unshift index in
                let t_args = unfold_args t in
                let orn_app = mkApp (orn_f, Array.of_list (List.append args [indexed])) in
                let sub_index = (index, mkApp (indexer, Array.of_list (List.append (shift_all_by i t_args) [indexed]))) in
                (mkApp (trm, Array.make 1 orn_app), b, sub_index :: indices)
              else
                let index = shift_by i (get_arg index_i t) in
                let args = adjust_no_index index_i (shift_all_by i (unfold_args t)) in
                let orn_app = mkApp (orn_f, Array.of_list args) in
                let indexed = unshift index in
                let t_args = unfold_args t in
                let sub_index = (index, mkApp (indexer, Array.of_list (List.append (remove_index index_i (shift_all_by i t_args)) [indexed]))) in
                (mkApp (trm, Array.make 1 orn_app), b, sub_index :: indices)
            else if eq_constr h t then (* TODO test multi-nat-index case *)
              (mkApp (trm, Array.make 1 (mkRel i)), b, indices)
            else
              (trm, unshift b, indices)
         | _ ->
            (trm, hypos, indices))
       (trm, prod_to_lambda (reduce_type env trm), indices) (* TODO redundant *)
       (List.rev (all_rel_indexes env))
  in (trm, indices)

(* Ornament the hypotheses *)
let ornament_hypos env orn index_i (from_ind, to_ind) is_fwd (trm, indices) =
  let indexer = Option.get orn.indexer in
  let indexer_type = reduce_type env indexer in
  let index_lam = remove_final_hypo (prod_to_lambda indexer_type) in
  let hypos = prod_to_lambda (reduce_type env trm) in
  let subbed_hypos = sub_in_hypos index_i index_lam from_ind to_ind hypos is_fwd in
  let env_hypos = zoom_env zoom_lambda_term env subbed_hypos in
  let (concl, indices) = ornament_args env_hypos index_i (from_ind, to_ind) orn is_fwd (trm, indices) in
  if is_fwd then
    (reconstruct_lambda env_hypos concl, indices)
  else
    (* Will this error if the indexer is used elsewhere? *)
    let indexed = List.fold_right all_eq_substs indices concl in
    (reconstruct_lambda env_hypos indexed, indices)

(* Ornament the conclusion *)
let ornament_concls concl_typ env orn index_i (from_ind, to_ind) is_fwd (trm, indices) =
  if is_or_applies from_ind concl_typ then
    let (env_zoom, trm_zoom) = zoom_lambda_term env trm in
    if is_fwd then
      let args = shift_all_by (List.length indices) (unfold_args concl_typ) in
      let promote = mkApp (orn.promote, Array.of_list args) in
      let concl = mkApp (promote, Array.make 1 trm_zoom) in
      (reconstruct_lambda env_zoom concl, indices)
    else
      let args =
        List.map
          (fun a ->
            List.fold_right
              all_eq_substs
              indices
              (map_term_env_if (* TODO refactor these HOFs *)
                 (fun env _ trm ->
                   try
                     is_or_applies to_ind (reduce_type env trm)
                   with _ ->
                     false)
                 (fun env _ trm ->
                   let args = unfold_args (reduce_type env trm) in
                   mkApp (orn.promote, Array.of_list (List.append args [trm])))
                 (fun _ -> ())
                 env_zoom
                 ()
                 a))
          (unfold_args concl_typ)
      in
      let forget = mkApp (orn.forget, Array.of_list args) in
      let concl = mkApp (forget, Array.make 1 trm_zoom) in
      (reconstruct_lambda env_zoom concl, indices)
  else
    (trm, indices)

(*
 * Determine if the direction is forwards or backwards
 * True if forwards, false if backwards
 *)
let direction (env : env) (orn : types) : bool =
  let orn_type = reduce_type env orn in
  let (from_args, to_args) = map_tuple unfold_args (ind_of_orn orn_type) in
  List.length from_args < List.length to_args

(*
 * Apply an ornament, but don't reduce the result.
 *
 * Assumes indexing ornament for now
 *)
let ornament_no_red (env : env) (orn : types) (orn_inv : types) (trm : types) =
  let is_fwd = direction env orn in
  let reverse_if_bwd (a, b) = if is_fwd then (a, b) else reverse (a, b) in
  let (orn, orn_inv) = reverse_if_bwd (orn, orn_inv) in
  let orn_type = reduce_type env orn in
  let (from_with_args, to_with_args) = ind_of_orn orn_type in
  let from_args = unfold_args from_with_args in
  let to_args = unfold_args to_with_args in
  let to_args_idx = List.mapi (fun i t -> (i, t)) to_args in
  let (index_i, index) = List.find (fun (_, t) -> contains_term (mkRel 1) t) to_args_idx in
  let indexer = Some (fst (destApp index)) in
  let promote = orn in
  let forget = orn_inv in
  let orn = { indexer; promote; forget } in
  let (from_ind, to_ind) = reverse_if_bwd (map_tuple ind_of (from_with_args, to_with_args)) in
  let app_orn ornamenter = ornamenter env orn index_i (from_ind, to_ind) is_fwd in
  let (env_concl, concl_typ) = zoom_product_type env (reduce_type env trm) in
  let orn = fst (app_orn (ornament_concls concl_typ) (app_orn ornament_hypos (trm, []))) in
  if is_fwd then
    orn
  else
    remove_unused_hypos orn (* weakens guarantee but gives better result *)

(* --- Reduction --- *)

(*
 * Compose two properties for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * TODO else case right now assumes new index is first, but not necessarily
 * true, so need to fix accordingly. To know how to do that, need to test
 * with tree or something
 *)
let compose_p npms index_i orn p_g p_f is_fwd indexer =
  let orn_f = if is_fwd then orn.forget else orn.promote in
  let (env_p_f, p_f_body) = zoom_lambda_term empty_env p_f in
  let off = nb_rel env_p_f in
  let orn_app = mkApp (orn_f, Array.of_list (mk_n_rels (npms + off))) in
  let shift_pms_by = shift_local (npms + 1) in
  let body =
    if is_fwd then
      if Option.has_some indexer then
        let f_index = Option.get indexer in
        let index_pms = shift_all_by (npms + off) (mk_n_rels npms) in
        let index_nonpms = shift_all_by npms (mk_n_rels off) in
        let index_args = Array.of_list (List.append index_pms index_nonpms) in
        let index = mkApp (f_index, index_args) in
        let reindex ts = insert_index index_i index (remove_index index_i ts) in
        let (env_p_g, p_g_body) = zoom_lambda_term empty_env p_g in
        let p_g_f = first_fun p_g_body in
        let p_g_args = Array.of_list (reindex (unfold_args p_g_body)) in
        let p_g = reconstruct_lambda env_p_g (mkApp (p_g_f, p_g_args)) in
        shift_pms_by off (mkApp (p_g, Array.make 1 orn_app))
      else
        shift_pms_by off (mkApp (p_g, Array.make 1 orn_app))
    else
      let index = get_arg index_i p_f_body in
      shift_pms_by (off - 1) (mkApp (p_g, Array.of_list [index; orn_app]))
  in reconstruct_lambda env_p_f (reduce_term body)

(*
 * Compose the IH for a constructor
 * TODO should just get the new p and apply that
 *)
let compose_ih orn index_i indexer env_g npms_g ip_g p_g c_f is_fwd =
  let orn_f = if is_fwd then orn.forget else orn.promote in
  let ip_g_typ = reduce_type env_g ip_g in
  let from_typ = first_fun (fst (ind_of_orn ip_g_typ)) in
  map_term_env_if
    (fun _ _ trm -> is_or_applies from_typ trm)
    (fun en p_g trm ->
      let args = unfold_args trm in
      let (pms, non_pms) = map_tuple Array.of_list (take_split npms_g args) in
      let p_g = if is_fwd then p_g else unshift p_g in
      let orn_final = Array.make 1 (mkRel 1) in
      let orn_pms = mkApp (orn_f, pms) in
      if is_fwd then
        let (_, _, orn_final_typ) = CRD.to_tuple @@ lookup_rel 1 en in
        let typ_args = Array.of_list (unfold_args orn_final_typ) in
        let orn_idx = shift (Array.get typ_args index_i) in
        let orn_app = mkApp (mkApp (orn_pms, Array.make 1 orn_idx), non_pms) in
        let p_args = Array.make 1 (mkApp (orn_app, orn_final)) in
        if Option.has_some indexer then
          let f_index = Option.get indexer in
          let index_pms = mkApp (f_index, pms) in
          let index_indexed = mkApp (index_pms, Array.make 1 orn_idx) in
          let index = shift (mkApp (mkApp (index_indexed, non_pms), orn_final)) in
          let reindex ts = insert_index index_i index (remove_index index_i ts) in
          let (env_p_g, p_g_body) = zoom_lambda_term empty_env p_g in
          let p_g_f = first_fun p_g_body in
          let p_g_args = Array.of_list (reindex (unfold_args p_g_body)) in
          let p_g = reconstruct_lambda env_p_g (mkApp (p_g_f, p_g_args)) in
          reduce_term (mkApp (mkApp (p_g, non_pms), p_args))
        else
          reduce_term (mkApp (mkApp (p_g, non_pms), p_args))
      else
        let orn_app = mkApp (orn_pms, non_pms) in
        let p_args = Array.make 1 (mkApp (orn_app, orn_final)) in
        reduce_term (mkApp (mkApp (p_g, non_pms), p_args)))
    shift
    env_g
    p_g
    c_f

(*
 * Compose two constructors for two applications of an induction principle
 * that are structurally the same when one is an ornament.
 *
 * For now, this does not handle nested induction.
 *
 * TODO clean, refactor orn/deorn, take fewer arguments, etc.
 *)
let compose_c env_f env_g orn index_i f_indexer npms_g ip_g p_g is_fwd is_g is_indexer c_g c_f =
  let orn_f = if is_fwd then orn.forget else orn.promote in
  let orn_f_typ = reduce_type env_f orn_f in
  let to_typ = first_fun (fst (ind_of_orn orn_f_typ)) in
  let is_deorn = is_or_applies to_typ in
  let always_true _ = true in
  let c_f_used = get_used_or_p_hypos is_deorn c_f in
  let c_g_used = get_used_or_p_hypos always_true c_g in
  let c_f = compose_ih orn index_i f_indexer env_g npms_g ip_g p_g c_f is_fwd in
  let (env_f_body, f_body) = zoom_lambda_term env_f c_f in
  let off = nb_rel env_f_body - nb_rel env_f in
  if not is_g then
    let f = if is_fwd then shift_by off c_g else shift_by (off - 1) c_g in
    let c_used = if is_fwd then c_f_used else c_g_used in
    (* Does this generalize? *)
    let args =
      List.map
        (map_term_env_if
           (fun env _ trm ->
             is_deorn (reduce_type env trm))
           (fun env _ trm ->
             let args = unfold_args (reduce_type env trm) in
             mkApp (orn_f, Array.of_list (List.append args [trm])))
           (fun _ -> ())
           env_f_body
           ())
        c_used
    in
    let f_app = reduce_term (mkApp (f, Array.of_list args)) in
    reconstruct_lambda_n env_f_body f_app (nb_rel env_f)
  else if is_indexer then
    let f = Option.get orn.indexer in
    let f_body_typ = reduce_type env_f_body f_body in
    let (nsubs, f_body) =
      map_track
        map_term_if
        (fun _ trm -> applies orn_f trm)
        (fun _ trm -> get_arg index_i trm)
        (fun _ -> ())
        ()
        f_body
    in
    (* Does this generalize, too? *)
    if nsubs > 0 then
      reconstruct_lambda_n env_f_body f_body (nb_rel env_f)
    else
      let f_args = List.append (unfold_args f_body_typ) [f_body] in
      let f_app = Reductionops.nf_all env_f_body Evd.empty (mkApp (f, Array.of_list f_args)) in
      reconstruct_lambda_n env_f_body f_app (nb_rel env_f)
  else
    let f = if is_fwd then orn.promote else orn.forget in
    let f_body_typ = reduce_type env_f_body f_body in
    let (nsubs, f_body) =
      map_track
        map_term_if
        (fun _ trm -> applies orn_f trm)
        (fun _ trm -> List.hd (List.rev (unfold_args trm)))
        (fun _ -> ())
        ()
        f_body
    in
    (* Does this generalize, too? *)
    if nsubs > 0 then
      reconstruct_lambda_n env_f_body f_body (nb_rel env_f)
    else
      let args = List.append (unfold_args f_body_typ) [f_body] in
      let f_app = Reductionops.nf_all env_f_body Evd.empty (mkApp (f, Array.of_list args)) in
      reconstruct_lambda_n env_f_body f_app (nb_rel env_f)

(*
 * Compose two applications of an induction principle that are
 * structurally the same when one is an ornament.
 *
 * TODO clean
 *)
let compose_inductive idx_n index_i orn (env_g, g) (env_f, f) is_fwd is_g is_indexer =
  let (ip_f, pms_f, p_f, cs_f, args_f) = deconstruct_eliminator env_f f in
  let (ip_g, pms_g, p_g, cs_g, args_g) = deconstruct_eliminator env_g g in
  let ip = ip_f in
  let pms = pms_f in
  if is_g && not is_indexer then
    let indexer = Option.get orn.indexer in
    let (env_f_body, f_body) = zoom_lambda_term env_f f in
    let f_typ = reduce_type env_f_body f_body in
    let f_typ_args = unfold_args f_typ in
    let index_args = List.append f_typ_args [f_body] in
    let indexer = reconstruct_lambda env_f_body (mkApp (indexer, Array.of_list index_args)) in
    let f_indexer = Some (make_constant idx_n) in
    let p = compose_p (List.length pms) index_i orn p_g p_f is_fwd f_indexer in
    let npms_g = List.length pms_g in
    let cs = List.map2 (compose_c env_f env_g orn index_i f_indexer npms_g ip_g p_g is_fwd is_g is_indexer) cs_g cs_f in
    let args = args_f in
    (apply_eliminator ip pms p cs args, Some indexer)
  else if is_indexer then
    let p = compose_p (List.length pms) index_i orn p_g p_f is_fwd None in
    let npms_g = List.length pms_g in
    let cs = List.map2 (compose_c env_f env_g orn index_i None npms_g ip_g p_g is_fwd is_g is_indexer) cs_g cs_f in
    let args = args_f in
    (apply_eliminator ip pms p cs args, None)
  else
    let p = compose_p (List.length pms) index_i orn p_g p_f is_fwd None in
    let npms_g = List.length pms_g in
    let cs = List.map2 (compose_c env_f env_g orn index_i None npms_g ip_g p_g is_fwd is_g is_indexer) cs_g cs_f in
    let args = args_f in
    let app = apply_eliminator ip pms p cs args in
    (app, None)

(*
 * This takes a term (f o orn_inv) and reduces it to f' where orn_inv is
 * moved inside of the function.
 *
 * It assumes the term is in an easy-to-factor form (the form apply produces).
 * It also does not yet handle terms like append where the final result
 * is then ornamented. It also does not yet handle proofs like app_nil_r
 * where the type of the final result is no longer definable as-is.
 * It also does not yet handle any situations where f is not just an application
 * of the induction principle for the unornamented type. Basically,
 * this is a very preliminary attempt at solving this problem, which I
 * will build on.
 *
 * TODO: Ornamentation direction is fine, but deornamentation direction
 * is horrid. Indices complicate factoring. This problem may happen
 * for other types, so maybe we want a special factoring function
 * instead of all of this nonsense. We'll find out later when we try
 * to extend this, I guess.
 *)
let internalize (env : env) (idx_n : Id.t) (orn : types) (orn_inv : types) (trm : types) =
  let is_fwd = direction env orn in
  let apply_if b f x = if b then f x else x in
  let apply_if_bwd f x = apply_if (not is_fwd) f x in
  let (orn, orn_inv) =  apply_if_bwd reverse (orn, orn_inv) in
  let orn_type = reduce_type env orn in
  let (from_with_args, to_with_args) = ind_of_orn orn_type in
  let from_args = unfold_args from_with_args in
  let to_args = unfold_args to_with_args in
  let to_args_idx = List.mapi (fun i t -> (i, t)) to_args in
  let (index_i, index) = List.find (fun (_, t) -> contains_term (mkRel 1) t) to_args_idx in
  let indexer = Some (fst (destApp index)) in
  let promote = orn in
  let forget = orn_inv in
  let orn = { indexer; promote; forget } in
  let composite = apply_if_bwd (temporary_index orn) trm in
  let factors_dep = factor_term_dep env trm in (* TODO testing *)
  debug_factors_dep factors_dep;
  let delta env trm = Reductionops.whd_delta env Evd.empty trm in
  let reduce env trm = reduce_term (delta env trm) in
  let orn_indexer = Option.get orn.indexer in
  let (Factor ((env, base), children)) = factors_dep in
  let rec compose_factors fs =
    match fs with
    | Factor ((en, t), children) ->
       if List.length children > 0 then
         let children_comp = List.map compose_factors children in
         let ((t_app, indexer), env, composed) = List.hd (List.rev children_comp) in
         let (e_body, t_body) = zoom_lambda_term en t in
         debug_term env t_app "t_app";
         debug_term e_body t_body "t_body";
         let body_uses f = applies f t_body in
         let uses f = (applies f t_app || body_uses f) && isApp t_app in
         let promotes = uses orn.promote in
         let forgets = uses orn.forget in
         let indexes = uses orn_indexer in
         let branch a b c = if promotes then a else if forgets then b else c in
         let no_red = branch composed composed true in
         if promotes || forgets || indexes then
           let g = (e_body, reduce_term (delta e_body t_body)) in
           debug_term (fst g) (snd g) "g";
           debug_term env (reduce env t_app) "t_app reduced";
           let f = (env, apply_if (not no_red) (reduce env) t_app) in
           debug_term (fst f) (snd f) "f";
           let orn_f = branch orn.promote orn.forget orn_indexer in
           let is_g = applies orn_f t_body in
           (compose_inductive idx_n index_i orn g f is_fwd is_g indexes, env, true)
         else
           let x = 0 in debug_term en t_app "t_app";
           (((reduce_term (mkApp (shift t, Array.make 1 t_app))), indexer), env, composed)
       else
         ((t, None), en, false)
    | Unit ->
       failwith "unexpected"
  in
  let ((internalized, indexer), env, _) = compose_factors factors_dep in
  debug_term env internalized "internalized";
  (reconstruct_lambda env internalized, indexer)


(* --- Top-level --- *)

(* Identify an ornament *)
let find_ornament n d_old d_new =
  let (evm, env) = Lemmas.get_current_context () in
  let trm_o = unwrap_definition env (intern env evm d_old) in
  let trm_n = unwrap_definition env (intern env evm d_new) in
  if isInd trm_o && isInd trm_n then
    let idx_n = with_suffix n "index" in
    let orn = search_orn_inductive env idx_n trm_o trm_n in
    let idx = orn.indexer in
    (if Option.has_some idx then
       let _ = define_term idx_n env evm (Option.get idx) in
       Printf.printf "Defined indexing function %s.\n\n" (string_of_id idx_n);
     else
       ());
    define_term n env evm orn.promote;
    Printf.printf "Defined promotion %s.\n\n" (string_of_id n);
    let inv_n = with_suffix n "inv" in
    define_term inv_n env evm orn.forget;
    Printf.printf "Defined forgetful function %s.\n\n" (string_of_id inv_n);
    ()
  else
    failwith "Only inductive types are supported"

(* Apply an ornament, but don't reduce *)
let apply_ornament n d_orn d_orn_inv d_old =
  let (evm, env) = Lemmas.get_current_context () in
  let c_orn = intern env evm d_orn in
  let c_orn_inv = intern env evm d_orn_inv in
  let c_o = intern env evm d_old in
  let trm_n = ornament_no_red env c_orn c_orn_inv c_o in
  define_term n env evm trm_n;
  Printf.printf "Defined ornamented fuction %s.\n\n" (string_of_id n);
  ()

(* Reduce an application of an ornament *)
let reduce_ornament n d_orn d_orn_inv d_old =
  let (evm, env) = Lemmas.get_current_context () in
  let c_orn = intern env evm d_orn in
  let c_orn_inv = intern env evm d_orn_inv in
  let c_o = intern env evm d_old in
  let trm_o = unwrap_definition env c_o in
  let idx_n = with_suffix n "index" in
  let (trm_n, indexer) = internalize env idx_n c_orn c_orn_inv trm_o in
  (if Option.has_some indexer then
     let indexer_o = Option.get indexer in
     let (indexer_n, _) = internalize env idx_n c_orn c_orn_inv indexer_o in
     define_term idx_n env evm indexer_n;
     Printf.printf "Defined indexer %s.\n\n" (string_of_id idx_n)
   else
     ());
  define_term n env evm trm_n;
  Printf.printf "Defined reduced ornamened function %s.\n\n" (string_of_id n);
  ()

(* --- Commands --- *)

(* Identify an ornament given two inductive types *)
VERNAC COMMAND EXTEND FindOrnament CLASSIFIED AS SIDEFF
| [ "Find" "ornament" constr(d_old) constr(d_new) "as" ident(n)] ->
  [ find_ornament n d_old d_new ]
END

(*
 * Given an ornament and a function, derive the ornamented version that
 * doesn't internalize the ornament.
 *
 * This is equivalent to porting the hypotheses and conclusions we apply
 * the function to via the ornament, but not actually reducing the
 * result to get something of a useful type. It's the first step in
 * lifting functions, which will be chained eventually to lift
 * functions entirely.
 *)
VERNAC COMMAND EXTEND ApplyOrnament CLASSIFIED AS SIDEFF
| [ "Apply" "ornament" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ apply_ornament n d_orn d_orn_inv d_old ]
END

(*
 * Reduce an application of an ornament.
 *)
VERNAC COMMAND EXTEND ReduceOrnament CLASSIFIED AS SIDEFF
| [ "Reduce" "ornament" constr(d_orn) constr(d_orn_inv) "in" constr(d_old) "as" ident(n)] ->
  [ reduce_ornament n d_orn d_orn_inv d_old ]
END
