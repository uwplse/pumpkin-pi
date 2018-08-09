open Constr
open Environ
open Coqterms
open Constrexpr
open Constrextern
open Names
open Recordops
open Libnames
open Constrexpr_ops
open Decl_kinds
open Evd
open Globnames
open Utilities
open Libobject
open Lib
open Mod_subst
       
(* --- Database of liftings for higher lifting --- *)

(*
 * This code is by Nate Yazdani, ported into this plugin
 * and renamed for consistency
 *)

(** Record information of the lifting structure. *)
let structure : struc_typ =
  let ind = destIndRef (Nametab.locate (qualid_of_string "Ornamental.Lifted.t")) in
  lookup_structure ind

(** Base-term projection of the lifting structure. *)
let project : global_reference =
  Nametab.locate (qualid_of_string "Ornamental.Lifted.base")

(** Constructor of the lifting structure. *)
let construct : constr_expr =
  let global = ConstructRef structure.s_CONST in
  mkRefC (extern_reference Id.Set.empty global)

(** Build the identifier [X + "_lift"] to use as the name of the lifting instance
    for the definition [base] with name [M_1.M_2...M_n.X]. *)
let name_lifted (base : global_reference) : Id.t =
  let name = Nametab.basename_of_global base in
  Id.of_string (String.concat "_" [Id.to_string name; "lift"])

(** Build an external expression for the lifting instance for the definition
    [base] given its lifted definition [lift]. *)
let make_lifted (base : global_reference) (lift : global_reference) : constr_expr =
  mkAppC (construct, [expr_of_global base; expr_of_global lift])
         
(** Register a canonical lifting for the definition [base] given its lifted
    definition [lift]. *)
let declare_lifted (evm : evar_map) (base : types) (lift : types) : unit =
  let env = Global.env () in
  let base = global_of_constr base in
  let lift = global_of_constr lift in
  let n = name_lifted base in
  let package = make_lifted base lift in
  let hook = Lemmas.mk_hook (fun _ x -> declare_canonical_structure x; x) in
  let k = (Global, Flags.is_universe_polymorphism (), CanonicalStructure) in
  let udecl = Univdecls.default_univ_decl in
  let etrm = EConstr.of_constr (intern env evm package) in
  ignore (edeclare n k ~opaque:false evm udecl etrm None [] hook true)

(** Retrieve the canonical lifting for the definition [base]. *)
let search_lifted (env : env) (base : types) : types option =
  if isConst base then
    try
      let base = global_of_constr base in
      let (_, info) = lookup_canonical_conversion (project, Const_cs base) in
      (* Reduce the lifting instance to HNF to extract the target component. *)
      let package = Reduction.whd_all env info.o_DEF in
      let (cons, args) = decompose_appvect package in
      Some (args.(3))
    with _ ->
      None
  else
    None

(* --- Temporary cache of constants --- *)

(*
 * This cache handles any constants encountered while lifting an object.
 * It is purposely not persistent, and only lasts for a single lifting session.
 * Otherwise, we would clog the cache with many constants.
 *)

type temporary_cache = (KerName.t, types) Hashtbl.t

(*
 * Initialize the local cache
 *)
let initialize_local_cache () =
  Hashtbl.create 100

(*
 * Check whether a constant is in the local cache
 *)
let is_locally_cached c trm =
  match kind trm with
  | Const (co, u) ->
     Hashtbl.mem c (Constant.canonical co)
  | _ ->
     false
       
(*
 * Lookup a value in the local cache
 *)
let lookup_local_cache c trm =
  match kind trm with
  | Const (co, u) ->
     Hashtbl.find c (Constant.canonical co)
  | _ ->
     failwith "not cached"

(*
 * Add a value to the local cache
 *)
let cache_local c trm lifted =
  match kind trm with
  | Const (co, u) ->
     Hashtbl.add c (Constant.canonical co) lifted
  | _ ->
     failwith "can't cache a non-constant"

(* --- Ornaments cache --- *)

(*
 * This is a persistent cache for ornaments given the old and new kernames.
 *)

(* The persistent storage is backed by a normal hashtable *)
module OrnamentsCache =
  Hashtbl.Make
    (struct
      type t = (KerName.t * KerName.t)
      let equal =
        (fun (o, n) (o', n') ->
          KerName.equal o o' && KerName.equal n n')
      let hash =
        (fun (o, n) ->
          Hashset.Combine.combine (KerName.hash o) (KerName.hash n))
    end)

(* Initialize the ornament cache *)
let orn_cache = OrnamentsCache.create 100

(*
 * Wrapping the table for persistence
 *)
type orn_obj = (KerName.t * KerName.t) * global_reference

let cache_ornament (_, (typs, orn)) =
  OrnamentsCache.add orn_cache typs orn

let sub_ornament (subst, (typs, orn)) =
  (map_tuple (subst_kn subst) typs, subst_global_reference subst orn)
              
let inOrns : orn_obj -> obj  =
  declare_object { (default_object "ORNAMENTS") with
    cache_function = cache_ornament;
    load_function = (fun _ -> cache_ornament);
    open_function = (fun _ -> cache_ornament);
    classify_function = (fun (typs, orn) -> Substitute (typs, orn));
    subst_function = sub_ornament }
              
(*
 * Check if an ornament is cached
 *)
let has_ornament typs =
  match map_tuple kind typs with
  | (Ind ((m_o, _), _), Ind ((m_n, _), _)) ->
     let (kn_o, kn_n) = map_tuple MutInd.canonical (m_o, m_n) in
     let contains = OrnamentsCache.mem orn_cache in
     contains (kn_o, kn_n) && contains (kn_n, kn_o)
  | _ ->
     false
       
(*
 * Lookup an ornament
 *)
let lookup_ornament typs =
  if not (has_ornament typs) then
    failwith "cannot find ornament; please supply ornamental promotion yourself"
  else
    let (((m_o, _), _), ((m_n, _), _)) = map_tuple destInd typs in
    let (kn_o, kn_n) = map_tuple MutInd.canonical (m_o, m_n) in
    let lookup = OrnamentsCache.find orn_cache in
    (lookup (kn_o, kn_n), lookup (kn_n, kn_o))

(*
 * Add an ornament to the ornament cache
 *)
let save_ornament typs (orn, orn_inv) =
  match map_tuple kind typs with
  | (Ind ((m_o, _), _), Ind ((m_n, _), _)) ->
     let (kn_o, kn_n) = map_tuple MutInd.canonical (m_o, m_n) in
     let orn_obj = inOrns ((kn_o, kn_n), orn) in
     let orn_inv_obj = inOrns ((kn_n, kn_o), orn_inv) in
     add_anonymous_leaf orn_obj;
     add_anonymous_leaf orn_inv_obj
  | _ ->
     failwith "can't cache a non-inductive type"

