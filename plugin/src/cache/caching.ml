open Constr
open Names
open Recordops
open Libnames
open Decl_kinds
open Globnames
open Utilities
open Libobject
open Lib
open Mod_subst
open Defutils

(* --- Database of liftings for higher lifting --- *)

(*
 * This code is by Nate Yazdani, ported into this plugin
 * and renamed for consistency
 *)

(** Record information of the lifting structure. *)
let structure () : struc_typ =
  try
    qualid_of_string "Ornamental.Lifted.t" |> Nametab.locate |>
      destIndRef |> lookup_structure
  with Not_found ->
    failwith "Error loading cache"

(** Constructor of the lifting structure. *)
let construct_gref () = ConstructRef (structure ()).s_CONST

(** Base-term projection of the lifting structure. *)
let project_gref () = Nametab.locate (qualid_of_string "Ornamental.Lifted.base")

(** Build the identifier [X + "_lift"] to use as the name of the lifting instance
    for the definition [base] with name [M_1.M_2...M_n.X]. *)
let name_lifted (base : global_reference) : Id.t =
  let name = Nametab.basename_of_global base in
  Id.of_string (String.concat "_" [Id.to_string name; "lift"])

(** Register a canonical lifting for the global reference [base_gref] given its
    lifted global reference [lifted_gref]. *)
let declare_lifted base_gref lifted_gref =
  let env = Global.env () in
  let evm = Evd.from_env env in
  let evm, construct_term = EConstr.fresh_global env evm (construct_gref ()) in
  let evm, base_term = EConstr.fresh_global env evm base_gref in
  let evm, base_type = Typing.type_of env evm base_term in
  let evm, lifted_term = EConstr.fresh_global env evm lifted_gref in
  let evm, lifted_type = Typing.type_of env evm lifted_term in
  let packed_term =
    EConstr.mkApp
      (construct_term, [|base_type; lifted_type; base_term; lifted_term|])
  in
  let n = name_lifted base_gref in
  ignore (define_canonical n evm (EConstr.to_constr evm packed_term) true) (* TODO extra conv. *) 

(** Retrieve the canonical lifting, as a term, for the global reference
    [base_gref]. *)
let search_lifted env base_gref =
  try
    let (_, info) = lookup_canonical_conversion (project_gref (), Const_cs base_gref) in
    (* Reduce the lifting instance to HNF to extract the target component. *)
    let package = Reduction.whd_all env info.o_DEF in
    let (cons, args) = decompose_appvect package in
    Some (args.(3))
  with _ ->
    None

(** Retrieve the canonical lifting, as a term, for the definition [base]. *)
let search_lifted_term env base_term =
  try
    global_of_constr base_term |> search_lifted env
  with Not_found -> None

(** Retrieve the canonical lifting, as a global reference, for the global
    reference [base_gref]. *)
let search_lifted env base_gref =
  try
    search_lifted env base_gref |> Option.map global_of_constr
  with Not_found ->
    (* A canonical lifting should always relate constant to constant,
       inductive to inductive, etc., so both components should always be
       representable as global references. *)
    CErrors.user_err (Pp.str "Found illegal canonical lifting.\n")

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
