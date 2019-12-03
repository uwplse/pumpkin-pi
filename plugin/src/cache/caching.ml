open Constr
open Names
open Recordops
open Libnames
open Globnames
open Utilities
open Libobject
open Lib
open Mod_subst
open Defutils
open Reducers
open Environ
open Declarations
open Names

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
  let sigma = Evd.from_env env in
  let sigma, construct_term = EConstr.fresh_global env sigma (construct_gref ()) in
  let sigma, base_term = EConstr.fresh_global env sigma base_gref in
  let sigma, base_type = Typing.type_of env sigma base_term in
  let sigma, lifted_term = EConstr.fresh_global env sigma lifted_gref in
  let sigma, lifted_type = Typing.type_of env sigma lifted_term in
  let packed_term =
    EConstr.mkApp
      (construct_term, [|base_type; lifted_type; base_term; lifted_term|])
  in
  let n = name_lifted base_gref in
  ignore (define_canonical n sigma (EConstr.to_constr sigma packed_term) true)

(** Retrieve the canonical lifting, as a term, for the global reference
    [base_gref]. *)
let search_lifted env sigma base_gref =
  try
    let (_, info) = lookup_canonical_conversion (project_gref (), Const_cs base_gref) in
    (* Reduce the lifting instance to HNF to extract the target component. *)
    let package = reduce_stateless whd env sigma info.o_DEF in
    let (cons, args) = decompose_appvect package in
    Some (args.(3))
  with _ ->
    None

(** Retrieve the canonical lifting, as a term, for the definition [base]. *)
let search_lifted_term env sigma base_term =
  try
    global_of_constr base_term |> search_lifted env sigma
  with Not_found -> None

(** Retrieve the canonical lifting, as a global reference, for the global
    reference [base_gref]. *)
let search_lifted env sigma base_gref =
  try
    search_lifted env sigma base_gref |> Option.map global_of_constr
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
      type t = (global_reference * global_reference)
      let equal =
        (fun (o, n) (o', n') ->
          eq_gr o o' && eq_gr n n')
      let hash =
        (fun (o, n) ->
          Hashset.Combine.combine
            (ExtRefOrdered.hash (TrueGlobal o))
            (ExtRefOrdered.hash (TrueGlobal n)))
    end)

(* Initialize the ornament cache *)
let orn_cache = OrnamentsCache.create 100

(*
 * The kind of ornament that is stored
 * TODO move this out since also used in lifting
 *)
type kind_of_orn = Algebraic | CurryRecord

(*
 * The kind of ornament is saved as an int, so this interprets it
 *)
let int_to_kind (i : int) =
  if i = 0 then
    Algebraic
  else if i = 1 then
    CurryRecord
  else
    failwith "Unsupported kind of ornament passed to interpret_kind in caching"

let kind_to_int (k : kind_of_orn) =
  match k with
  | Algebraic ->
     0
  | CurryRecord ->
     1
             
(*
 * Wrapping the table for persistence
 *)
type orn_obj =
  (global_reference * global_reference) * (global_reference * global_reference * int)

let cache_ornament (_, (typs, orns_and_kind)) =
  OrnamentsCache.add orn_cache typs orns_and_kind

let sub_ornament (subst, (typs, (orn_o, orn_n, kind))) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let orn_o, orn_n = map_tuple (subst_global_reference subst) (orn_o, orn_n) in
  typs, (orn_o, orn_n, kind)

let inOrns : orn_obj -> obj =
  declare_object { (default_object "ORNAMENTS") with
    cache_function = cache_ornament;
    load_function = (fun _ -> cache_ornament);
    open_function = (fun _ -> cache_ornament);
    classify_function = (fun orn_obj -> Substitute orn_obj);
    subst_function = sub_ornament }

(*
 * Precise version
 *)
let has_ornament_exact typs =
  try
    let globals = map_tuple global_of_constr typs in
    OrnamentsCache.mem orn_cache globals
  with _ ->
    false
              
(*
 * Check if an ornament is cached
 *)
let has_ornament typs =
  if has_ornament_exact typs then
    true
  else
    has_ornament_exact (reverse typs)

(*
 * Lookup an ornament
 *)
let lookup_ornament typs =
  let typs = if has_ornament_exact typs then typs else reverse typs in
  if not (has_ornament typs) then
    CErrors.user_err (Pp.str "Cannot find ornament; please supply ornamental promotion yourself")
  else
    let globals = map_tuple global_of_constr typs in
    let (orn, orn_inv, i) = OrnamentsCache.find orn_cache globals in
    try
      let orn, orn_inv = map_tuple Universes.constr_of_global (orn, orn_inv) in
      (orn, orn_inv, int_to_kind i)
    with _ ->
      failwith "Ornament is not in the current environment; please report a bug"

(*
 * Add an ornament to the ornament cache
 *)
let save_ornament typs (orn, orn_inv, kind) =
  try
    let globals = map_tuple global_of_constr typs in
    let orn, orn_inv = map_tuple global_of_constr (orn, orn_inv) in
    let orn_obj = inOrns (globals, (orn, orn_inv, kind_to_int kind)) in
    add_anonymous_leaf orn_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache ornament")
 

