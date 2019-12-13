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
 * This is a persistent cache for liftings
 *)

(* The persistent storage is backed by a normal hashtable *)
module LiftingsCache =
  Hashtbl.Make
    (struct
      type t = (global_reference * global_reference * global_reference)
      let equal =
        (fun (o, n, t) (o', n', t') ->
          eq_gr o o' && eq_gr n n' && eq_gr t t')
      let hash =
        (fun (o, n, t) ->
          Hashset.Combine.combine
            (Hashset.Combine.combine
               (ExtRefOrdered.hash (TrueGlobal o))
               (ExtRefOrdered.hash (TrueGlobal n)))
            (ExtRefOrdered.hash (TrueGlobal t)))
    end)

(* Initialize the lifting cache *)
let lift_cache = LiftingsCache.create 100
             
(*
 * Wrapping the table for persistence
 *)
type lift_obj =
  (global_reference * global_reference * global_reference) * global_reference

let cache_lifting (_, (orns_and_trm, lifted_trm)) =
  LiftingsCache.add lift_cache orns_and_trm lifted_trm

let sub_lifting (subst, ((orn_o, orn_n, trm), lifted_trm)) =
  let orn_o, orn_n = map_tuple (subst_global_reference subst) (orn_o, orn_n) in
  let trm = subst_global_reference subst trm in
  let lifted_trm = subst_global_reference subst lifted_trm in
  (orn_o, orn_n, trm), lifted_trm

let inLifts : lift_obj -> obj =
  declare_object { (default_object "LIFTINGS") with
    cache_function = cache_lifting;
    load_function = (fun _ -> cache_lifting);
    open_function = (fun _ -> cache_lifting);
    classify_function = (fun orn_obj -> Substitute orn_obj);
    subst_function = sub_lifting }
              
(*
 * Check if there is a lifting along an ornament for a given term
 *)
let has_lifting (orn_o, orn_n, trm) =
  try
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    LiftingsCache.mem lift_cache (orn_o, orn_n, trm)
  with _ ->
    false

(*
 * Lookup a lifting
 *)
let lookup_lifting (orn_o, orn_n, trm) =
  if not (has_lifting (orn_o, orn_n, trm)) then
    None
  else
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    let lifted_trm = LiftingsCache.find lift_cache (orn_o, orn_n, trm) in
    try
      Some (Universes.constr_of_global lifted_trm)
    with _ ->
      None

(*
 * Add a lifting to the lifting cache
 *)
let save_lifting (orn_o, orn_n, trm) lifted_trm =
  try
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    let lifted_trm = global_of_constr lifted_trm in
    let lift_obj = inLifts ((orn_o, orn_n, trm), lifted_trm) in
    add_anonymous_leaf lift_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache lifting")

(* --- Temporary cache of constants --- *)

(*
 * This cache handles any constants encountered while lifting an object.
 * It is purposely not persistent, and only lasts for a single lifting session.
 * Otherwise, we would clog the cache with many constants.
 *)

type temporary_cache = (global_reference, types) Hashtbl.t

(*
 * Initialize the local cache
 *)
let initialize_local_cache () =
  Hashtbl.create 100

(*
 * Check whether a constant is in the local cache
 *)
let is_locally_cached c trm =
  try
    let gr = global_of_constr trm in
    Hashtbl.mem c gr
  with _ ->
    false

(*
 * Lookup a value in the local cache
 *)
let lookup_local_cache c trm =
  try
    let gr = global_of_constr trm in
    Hashtbl.find c gr
  with _ ->
    failwith "not cached"

(*
 * Add a value to the local cache
 *)
let cache_local c trm lifted =
  try
    let gr = global_of_constr trm in
    Hashtbl.add c gr lifted
  with _ ->
    Feedback.msg_warning (Pp.str "can't cache term")

(* --- Ornaments cache --- *)

(*
 * This is a persistent cache for ornaments
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
    None
  else
    let globals = map_tuple global_of_constr typs in
    let (orn, orn_inv, i) = OrnamentsCache.find orn_cache globals in
    try
      let orn, orn_inv = map_tuple Universes.constr_of_global (orn, orn_inv) in
      Some (orn, orn_inv, int_to_kind i)
    with _ ->
      None
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
 

