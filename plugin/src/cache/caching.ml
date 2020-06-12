open Constr
open Globnames
open Utilities
open Libobject
open Lib
open Promotion

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
  (global_reference * global_reference * global_reference) *
  (global_reference option)

let cache_lifting (_, (orns_and_trm, lifted_trm)) =
  LiftingsCache.add lift_cache orns_and_trm lifted_trm

let sub_lifting (subst, ((orn_o, orn_n, trm), lifted_trm)) =
  let orn_o, orn_n = map_tuple (subst_global_reference subst) (orn_o, orn_n) in
  let trm = subst_global_reference subst trm in
  let lifted_trm =
    if Option.has_some lifted_trm then
      Some (subst_global_reference subst (Option.get lifted_trm))
    else
      None
  in (orn_o, orn_n, trm), lifted_trm

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
let has_lifting_opt (orn_o, orn_n, trm) =
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
  if not (has_lifting_opt (orn_o, orn_n, trm)) then
    None
  else
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    let lifted_trm = LiftingsCache.find lift_cache (orn_o, orn_n, trm) in
    try
      Some (Universes.constr_of_global (Option.get lifted_trm))
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
    let lift_obj = inLifts ((orn_o, orn_n, trm), Some lifted_trm) in
    add_anonymous_leaf lift_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache lifting")

(* --- Opaque liftings --- *)

(* Initialize the opaque lifting cache *)
let opaque_lift_cache = LiftingsCache.create 100

(*
 * Wrapping the table for persistence
 *)
type opaque_lift_obj =
  (global_reference * global_reference * global_reference) * bool

let cache_opaque_lifting (_, (orns_and_trm, is_opaque)) =
  LiftingsCache.add opaque_lift_cache orns_and_trm is_opaque

let sub_opaque_lifting (subst, ((orn_o, orn_n, trm), is_opaque)) =
  let orn_o, orn_n = map_tuple (subst_global_reference subst) (orn_o, orn_n) in
  let trm = subst_global_reference subst trm in
  (orn_o, orn_n, trm), is_opaque

let inOpaqueLifts : opaque_lift_obj -> obj =
  declare_object { (default_object "OPAQUE_LIFTINGS") with
    cache_function = cache_opaque_lifting;
    load_function = (fun _ -> cache_opaque_lifting);
    open_function = (fun _ -> cache_opaque_lifting);
    classify_function = (fun opaque_obj -> Substitute opaque_obj);
    subst_function = sub_opaque_lifting }
              
(*
 * Check if there is an opaque lifting along an ornament for a given term
 *)
let has_opaque_lifting_bool (orn_o, orn_n, trm) =
  try
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    LiftingsCache.mem opaque_lift_cache (orn_o, orn_n, trm)
  with _ ->
    false

(*
 * Lookup an opaque lifting
 *)
let lookup_opaque (orn_o, orn_n, trm) =
  if has_opaque_lifting_bool (orn_o, orn_n, trm) then
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    LiftingsCache.find opaque_lift_cache (orn_o, orn_n, trm)
  else
    false

(*
 * Add an opaque lifting to the opaque lifting cache
 *)
let save_opaque (orn_o, orn_n, trm) =
  try
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    let opaque_lift_obj = inOpaqueLifts ((orn_o, orn_n, trm), true) in
    let lift_obj = inLifts ((orn_o, orn_n, trm), Some trm) in
    add_anonymous_leaf opaque_lift_obj;
    add_anonymous_leaf lift_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache opaque lifting")

(*
 * Remove an opaque lifting from the opaque lifting cache
 *)
let remove_opaque (orn_o, orn_n, trm) =
  try
    let orn_o, orn_n = map_tuple global_of_constr (orn_o, orn_n) in
    let trm = global_of_constr trm in
    let opaque_lift_obj = inOpaqueLifts ((orn_o, orn_n, trm), false) in
    let lift_obj = inLifts ((orn_o, orn_n, trm), None) in
    add_anonymous_leaf opaque_lift_obj;
    add_anonymous_leaf lift_obj
  with _ ->
    Feedback.msg_warning (Pp.str "Failed to cache opaque lifting")
                         
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
                         
(* --- Equivalence cache --- *)

(*
 * This is a persistent cache for equivalences
 * (for now all called ornaments because of legacy code---will change later)
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

type 'a metadata = (global_reference * global_reference) * 'a 

(* Initialize the ornament cache *)
let orn_cache = OrnamentsCache.create 100

(* Initialize the private cache of indexers for algebraic ornamnets *)
let indexer_cache = OrnamentsCache.create 100

(* Initialize the private cache of swap maps for swap ornamnets *)
let swap_cache = OrnamentsCache.create 100
                                      
(*
 * The kind of ornament is saved as an int, so this interprets it
 *)
let int_to_kind (i : int) globals =
  if i = 0 then
    let (indexer, off) = OrnamentsCache.find indexer_cache globals in
    let indexer = Universes.constr_of_global indexer in
    Algebraic (indexer, off)
  else if i = 1 then
    CurryRecord
  else if i = 2 then
    let swap_map = OrnamentsCache.find swap_cache globals in
    SwapConstruct swap_map
  else if i = 3 then
    UnpackSigma
  else if i = 4 then
    Custom
  else
    failwith "Unsupported kind of ornament passed to interpret_kind in caching"

let kind_to_int (k : kind_of_orn) =
  match k with
  | Algebraic _ ->
     0
  | CurryRecord ->
     1
  | SwapConstruct _ ->
     2
  | UnpackSigma ->
     3
  | Custom ->
     4

(*
 * Wrapping the table for persistence
 *)

type orn_obj = (global_reference * global_reference * int) metadata
type indexer_obj = (global_reference * int) metadata
type swap_obj = ((int * int) list) metadata

let cache_ornament (_, (typs, orns_and_kind)) =
  OrnamentsCache.add orn_cache typs orns_and_kind

let cache_indexer (_, (typs, indexer_and_off)) =
  OrnamentsCache.add indexer_cache typs indexer_and_off

let cache_swap_map (_, (typs, swap_map)) =
  OrnamentsCache.add swap_cache typs swap_map

let sub_ornament (subst, (typs, (orn_o, orn_n, kind))) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let orn_o, orn_n = map_tuple (subst_global_reference subst) (orn_o, orn_n) in
  typs, (orn_o, orn_n, kind)

let sub_indexer (subst, (typs, (indexer, off))) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let indexer = subst_global_reference subst indexer in
  typs, (indexer, off)

let sub_swap_map (subst, (typs, swap_map)) =
  let typs = map_tuple (subst_global_reference subst) typs in
  typs, swap_map

let inOrns : orn_obj -> obj =
  declare_object { (default_object "ORNAMENTS") with
    cache_function = cache_ornament;
    load_function = (fun _ -> cache_ornament);
    open_function = (fun _ -> cache_ornament);
    classify_function = (fun orn_obj -> Substitute orn_obj);
    subst_function = sub_ornament }

let inIndexers : indexer_obj -> obj =
  declare_object { (default_object "INDEXERS") with
    cache_function = cache_indexer;
    load_function = (fun _ -> cache_indexer);
    open_function = (fun _ -> cache_indexer);
    classify_function = (fun ind_obj -> Substitute ind_obj);
    subst_function = sub_indexer }

let inSwaps : swap_obj -> obj =
  declare_object { (default_object "SWAPS") with
    cache_function = cache_swap_map;
    load_function = (fun _ -> cache_swap_map);
    open_function = (fun _ -> cache_swap_map);
    classify_function = (fun ind_obj -> Substitute ind_obj);
    subst_function = sub_swap_map }             

(*
 * Precise version
 *)
let has_metadata_exact cache typs =
  try
    let globals = map_tuple global_of_constr typs in
    OrnamentsCache.mem cache globals
  with _ ->
    false
              
(*
 * Check if an ornament is cached
 *)
let has_metadata cache typs =
  if has_metadata_exact cache typs then
    true
  else
    has_metadata_exact cache (reverse typs)

(*
 * Lookup an ornament
 *)
let lookup_ornament typs =
  let typs = if has_metadata_exact orn_cache typs then typs else reverse typs in
  if not (has_metadata orn_cache typs) then
    None
  else
    let globals = map_tuple global_of_constr typs in
    let (orn, orn_inv, i) = OrnamentsCache.find orn_cache globals in
    try
      let orn, orn_inv = map_tuple Universes.constr_of_global (orn, orn_inv) in
      Some (orn, orn_inv, int_to_kind i globals)
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
    add_anonymous_leaf orn_obj;
    match kind with
    | Algebraic (indexer, off) ->
       let indexer = global_of_constr indexer in
       let ind_obj = inIndexers (globals, (indexer, off)) in
       add_anonymous_leaf ind_obj
    | SwapConstruct swap_map ->
       let ind_obj = inSwaps (globals, swap_map) in
       add_anonymous_leaf ind_obj
    | CurryRecord | UnpackSigma | Custom ->
       ()
  with _ ->
    Feedback.msg_warning
      (Pp.seq
         [Pp.str "Failed to cache equivalence. ";
          Pp.str "Please try definining your types as constants, ";
          Pp.str "and passing those constants to the command instead."])
 
                        
(* --- Lifting configuration cache --- *)

(*
 * This is a persistent cache for DepConstr, DepElim, IdEta, and RewEta
 *)

(* Initialize the config cache *)
let dep_constr_cache = OrnamentsCache.create 100
let dep_elim_cache = OrnamentsCache.create 100
let id_eta_cache = OrnamentsCache.create 100
let rew_eta_cache = OrnamentsCache.create 100
             
(*
 * Wrapping the table for persistence
 *)
type dep_constr_obj = (global_reference array * global_reference array) metadata
type dep_elim_obj = (global_reference * global_reference) metadata
type id_eta_obj = (global_reference * global_reference) metadata
type rew_eta_obj = (global_reference * global_reference) metadata

let cache_dep_constr (_, (typs, constrs)) =
  OrnamentsCache.add dep_constr_cache typs constrs

let cache_dep_elim (_, (typs, elims)) =
  OrnamentsCache.add dep_elim_cache typs elims

let cache_id_eta (_, (typs, ids)) =
  OrnamentsCache.add id_eta_cache typs ids

let cache_rew_eta (_, (typs, rews)) =
  OrnamentsCache.add rew_eta_cache typs rews

let sub_dep_constr (subst, (typs, (constrs_o, constrs_n))) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let constrs_o = Array.map (subst_global_reference subst) constrs_o in
  let constrs_n = Array.map (subst_global_reference subst) constrs_n in
  typs, (constrs_o, constrs_n)

let sub_dep_elim (subst, (typs, elims)) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let elims = map_tuple (subst_global_reference subst) elims in
  typs, elims

let sub_id_eta (subst, (typs, ids)) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let ids = map_tuple (subst_global_reference subst) ids in
  typs, ids

let sub_rew_eta (subst, (typs, rews)) =
  let typs = map_tuple (subst_global_reference subst) typs in
  let rews = map_tuple (subst_global_reference subst) rews in
  typs, rews

let inDepConstrs : dep_constr_obj -> obj =
  declare_object { (default_object "DEP_CONSTRS") with
    cache_function = cache_dep_constr;
    load_function = (fun _ -> cache_dep_constr);
    open_function = (fun _ -> cache_dep_constr);
    classify_function = (fun dep_constr_obj -> Substitute dep_constr_obj);
    subst_function = sub_dep_constr }

let inDepElims : dep_elim_obj -> obj =
  declare_object { (default_object "DEP_ELIMS") with
    cache_function = cache_dep_elim;
    load_function = (fun _ -> cache_dep_elim);
    open_function = (fun _ -> cache_dep_elim);
    classify_function = (fun dep_elim_obj -> Substitute dep_elim_obj);
    subst_function = sub_dep_elim }

let inIdEtas : id_eta_obj -> obj =
  declare_object { (default_object "ID_ETAS") with
    cache_function = cache_id_eta;
    load_function = (fun _ -> cache_id_eta);
    open_function = (fun _ -> cache_id_eta);
    classify_function = (fun id_eta_obj -> Substitute id_eta_obj);
    subst_function = sub_id_eta }

let inRewEtas : rew_eta_obj -> obj =
  declare_object { (default_object "REW_ETAS") with
    cache_function = cache_rew_eta;
    load_function = (fun _ -> cache_rew_eta);
    open_function = (fun _ -> cache_rew_eta);
    classify_function = (fun rew_eta_obj -> Substitute rew_eta_obj);
    subst_function = sub_rew_eta }

(*
 * Lookup a configuration
 * For now this just gets IdEta and ConstrEta, just so we can test to start
 *)
let lookup_config typs =
  if not (has_metadata_exact dep_constr_cache typs &&
          has_metadata_exact dep_elim_cache typs &&
          has_metadata_exact id_eta_cache typs &&
          has_metadata_exact rew_eta_cache typs) then
    None
  else
    let globals = map_tuple global_of_constr typs in
    let constrs = OrnamentsCache.find dep_constr_cache globals in
    let elims = OrnamentsCache.find dep_elim_cache globals in
    let ids = OrnamentsCache.find id_eta_cache globals in
    let rews = OrnamentsCache.find rew_eta_cache globals in
    try
      let constrs = map_tuple (Array.map Universes.constr_of_global) constrs in
      let elims = map_tuple Universes.constr_of_global elims in
      let ids = map_tuple Universes.constr_of_global ids in
      let rews = map_tuple Universes.constr_of_global rews in
      Some (constrs, elims, ids, rews)
    with _ ->
      Feedback.msg_warning
        (Pp.seq
           [Pp.str "Failed to retrieve cached configuration. ";
            Pp.str "Lifting may fail later. ";
            Pp.str "Please report a bug if this happens."]);
      None
 
(*
 * Add DepConstr to the config cache
 *)
let save_dep_constrs typs constrs =
  try
    let globals = map_tuple global_of_constr typs in
    let constrs = map_tuple (Array.map global_of_constr) constrs in
    let dep_constr_obj = inDepConstrs (globals, constrs) in
    add_anonymous_leaf dep_constr_obj
  with _ ->
    Feedback.msg_warning
      (Pp.seq
         [Pp.str "Failed to cache DepConstr configuration. ";
          Pp.str "Lifting may fail later. ";
          Pp.str "Please report a bug if this happens."])

(*
 * Add DepElim to the config cache
 *)
let save_dep_elim typs elims =
  try
    let globals = map_tuple global_of_constr typs in
    let elims = map_tuple global_of_constr elims in
    let dep_elim_obj = inDepElims (globals, elims) in
    add_anonymous_leaf dep_elim_obj
  with _ ->
    Feedback.msg_warning
      (Pp.seq
         [Pp.str "Failed to cache DepElim configuration. ";
          Pp.str "Lifting may fail later. ";
          Pp.str "Please report a bug if this happens."])

(*
 * Add IdEta to the config cache
 *)
let save_id_eta typs ids =
  try
    let globals = map_tuple global_of_constr typs in
    let ids = map_tuple global_of_constr ids in
    let id_eta_obj = inIdEtas (globals, ids) in
    add_anonymous_leaf id_eta_obj
  with _ ->
    Feedback.msg_warning
      (Pp.seq
         [Pp.str "Failed to cache IdEta configuration. ";
          Pp.str "Lifting may fail later. ";
          Pp.str "Please report a bug if this happens."])

(*
 * Add RewEta to the config cache
 *)
let save_rew_eta typs rews =
  try
    let globals = map_tuple global_of_constr typs in
    let rews = map_tuple global_of_constr rews in
    let rew_eta_obj = inRewEtas (globals, rews) in
    add_anonymous_leaf rew_eta_obj
  with _ ->
    Feedback.msg_warning
      (Pp.seq
         [Pp.str "Failed to cache RewEta configuration. ";
          Pp.str "Lifting may fail later. ";
          Pp.str "Please report a bug if this happens."])
