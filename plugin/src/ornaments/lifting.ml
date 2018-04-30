(*
 * Datatypes for promotions and lifting
 *)

open Utilities
open Term
open Environ
open Coqterms
open Zooming
open Promotions
open Hofs
open Constrexpr
open Globnames
open Constrextern
open Names
open Recordops
open Libnames
open Constrexpr_ops

(* --- Datatypes --- *)

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
    index_i : int option;
    indexer : types option;
    promote : types;
    forget : types;
  }

(*
 * A lifting is an ornamental promotion between types, a direction,
 * a hint whether it corresponds to an indexing function for an outer lifting,
 * and an optional indexer for the promoted function.
 *
 * I may add more things here later. This is just a convenient configuration
 * for promoting functions.
 *)
type lifting =
  {
    orn : promotion;
    is_fwd : bool;
    is_indexer : bool;
    lifted_indexer : types option;
  }

(*
 * A composition is a pair of functions and environments with
 * a corresponding lifting. It also contains a hint is_g, which says
 * whether lifting is applied to g or to f. This represents a single (factored)
 * applied but not simplified ornamentation.
 *)
type composition =
  {
    l : lifting;
    g : env * types;
    f : env * types;
    is_g : bool;
  }

(* --- Initialization --- *)

(* 
 * Unpack a promotion
 *)
let unpack_promotion env promotion =
  let (env_promotion, body) = zoom_lambda_term env promotion in
  reconstruct_lambda env_promotion (last (unfold_args body))
    
(*
 * Initialize a promotion
 *)
let initialize_promotion env evd promote forget =
  let promote_unpacked = unpack_promotion env (unwrap_definition env promote) in
  let to_ind = snd (on_type ind_of_promotion_type env evd promote_unpacked) in
  let to_args = unfold_args to_ind in
  let to_args_idx = List.mapi (fun i t -> (i, t)) to_args in
  let (index_i, index) = List.find (fun (_, t) -> contains_term (mkRel 1) t) to_args_idx in
  let index_i = Some index_i in
  let indexer = Some (first_fun index) in
  { index_i; indexer; promote; forget }

(*
 * Initialize a lifting
 *)
let initialize_lifting orn is_fwd =
  let lifted_indexer = None in
  let is_indexer = false in
  { orn ; is_fwd ; lifted_indexer ; is_indexer }

(* --- Control structures --- *)
    
(*
 * These two functions determine what function to use to go back to
 * an old type or get to a new type when lifting
 *)
let lift_back (l : lifting) = if l.is_fwd then l.orn.forget else l.orn.promote
let lift_to (l : lifting) = if l.is_fwd then l.orn.promote else l.orn.forget

(* Other control structures *)
let directional l a b = if l.is_fwd then a else b
let if_indexer l a b = if l.is_indexer then a else b
let map_directional f g l x = map_if_else f g l.is_fwd x
let map_indexer f g l x = map_if_else f g l.is_indexer x
let map_forward f l x = map_if f l.is_fwd x
let map_backward f l x = map_if f (not l.is_fwd) x
let map_if_indexer f l x = map_if f l.is_indexer x

(* --- Database of liftings for higher lifting --- *)

(*
 * This code is by Nate Yazdani, ported into this plugin
 * and renamed for consistency
 *)

(** Construct the external expression for a definition. *)
let expr_of_global (g : global_reference) : constr_expr =
  let r = extern_reference Loc.ghost Id.Set.empty g in
  CAppExpl (Loc.ghost, (None, r, None), [])

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
  mkRefC (extern_reference Loc.ghost Id.Set.empty global)

(** Build the identifier [X + "_lift"] to use as the name of the lifting instance
    for the definition [base] with name [M_1.M_2...M_n.X]. *)
let name_lifted (base : global_reference) : Id.t =
  let name = Nametab.basename_of_global base in
  Id.of_string (String.concat "_" [Id.to_string name; "lift"])

(** Build the identifier [X + "_red"] to use as the name of the reduced lifting
 instance for the definition [base] with name [M_1.M_2...M_n.X]. *)
let name_reduced (base : global_reference) : Id.t =
  let name = Nametab.basename_of_global base in
  Id.of_string (String.concat "_" [Id.to_string name; "red"])

(** Build an external expression for the lifting instance for the definition
    [base] given its lifted definition [lift]. *)
let make_lifted (base : global_reference) (lift : global_reference) : constr_expr =
  mkAppC (construct, [expr_of_global base; expr_of_global lift])

(** Register a canonical lifting for the definition [base] given its lifted
    definition [lift]. *)
let declare_lifted (base : types) (lift : types) : unit =
  let base = global_of_constr base in
  let lift = global_of_constr lift in
  let ident = name_lifted base in
  let package = make_lifted base lift in
  let hook = Lemmas.mk_hook (fun _ -> declare_canonical_structure) in
  Command.do_definition ident
    (Decl_kinds.Global, false, Decl_kinds.CanonicalStructure)
    None [] None package None hook

(** Register a canonical reduction for the lifted definition [lift] 
    given its reduced definition [red]. *)
let declare_reduced (lift : types) (red : types) : unit =
  let lift = global_of_constr lift in
  let red = global_of_constr red in
  let ident = name_reduced lift in
  let package = make_lifted lift red in
  let hook = Lemmas.mk_hook (fun _ -> declare_canonical_structure) in
  Command.do_definition ident
    (Decl_kinds.Global, false, Decl_kinds.CanonicalStructure)
    None [] None package None hook

(** Retrieve the canonical lifting for the definition [base]. *)
let search_canonical (env : env) (base : types) : types option =
  try
    let base = global_of_constr base in
    let (_, info) = lookup_canonical_conversion (project, Const_cs base) in
    (* Reduce the lifting instance to HNF to extract the target component. *)
    let package = Reduction.whd_all env info.o_DEF in
    let (cons, args) = Term.decompose_appvect package in
    Some (args.(3))
  with _ ->
    None

(** Retrieve the canonical lifting for the definition [base].
    Return the reduced version if it exists. *)
let search_lifted (env : env) (base : types) : types option =
  map_default
    (fun l -> map_default (fun r -> Some r) (Some l) (search_canonical env l))
    None
    (search_canonical env base)
 
