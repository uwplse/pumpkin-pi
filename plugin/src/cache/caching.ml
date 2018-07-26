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
       
(* --- Database of liftings for higher lifting --- *)

(*
 * This code is by Nate Yazdani, ported into this plugin
 * and renamed for consistency
 *)

(** Construct the external expression for a definition. *)
let expr_of_global (g : global_reference) : constr_expr =
  let r = extern_reference Id.Set.empty g in
  CAst.make @@ (CAppExpl ((None, r, None), []))

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
  ignore (edeclare n k ~opaque:false evm udecl etrm None [] hook)

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
