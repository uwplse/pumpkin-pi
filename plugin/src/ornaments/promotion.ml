open Constr
open Declarations
open Stateutils
open Reducers
open Zooming
open Envutils
open Apputils
open Utilities
open Environ

(* --- Ornamental promotions --- *)

(*
 * The kind of ornament that is stored
 *)
type kind_of_orn =
  | Algebraic of constr * int
  | CurryRecord
  | SwapConstruct of (int * int) list
  | UnpackSigma
  | Custom of (types * types)
  | Setoid of ((types * types) * (types list * constr list * constr list))

(*
 * An ornamental promotion is a function from T1 -> T2,
 * a function from T2 -> T1, and a kind of ornament.
 *)
type promotion =
  {
    promote : types;
    forget : types;
    kind : kind_of_orn;
  }

(*
 * Get the swap map from the promotion or forgetful function, if one
 * is provided
 *)
let swap_map_of_promote_or_forget env a b promote_o forget_o =
  let trm_o_o = if Option.has_some promote_o then promote_o else forget_o in
  let f = Option.get trm_o_o in
  let ((i_o, ii_o), u_o) = destInd (if Option.has_some promote_o then a else b) in
  let m_o = lookup_mind i_o env in
  let b_o = m_o.mind_packets.(0) in
  let cs_o = b_o.mind_consnames in
  let ncons = Array.length cs_o in
  map_state
    (fun i sigma ->
      let c_o = mkConstructU (((i_o, ii_o), i), u_o) in
      let sigma, c_o_typ = reduce_type env sigma c_o in
      let env_c_o, c_o_typ = zoom_product_type env c_o_typ in
      let nargs = new_rels2 env_c_o env in
      let c_o_args = mk_n_rels nargs in
      let c_o_app = mkAppl (c_o, c_o_args) in
      let typ_args = unfold_args c_o_typ in
      let sigma, c_o_lifted = reduce_nf env_c_o sigma (mkAppl (f, snoc c_o_app typ_args)) in
      let swap = ((((i_o, ii_o), i), u_o), destConstruct (first_fun c_o_lifted)) in
      sigma, if Option.has_some promote_o then swap else reverse swap)
    (range 1 (ncons + 1))  
