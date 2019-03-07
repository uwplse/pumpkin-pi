(*
 * Dealing with arguments of applications for indexing inductive types
 *)

open Constr
open Utilities
open Debruijn
open Coqterms
open Hofs

(* --- Generic functions --- *)

(*
 * Insert an index into a list of terms in the location index_i
 *)
let insert_index index_i index args =
  let (before, after) = take_split index_i args in
  List.append before (index :: after)

(*
 * Remove an index from a list of terms in the location index_i
 *)
let remove_index index_i args =
  let (before, after) = take_split index_i args in
  List.append before (List.tl after)

(*
 * Insert an index where an old index was
 *)
let reindex index_i index args =
  insert_index index_i index (remove_index index_i args)

(*
 * Reindex using a reindexer, but for an application
 *)
let reindex_app reindexer app =
  mkAppl (first_fun app, reindexer (unfold_args app))

(*
 * Reindex the body of a lambda
 *)
let reindex_body reindexer lam =
  let (n, t, b) = destLambda lam in
  mkLambda (n, t, reindexer b)

(*
 * Apply the term to a dummy index, when we would like the other arguments,
 * but we are not sure if the term is a lambda or curried
 *)
let dummy_index env f =
  reduce_term env (mkAppl (f, [mkRel 0]))

(* --- Managing inductive property arguments --- *)

(*
 * Unshift arguments after index_i, since the index is no longer in
 * the hypotheses
 *)
let adjust_no_index index_i args =
  let (before, after) = take_split index_i args in
  List.append before (unshift_all after)

(*
 * Returns true if the hypothesis i is used to compute the index at position
 * off in any application of the property p in some inductive hypothesis
 * of the eliminator type typ
 *)
let rec computes_ih_index off p i typ =
  match kind typ with
  | Prod (n, t, b) ->
     let p_b = shift p in
     let i_b = shift i in
     if applies p t then
       let index = get_arg off t in
       contains_term i index || computes_ih_index off p_b i_b b
     else
       computes_ih_index off p_b i_b b
  | _ ->
     false
                 
(* --- Getting arguments to indexed types --- *)

(*
 * Given a type we are promoting to/forgetting from,
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
let non_index_args index_i env typ =
  let typ = reduce_nf env typ in
  if is_or_applies sigT typ then
    let packer = (dest_sigT typ).packer in
    remove_index index_i (unfold_args (dummy_index env packer))
  else
    unfold_args typ

(*
 * Given a term with the type we are promoting to/forgetting from,
 * get all of the arguments to that type that aren't the new/forgotten index
 *)
let non_index_typ_args index_i env evd trm =
  if is_or_applies existT trm then
    (* don't bother type-checking *)
    let packer = (dest_existT trm).packer in
    remove_index index_i (unfold_args (dummy_index env packer))
  else
    on_type (non_index_args index_i env) env evd trm
