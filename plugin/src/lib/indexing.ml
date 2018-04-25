(*
 * Dealing with arguments of applications for indexing inductive types
 *)

open Term
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
let with_dummy_index env f =
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
 * Returns the first inductive hypothesis in the constructor type typ
 * for which the hypothesis h is used to compute the index at position index_i
 *)
let rec index_ih index_i p h typ i =
  match kind_of_term typ with
  | Prod (n, t, b) ->
     let p_b = shift p in
     let i_b = shift h in
     if applies p t then
       if contains_term h (get_arg index_i t) then
         Some (mkRel i, t)
       else
         index_ih index_i p_b i_b b (i - 1)
     else
       index_ih index_i p_b i_b b (i - 1)
  | App (_, _) when applies p typ ->
     if contains_term h (get_arg index_i typ) then
       Some (mkRel i, typ)
     else
       None
  | _ ->
     None

(*
 * Returns true if the hypothesis i is used to compute the index at position
 * index_i in any application of a property p in the eliminator type typ.
 *)
let rec computes_index index_i p i typ =
  match kind_of_term typ with
  | Prod (n, t, b) ->
     let p_b = shift p in
     let i_b = shift i in
     if applies p t then
       contains_term i (get_arg index_i t) || computes_index index_i p_b i_b b
     else
       computes_index index_i p_b i_b b
  | App (_, _) when applies p typ ->
     contains_term i (get_arg index_i typ)
  | _ ->
     false

(*
 * Returns true if the hypothesis i is _only_ used to compute the index
 * at index_i, and is not used to compute any other indices or parameters
 *)
let computes_only_index env evd index_i p i typ =
  let p_arity = arity (infer_type env evd p) in
  let indices = List.map unshift_i (from_one_to (p_arity - 1)) in
  if computes_index index_i p i typ then
    let indices_not_i = remove_index index_i indices in
    List.for_all (fun j -> not (computes_index j p i typ)) indices_not_i
  else
    false
