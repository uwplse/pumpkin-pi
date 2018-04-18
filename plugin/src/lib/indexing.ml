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
