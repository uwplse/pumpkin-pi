open Lifting
open Apputils
open Promotion
open Constr
open Names

(*
 * If an element in the provided list matches the predicate,
 * return the element. Returns None if no element exists.
 * The evar map is threaded through calls to the predicate.
 *)
let rec find_assoc_list_state pred env l sigma =
  match l with
  | [] -> sigma, None
  | h :: t ->
     let sigma, result = pred env h sigma in
     if result then
       sigma, Some h
     else
       find_assoc_list_state pred env t sigma

(*
 * Given an association list l, returns the first (key, element) pair such that
 * key is convertible to trm.
 *)
let find_key_convertible_to env l sigma trm =
  let pred env t sigma = Convertibility.convertible env sigma (fst t) trm in
  find_assoc_list_state pred env l sigma

(* Find the equivalence relation associated with a type in the source setoid. *)
let find_eq_rel_for_source_type l env sigma typ =
  let kind = l.orn.kind in
  match kind with
  | Setoid (typs, (eq_types, eq_rels_a, _)) ->
     let rec get_as eq_types eq_rels acc1 acc2 =
       match eq_types, eq_rels with
       | h1 :: t1, h2 :: t2 ->
          if Option.has_some h2 then
            get_as t1 t2 (h1 :: acc1) ((fst (Option.get h2)) :: acc2)
          else
            get_as t1 t2 acc1 acc2
       | _ :: _, [] -> failwith "More types than eq_rels in Setoid lifting"
       | [], _ :: _ -> failwith "More eq_rels than types in Setoid lifting"
       | [], [] -> acc1, acc2 in
     let eq_types, eq_rels = get_as eq_types eq_rels_a [] [] in
     let rel_map = List.combine eq_types eq_rels in
     let sigma, found_rel = find_key_convertible_to env rel_map sigma typ in
     let eq_rel =
       match found_rel with
       | None -> mkAppl (Equtils.eq, [typ])
       | Some p -> snd p in
     sigma, eq_rel
  | _ -> failwith "Eq lifting unsupported outside of Setoid lifting"

(* Find the equivalence relation associated with a type in the target setoid. *)
let find_eq_rel_for_target_type l env sigma typ =
  let kind = l.orn.kind in
  match kind with
  | Setoid (typs, (eq_types, eq_rels_a, eq_rels_b)) ->
     let rec get_bs eq_types eq_rels acc1 acc2 =
       match eq_types, eq_rels with
       | h1 :: t1, h2 :: t2 ->
          if Option.has_some h2 then
            get_bs t1 t2 (h1 :: acc1) ((fst (Option.get h2)) :: acc2)
          else
            get_bs t1 t2 acc1 acc2
       | _ :: _, [] -> failwith "More types than eq_rels in Setoid lifting"
       | [], _ :: _ -> failwith "More eq_rels than types in Setoid lifting"
       | [], [] -> acc1, acc2 in
     let eq_types, eq_rels = get_bs eq_types eq_rels_b [] [] in
     let rel_map = List.combine eq_types eq_rels in
     let sigma, found_rel = find_key_convertible_to env rel_map sigma typ in
     let eq_rel =
       match found_rel with
       | None -> mkAppl (Equtils.eq, [typ])
       | Some p -> snd p in
     sigma, eq_rel
  | _ -> failwith "Eq lifting unsupported outside of Setoid lifting"

(* Find the type corresponding to trm if it is a registered equivalence relation in the source setoid. *)
let find_type_for_eq_rel_source_setoid l env sigma trm =
  let kind = l.orn.kind in
  match kind with
  | Setoid (typs, (eq_types, eq_rels_a, _)) ->
     let rec get_a sigma eq_types eq_rels =
       match eq_types, eq_rels with
       | h1 :: t1, h2 :: t2 ->
          if Option.has_some h2 then
            let eq_rel, _ = Option.get h2 in
            let sigma, b = Convertibility.convertible env sigma trm eq_rel in
            if b then
              sigma, Some h1
            else
              get_a sigma t1 t2
          else
            get_a sigma t1 t2
       | _ :: _, [] -> failwith "More types than eq_rels in Setoid lifting"
       | [], _ :: _ -> failwith "More eq_rels than types in Setoid lifting"
       | [], [] -> sigma, None in
     get_a sigma eq_types eq_rels_a
  | _ -> failwith "Eq lifting unsupported outside of Setoid lifting"  

(* Find the equivalence proof associated with a type in the source setoid. *)
let find_eq_proof_for_source_type l env sigma typ =
  let kind = l.orn.kind in
  match kind with
  | Setoid (typs, (eq_types, eq_rels_a, _)) ->
     let rec get_as eq_types eq_rels acc1 acc2 =
       match eq_types, eq_rels with
       | h1 :: t1, h2 :: t2 ->
          if Option.has_some h2 then
            get_as t1 t2 (h1 :: acc1) ((snd (Option.get h2)) :: acc2)
          else
            get_as t1 t2 acc1 acc2
       | _ :: _, [] -> failwith "More types than eq_rels in Setoid lifting"
       | [], _ :: _ -> failwith "More eq_rels than types in Setoid lifting"
       | [], [] -> acc1, acc2 in
     let eq_types, eq_proofs = get_as eq_types eq_rels_a [] [] in
     let rel_map = List.combine eq_types eq_proofs in
     let sigma, found_proof = find_key_convertible_to env rel_map sigma typ in
     let eq_proof =
       match found_proof with
       | None -> mkAppl (Equivutils.eq_equivalence, [typ])
       | Some p -> snd p in
     sigma, eq_proof
  | _ -> failwith "Eq lifting unsupported outside of Setoid lifting"

(* Find the equivalence proof associated with a type in the target setoid. *)
let find_eq_proof_for_target_type l env sigma typ =
  let kind = l.orn.kind in
  match kind with
  | Setoid (typs, (eq_types, _, eq_rels_b)) ->
     let rec get_bs eq_types eq_rels acc1 acc2 =
       match eq_types, eq_rels with
       | h1 :: t1, h2 :: t2 ->
          if Option.has_some h2 then
            get_bs t1 t2 (h1 :: acc1) ((snd (Option.get h2)) :: acc2)
          else
            get_bs t1 t2 acc1 acc2
       | _ :: _, [] -> failwith "More types than eq_rels in Setoid lifting"
       | [], _ :: _ -> failwith "More eq_rels than types in Setoid lifting"
       | [], [] -> acc1, acc2 in
     let eq_types, eq_proofs = get_bs eq_types eq_rels_b [] [] in
     let rel_map = List.combine eq_types eq_proofs in
     let sigma, found_proof = find_key_convertible_to env rel_map sigma typ in
     let eq_proof =
       match found_proof with
       | None -> mkAppl (Equivutils.eq_equivalence, [typ])
       | Some p -> snd p in
     sigma, eq_proof
  | _ -> failwith "Eq lifting unsupported outside of Setoid lifting"

let setoid_defs_path =
  ModPath.MPfile
    (DirPath.make (List.map Id.of_string ["SetoidDefs" ; "Ornamental"]))

let start_rewrite_annotation = 
  mkConst (Constant.make2 setoid_defs_path (Label.make "START_REWRITE"))

let rewrite_tactic_from_id id =
  let s = Pp.str ("rewrite " ^ (Names.Id.to_string id)) in
  let s' = Format.asprintf "%a" Pp.pp_with s in
  Decompiler.parse_tac_str s'

let setoid_rewrite_tactic_from_id id =
  let s = Pp.str ("setoid_rewrite " ^ (Names.Id.to_string id)) in
  let s' = Format.asprintf "%a" Pp.pp_with s in
  Decompiler.parse_tac_str s'
