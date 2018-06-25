
let group_by k p xs =
  let rec aux xs ys =
    match xs, ys with
    | (x :: xs), (y :: _) when p (k y) (k x) -> aux xs (x :: ys)
    | (x :: xs), _ -> List.rev ys :: aux xs [x]
    | [], _ -> List.rev ys :: []
  in
  aux xs []

let index_ord ?init:(i=0) cmp x xs =
  let leq x y = cmp x y <= 0 in
  let rec aux i = function
    | x' :: xs' -> if leq x x' then i else aux (i + 1) xs'
    | [] -> i
  in
  aux i xs

let member_ord cmp x xs =
  let rec aux = function
    | x' :: xs' -> let ord = cmp x x' in (ord <= 0) && (ord = 0 || aux xs')
    | [] -> false
  in
  aux xs

let converse p = fun x y -> not (p x y)

let decompose_prod term =
  let open Constr in
  let rec aux params body =
    match kind body with
    | Prod (_, param, body') ->
      aux (param :: params) body'
    | _ ->
      (CList.rev params, body)
  in
  aux [] term

(*
 * Check two terms [e1] and [e2] for syntactic equality, ignoring universe
 * instances and local references (i.e., [Rel] subterms).
 *)
let eq_constr_nounivs_norels e1 e2 =
  let open Constr in
  let ign_univs _ _ _ _ = true in
  let ign_sorts _ _ = true in
  let rec eq nbinds e1 e2 =
    match kind e1, kind e2 with
    | Rel i, Rel j ->
      (i > nbinds && j > nbinds) || i = j
    | Prod (_, t1, e1'), Prod (_, t2, e2') ->
      eq nbinds t1 t2 && eq (nbinds + 1) e1' e2'
    | Lambda (_, t1, e1'), Lambda (_, t2, e2') ->
      eq nbinds t1 t2 && eq (nbinds + 1) e1' e2'
    | LetIn (_, e1', t1, e1''), LetIn (_, e2', t2, e2'') ->
      eq nbinds e1' e2' && eq nbinds t1 t2 && eq (nbinds + 1) e1' e2'
    | Fix _, Fix _ ->
      invalid_arg "fixpoint expressions are unsuppored"
    | CoFix _, CoFix _ ->
      invalid_arg "cofixpoint expressions are unsuppored"
    | _, _ ->
      compare_head_gen ign_univs ign_sorts (fun _ -> eq nbinds) 0 e1 e2
  in
  eq 0 e1 e2

let free_rels e =
  let open Util in
  let open Constr in
  let rec aux nbinds term rels =
    match kind term with
    | Rel i ->
      if i < nbinds then rels else i :: rels
    | Cast (term', _, _) ->
      aux nbinds term' rels
    | Prod (_, param, body) ->
      rels |> aux (nbinds + 1) body |> aux nbinds param
    | Lambda (_, param, body) ->
      rels |> aux (nbinds + 1) body |> aux nbinds param
    | LetIn (_, let_term, let_type, body) ->
      rels |> aux (nbinds + 1) body |> aux nbinds let_type |> aux nbinds let_term
    | App (head, args) ->
      rels |> Array.fold_right (aux nbinds) args |> aux nbinds head
    | Proj (_, term) ->
      aux nbinds term rels
    | Case (info, discr, pred, branches) ->
      let open Inductiveops in
      let nvars = info.ci_cstr_ndecls in
      let nidcs = inductive_nrealdecls info.ci_ind in
      rels |> Array.fold_right2 (fun n -> aux (nbinds + n)) nvars branches |>
      aux (nbinds + nidcs) pred |> aux nbinds discr
    | Fix _ ->
      invalid_arg "fixpoint expressions are unsuppored"
    | CoFix _ ->
      invalid_arg "cofixpoint expressions are unsuppored"
    | _ -> rels
  in
  aux 0 e []

(*
 * An element [(k, m)], called an aligned segment, indicates that the next
 * [k + m] declarations, in the order of deBruijn indexing, is some mixture of
 * [k] inserted declarations and [m] matched declarations. An aligned segment
 * is called unambiguous when one of its components is zero (and is called
 * ambiguous otherwise). Similarly, an alignment in which every aligned segment
 * is unambiguous is itself called unambiguous (and is called ambiguous
 * otherwise).
 *)
type alignment = (int * int) list

let compact algn =
  let rec aux = function
    | (0, mat) :: segs -> aux_mat mat segs
    | (ins, 0) :: segs -> aux_ins ins segs
    | seg :: segs -> seg :: aux segs
    | [] -> []
  and aux_mat mat = function
    | (0, mat') :: segs -> aux_mat (mat + mat') segs
    | segs -> (0, mat) :: aux segs
  and aux_ins ins = function
    | (ins', 0) :: segs -> aux_ins (ins + ins') segs
    | segs -> (ins, 0) :: aux segs
  in
  aux algn

let join algn1 algn2 =
  let rec aux = function
    | (((ins1, mat1) as seg1) :: segs1'),
      (((ins2, mat2) as seg2) :: segs2') ->
      let ins', mat' = ins2 - ins1, mat2 - mat1 in
      if ins' = 0 && mat' = 0 then
        seg1 :: aux (segs1', segs2')
      else if ins' >= 0 && mat' >= 0 then
        seg1 :: aux (segs1', (ins', mat') :: segs2')
      else if ins' <= 0 && mat' <= 0 then
        seg2 :: aux ((-ins', -mat') :: segs1', segs2')
      else
        invalid_arg "inconsistent alignments"
    | segs1, [] -> segs1
    | [], segs2 -> segs2
  in
  compact (aux (algn1, algn2))

let align_rels idx_o idx_n len_o len_n term_o term_n =
  (* TODO: Factor out "re-positioning" *)
  let open Util in
  let rels_o = free_rels term_o in
  let rels_n = free_rels term_n in
  let bnd_o = len_o - idx_o in
  let bnd_n = len_n - idx_n in
  let seg0 = (idx_n - idx_o, idx_o) in
  let align_rels rel_o rel_n =
    if rel_o > rel_n then
      invalid_arg "incompatible types"
    else if rel_o < bnd_o && rel_n < bnd_n then
      [(rel_n - rel_o, rel_o)]
    else if rel_o - bnd_o <> rel_n - bnd_n then
      invalid_arg "incompatible types"
    else
      []
  in
  try
    Some (seg0 :: List.fold_left join [] (List.map2 align_rels rels_o rels_n))
  with Invalid_argument _ -> None

(*
 * Given two local contexts (of type [Context.Rel.t]) in which the first (the
 * "old" context) is effectively a subset of the second (the "new" context),
 * determine which declarations were inserted into the first to construct the
 * second. The answer is returned as a list of positions for the inserted
 * declarations, relative to the outermost declaration of the second (new)
 * context (i.e., context length - deBruijn index of relevant declaration).
 *
 * Assumptions:
 * 1. Both contexts share an outer environment, given by [env].
 * 2. Neither context contains local definitions (i.e., let definitions).
 * 3. Common declaration names are an appropriate way to disambiguate between
 *    multiple equally valid context alignments.
 *)
let align_decls env ctx_o ctx_n =
  let open Util in
  let open Context in
  let len_n = Rel.length ctx_n in
  let len_o = Rel.length ctx_o in
  let ndiff = len_n - len_o in
  let shift_nth idx e nth = Debruijn.shift_local (idx - nth) 1 e in
  let rec scan env idx_o idx_n ctx_o ctx_n algns =
    match ctx_n with
    | decl_n :: _ ->
      let repr = Rel.Declaration.get_type decl_n in
      let dissimilar decl =
        Rel.Declaration.get_type decl |> eq_constr_nounivs_norels repr |> not
      in
      let subctx_o, ctx_o' = List.split_when dissimilar ctx_o in
      let subctx_n, ctx_n' = List.split_when dissimilar ctx_n in
      if Rel.length subctx_o > Rel.length subctx_n then
        invalid_arg "type misalignment";
      (* 3. For each type group, in lockstep from innermost to outermost: *)
      (*    a. Check compatibility of each old type with the [ndiff] new types beginning at the same offset *)
      (*    b. Compute the set of index shifts necessary to align a new member with each compatible old member *)
      (*    c. Join the index shift sets for each consistent new/old member alignment *)
      (*    d. Join each such index shift set with the accumulated set, pointwise *)
      (* 4. If there is a unique index shift set remaining, return that as the alignment *)
      (* 5. Else, return the index shift set that matches the most identically named declarations *)
      ??
    | [] -> if List.empty ctx_o then [] else invalid_arg "type misalignment"
  in
  let lookup idx = Rel.Declaration.get_type (Rel.lookup idx ctx_n) in
  ??
