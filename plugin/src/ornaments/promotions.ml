(*
 * Ornamental promotion/forgetful functions
 *)

open Term

(* 
 * Given the type of an ornamental promotion function, get the inductive types
 * that the function maps between, including all of their arguments 
 *)
let rec ind_of_promotion_type (typ : types) : types * types =
  match kind_of_term typ with
  | Prod (n, t, b) when isProd b ->
     ind_of_promotion_type b
  | Prod (n, t, b) ->
     (t, b)
  | _ ->
     failwith "not an ornamental promotion/forgetful function type"
