(*
 * These are the produtils from the library, but extended to automatically
 * also preprocess rather than produce terms with match statements
 *)

open Constr
open Produtils

(* --- Constants --- *)

(*
 * These are unchanged
 *)
val prod : types
val pair : constr
val prod_rect : constr

(*
 * These are changed to use eliminators rather than match statements
 *)
val fst_elim : unit -> constr
val snd_elim : unit -> constr

(* --- Representations --- *)

(*
 * These are unchanged
 *)
val apply_pair : pair_app -> constr
val dest_pair : constr -> pair_app
val apply_prod : prod_app -> types
val dest_prod : types -> prod_app
val elim_prod : prod_elim -> constr
val dest_prod_elim : constr -> prod_elim

(*
 * These are changed to use eliminators rather than match statements
 *)
val prod_fst_elim : prod_app -> constr -> constr
val prod_snd_elim : prod_app -> constr -> constr
val prod_projections_elim : prod_app -> constr -> constr * constr

(* --- Extra utilities --- *)

val prod_typs : prod_app -> (types * types)
val eta_prod_rec : constr -> types -> constr
