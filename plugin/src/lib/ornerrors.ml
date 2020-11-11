open Utilities
open CErrors
open Himsg
open Constr

(* 
 * Errors and error messages
 *)

(* --- Exceptions --- *)

exception NotEliminators
exception NotInductive
exception NotAlgebraic

(* --- Error descriptions --- *)

let err_unsupported_change = Pp.str "Change not yet supported."

let err_name_inference =
  Pp.str "Could not automatically determine name for new ornament."

let err_new_parameter = Pp.str "New parameters not yet supported."

let err_new_constructor = Pp.str "New constructors not yet supported."

let err_save_ornament = Pp.str "Failed to save ornament."

let err_unexpected_change expected_kind =
  Pp.seq
    [Pp.str "CARROT expected an ";
     Pp.str expected_kind;
     Pp.str "."]

let err_opaque_not_constant qid =
  Pp.seq
    [Pp.str "The identifier ";
     Libnames.pr_qualid qid;
     Pp.str " that was passed to the { opaque ... } option is not a constant,";
     Pp.str " or does not exist."]

let err_type env sigma err =
  Pp.seq
    [Pp.str "CARROT tried to produce a term that is not well-typed. ";
     Pp.str "Coq gave us this scary looking error:\n";
     Pp.fnl ();
     explain_pretype_error env sigma err;
     Pp.fnl ();
     Pp.fnl ();
     Pp.str "This is often due to one of three issues:\n";
     Pp.str "1. during lifting, the term refers to an earlier term that is opaque, or\n";
     Pp.str "2. during lifting, the term contains match statements that are not preprocessed.\n";
     Pp.str "3. during search or lifting, a type or term is not supported, but we do not correctly detect this."]

let err_ambiguous_swap env num_solutions swap_maps sigma =
  let print_swap_map i swap_map =
    Pp.seq
      [Pp.int i;
       Pp.str ") ";
       (Pp.prlist_with_sep
          (fun _ -> Pp.str ", ")
          (fun (c_o, c_n) ->
            Pp.prlist_with_sep
              (fun _ -> Pp.str " <-> ")
              (Printer.pr_constr_env env sigma)
              [mkConstructU c_o; mkConstructU c_n])
          swap_map);
       Pp.fnl ()]
  in
  Pp.seq
    [Pp.str "CARROT found ";
     Pp.str num_solutions;
     Pp.str " possible mappings for constructors. ";
     Pp.str "Showing up to the first 50:";
     Pp.fnl ();
     Pp.seq (List.mapi print_swap_map swap_maps);
     Pp.fnl ();
     Pp.str "Please choose the mapping you'd like to use. ";
     Pp.str "Then, pass that to CARROT by calling `Find ornament` again. ";
     Pp.str "For example: `Find ornament old new { mapping 0 }`. ";
     Pp.str "If the mapping you want is not in the 50 shown, ";
     Pp.str "please pass the mapping to `Save ornament` instead."]

  
(* --- Possible workaround suggestions --- *)

let try_name = Pp.str "passing a name explicitly to `Find ornament`"
let try_opaque = Pp.str "skipping subterms using the `{ opaque ... }` option"
let try_not_opaque = Pp.str "unsetting some subterms that are set as opaque"
let try_preprocess = Pp.str "preprocessing the definition first"
let try_check_typos = Pp.str "checking for typos"
let try_fully_qualify = Pp.str "fully qualifying the identifier"
let try_supported = Pp.str "using similar, supported types"
let try_provide = Pp.str "providing your own ornament using `Save ornament`"
            
let workaround suggestions =
  Pp.seq
    [Pp.str "To get around this, consider ";
     Pp.prlist_with_sep (fun _ -> Pp.str ", or ") id suggestions;
     Pp.str "."]

(* --- Suggestion to read the FAQ --- *)

let read_faq =
  Pp.str "Please see the README in REDACTED for more information."

(* --- Reasons to cut an issue --- *)

let cool_feature = Pp.str "you really want this feature"
let problematic = Pp.str "this continues to cause you trouble"
let mistake = Pp.str "you believe this should already be supported"

let cut_issue reasons =
  Pp.seq
    [Pp.str "If ";
     Pp.prlist_with_sep (fun _ -> Pp.str ", or if ") id reasons;
     Pp.str ", then please cut an issue in the REDACTED repository."]

(* --- Putting these together --- *)
    
(*
 * Our own user_err function to make it easier to present nice information
 * to the user
 *)
let user_err hdr err suggestions reasons =
  user_err
    ~hdr:hdr
    (Pp.prlist_with_sep
       Pp.spc
       id
       [err; workaround suggestions; read_faq; cut_issue reasons])
