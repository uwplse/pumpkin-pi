open Utilities
open CErrors
open Himsg

(* 
 * Errors and error messages
 *)

(* --- Exceptions --- *)

exception NotEliminators
exception NotInductive
exception NotAlgebraic

(* --- Error descriptions --- *)

let err_unsupported_change = Pp.str "Change not yet supported."

let err_new_parameter = Pp.str "New parameters not yet supported."

let err_new_constructor = Pp.str "New constructors not yet supported."

let err_save_ornament = Pp.str "Failed to save ornament."

let err_unexpected_change expected_kind =
  Pp.seq
    [Pp.str "DEVOID expected an ";
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
    [Pp.str "DEVOID tried to produce a term that is not well-typed. ";
     Pp.str "Coq gave us this scary looking error:\n";
     Pp.fnl ();
     explain_pretype_error env sigma err;
     Pp.fnl ();
     Pp.fnl ();
     Pp.str "This is often due to one of three issues:\n";
     Pp.str "1. during lifting, the term refers to an earlier term that is opaque, or\n";
     Pp.str "2. during lifting, the term contains match statements that are not preprocessed.";
     Pp.str "3. during search or lifting, a type or term is not supported, but we do not correctly detect this."]

(* --- Possible workaround suggestions --- *)

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
  Pp.str "Please see the README in uwplse/ornamental-search for more information."

(* --- Reasons to cut an issue --- *)

let cool_feature = Pp.str "you really want this feature"
let problematic = Pp.str "this continues to cause you trouble"
let mistake = Pp.str "you believe this should already be supported"

let cut_issue reasons =
  Pp.seq
    [Pp.str "If ";
     Pp.prlist_with_sep (fun _ -> Pp.str ", or if ") id reasons;
     Pp.str ", then please cut an issue in the uwplse/ornamental-search repository."]

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
