(*
 * By Nate Yazdani
 *)

Structure t {B O : Type} :=
  Pack { base : B; lift : O }.

Arguments Pack {B O}.
Arguments base {B O}.
Arguments lift {B O}.
