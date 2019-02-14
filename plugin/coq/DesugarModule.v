Require Import Ornamental.Ornaments.
Require List.

(*
 * NOTE: Any serious bug is likely to cause a typing error, and comparing the
 * exact output against some reference would give negligible further assurance
 * at the cost of unwieldiness. It would be very difficult to translate terms
 * only partially while preserving well-typedness.
 *)
Desugar Module List as List' {include length, app}.
