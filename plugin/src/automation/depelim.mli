(*
 * Dependent elimination for inductive families over sigma-packed indices.
 *)

open Constr
open Inductive

(*
 * Construct a wrapper term around an inductive family's (given as a
 * `mind_specif`) eliminator (given as a constant `constr` reference with its
 * `types`), returning both the wrapper `constr` and its "natural" `types`.
 *
 * The wrapper term resembles an eta-expansion of the underlying eliminator,
 * except that the applied motive is also an eta-expansion in which any index
 * of sigma type is definitionally eta-expanded. The net effect is that the
 * wrapped eliminator accepts a motive expecting definitional eta-expansion
 * of indices with sigma type.
 *
 * The wrapped eliminator can be understood as enabling implicit dependent
 * elimination for the inductive family w.r.t. its indices of sigma type.
 * Since the canonical form of a sigma type is irrefutable, this (fairly)
 * simple instance of dependent elimination does not need to rely on any
 * extra axiom or any special (proof of a) property like UIP.
 *
 * NOTE: Using the returned `types` is not strictly necessary, but it is much
 * more readable than that inferred by type-checking.
 *)
val eta_guard_eliminator : mind_specif -> constr -> types -> constr * types
