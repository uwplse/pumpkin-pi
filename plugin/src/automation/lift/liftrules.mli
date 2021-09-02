open Liftconfig
open Constr
open Environ
open Evd
open Stateutils
open Reducers
      
(*
 * This module takes in a Coq term that we are lifting and determines
 * the appropriate lifting rule to run
 *)

(* --- Datatypes --- *)

(*
 * When an optimization may be possible, we return one of these.
 * Sometimes, we need more information to determine if the optimization is
 * definitely possible. This just makes it very explicit in the code what
 * is an attempt at an optimization, as opposed to what is needed for
 * correctness only.
 *
 * See the implementation for an explanation of each of these.
 *)
type lift_optimization =
| GlobalCaching of constr
| LocalCaching of constr
| OpaqueConstant
| SimplifyProjectId of reducer * (constr * constr array)
| LazyEta of constr
| AppLazyDelta of constr * constr array
| ConstLazyDelta of Names.Constant.t Univ.puniverses

(*
 * We compile Gallina to a language that matches our premises for the rules
 * in our lifting algorithm. Each of these rules carries more information
 * that is essentially cached for efficiency.
 *
 * See the implementation for an explanation of each of these.
 *)
type lift_rule =
| Equivalence of constr * constr list
| LiftConstr of reducer * (constr * constr list)
| Eta of reducer * (constr * constr list)
| Iota of constr * constr list
| Coherence of reducer * (constr * constr list)
| Optimization of lift_optimization
| CIC of (constr, types, Sorts.t, Univ.Instance.t) kind_of_term

(*
 * Determine which lift rule to run
 *
 * The lift_rule argument is the previous lift rules
 * to prevent infinite recursion in obvious cases
 *)
val determine_lift_rule :
  lift_config -> env -> constr -> lift_rule list -> evar_map -> lift_rule state
