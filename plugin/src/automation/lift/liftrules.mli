open Liftconfig
open Constr
open Environ
open Evd
open Indutils
open Stateutils
open Reducers
      
(* TODO top-level comment, clean, etc *)

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
| SimplifyProjectPacked of reducer * (constr * constr array)
| LazyEta of constr
| AppLazyDelta of constr * constr array
| ConstLazyDelta of Names.Constant.t Univ.puniverses
| SmartLiftConstr of constr * constr list

(* TODO move/refactor/explain each/top comment/finish/simplify/move more optimizations up/clean/be consistent about how these recurse *)
type lift_rule =
| Equivalence of constr list
| LiftConstr of constr * constr list
| LiftPack
| Coherence of types * constr * constr list
| LiftElim of elim_app
| Section
| Retraction
| Internalize
| Optimization of lift_optimization
| CIC

(* TODO comment etc *)
val determine_lift_rule :
  lift_config -> env -> constr -> evar_map -> lift_rule state
