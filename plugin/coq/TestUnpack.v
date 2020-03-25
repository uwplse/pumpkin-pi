(*
 * Lifting tests for unpack
 *)

(* TODO add deps and so on *)
(* TODO add to test.sh *)
(* TODO add more here *)
(* TODO clean *)
(* TODO bwd direction *)

Definition minimal_test (T : Type) (n : nat) := { s : { n : nat & vector T n } & projT1 s = n }.
Lift packed vector in minimal_test as minimal_test_lifted. (* TODO move to tests somewhere *)
Print minimal_test_lifted.
Definition proj1_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT1 pv.
Print proj1_test.
Lift packed vector in proj1_test as proj1_test_lifted.
Definition proj1_test_expected (T : Type) (n : nat) (v : vector T n) := existT _ n v.
Print proj1_test_expected.
Print proj1_test_lifted.
Definition minimal_test_2 (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := pv.
Lift packed vector in minimal_test_2 as minimal_test_2_lifted { opaque eq_rect }. (* TODO need to stop this from reducing generally... refold or something *)
Print minimal_test_2_lifted.
Definition proj2_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT2 pv.
Lift packed vector in proj2_test as proj2_test_lifted.

Print proj2_test_lifted.

Definition lifted (T : Type) (n : nat)  (pv : vector T n) :=
  existT (fun (s : sigT (vector T)) => projT1 s = n) (existT (fun n => vector T n) n pv) (eq_refl n).
Check lifted.
Definition ex_test_constr (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) : {s : {x : nat & vector T x} & projT1 s = n} :=
  (fun n v H => existT _ (existT _ n v) H) (projT1 (projT1 pv)) (projT2 (projT1 pv)) (projT2 pv).

Print ex_test_constr.
Lift packed vector in ex_test_constr as ex_test_constr_lifted.
Print ex_test_constr_lifted.
Lemma ex_test_constr_lift_correct :
  forall T n v, ex_test_constr_lifted T n v = v.
Proof.
  reflexivity.
Qed.

(* TODO we will need to eta expand below to above before running: *)
Definition ex_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := existT _ (projT1 pv) (projT2 pv).
Definition ex_test_expected (T : Type) (n : nat) (v : vector T n) := v.

Lift packed vector in ex_test as ex_test_lifted.
Print ex_test_lifted. (* TODO yay!!! ok now move on to other tests *)

Definition proj1_eta_test (T : Type) (n : nat) (pv : { s : { n : nat & vector T n } & projT1 s = n }) := projT1 (existT _ (projT1 pv) (projT2 pv)).
Lift packed vector in proj1_eta_test as proj1_eta_test_lifted.
Print proj1_eta_test_lifted.

(* TODO still stuck here: *)
Print packed_vector.zip.