(*
 * Section 1 Example, using CARROT
 *)

Require Import Vector.
Require Import List.
Require Import Ornamental.Ornaments.

(* syntax to match paper *)
Notation vector := Vector.t.

(*
 * map_length from the list standard library
 *)
Check map_length.

(*
 * Coq's vector map.
 *)
Check Vector.map.

(* --- Bonus material --- *)

(*
 * We can get Vector.map from List.map.
 *)

Preprocess List.map as list_map'.
Find ornament list vector as ltv.
Lift list vector in list_map' as map_p.
Unpack map_p as map_u.

(* User-friendly version *)
Program Definition map {T1} {T2} (f : T1 -> T2) {n : nat} (v : vector T1 n) : vector T2 n :=
  map_u T1 T2 f n v.
Next Obligation.
  induction v.
  - auto.
  - simpl. f_equal. auto.
Defined.

(* We can show it's the same as Coq's map *)
Lemma map_correct :
  forall {T1} {T2} (f : T1 -> T2) {n : nat} (v : vector T1 n),
    map f v = Vector.map f v.
Proof.
  intros. induction v.
  - auto.
  - simpl. rewrite <- IHv. unfold map. simpl.
    destruct (map_obligation_1 T1 T2 f n v). auto. 
Qed.
