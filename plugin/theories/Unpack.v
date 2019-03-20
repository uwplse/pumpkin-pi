Require Import Coq.Program.Tactics.
Require Import Coq.Logic.EqdepFacts.

Local Notation "( x ; y )" := (@existT _ _ x y).
Local Notation "p '.1'" := (@projT1 _ _ p) (left associativity, at level 8).
Local Notation "p '.2'" := (@projT2 _ _ p) (left associativity, at level 8).

Lemma sigT_eta {A : Type} {B : A -> Type} (p : {x:A & B x}) : p = (p.1; p.2).
Proof. destruct p. auto. Defined.

Lemma eq_sigT_eta {A : Type} {B : A -> Type} {p q : {x:A & B x}} :
  p = q -> (p.1; p.2) = (q.1; q.2).
Proof. destruct p, q. auto. Defined.

Ltac rewrap unwrapped :=
  lazymatch goal with
  | [ |- forall (x : ?A), @?C x ] =>
    let x := fresh x in
    refine (fun (x : ?A) => _);
    lazymatch A with
    | @sigT _ _ =>
      rewrap (unwrapped x.1 x.2)
    | _ =>
      rewrap (unwrapped x)
    end
  | [ |- @eq_dep ?A ?B ?x_i ?x ?y_i ?y ] =>
    exact (@eq_dep_eq_sigT A B x_i y_i x y unwrapped)
  | [ |- _ ] =>
    exact unwrapped
  end.

Ltac unwrap wrapped :=
  lazymatch (eval hnf in wrapped) with
  | forall (x : ?A), @?C x =>
    let x := fresh x in
    lazymatch A with
    | @sigT ?A ?B =>
      let x_i := fresh x "_i" in
      refine (forall (x_i : A) (x : B x_i), _);
      unwrap (C (x_i; x))
    | _ =>
      refine (forall (x : A), _);
      unwrap (C x)
    end
  | @eq (@sigT ?A ?B) ?x ?y =>
    exact (eq_dep A B x.1 x.2 y.1 y.2)
  | _ =>
    exact wrapped
  end.

Ltac repack index value :=
  lazymatch goal with
  | [ |- forall (x : ?A), _ ] =>
    let x := fresh x in
    refine (fun (x : ?A) => _);
    lazymatch A with
    | @sigT _ _ =>
      repack (index x.1 x.2) (value x.1 x.2)
    | _ =>
      repack (index x) (value x)
    end
  | [ |- @sigT _ _ ] =>
    exact (index; value)
  end.

Ltac unpack_index packed :=
  lazymatch (eval hnf in packed) with
  | forall (x : ?A), @?C x =>
    let x := fresh x in
    lazymatch A with
    | @sigT ?A ?B =>
      let x_i := fresh x "_i" in
      refine (forall (x_i : A) (x : B x_i), _);
      unpack_index (C (x_i; x))
    | context K [(@sigT _ _)] =>
      let A' := unwrap A in
      refine (forall (x : A'), _);
      assert A as x' by rewrap x;
      unpack_index (C x')
    | _ =>
      refine (forall (x : A), _);
      unpack_index (C x)
    end
  | @sigT ?A ?B =>
    exact A
  end.

Ltac unpack_value packed index :=
  lazymatch (eval hnf in packed) with
  | forall (x : ?A), @?C x =>
    let x := fresh x in
    lazymatch A with
    | @sigT ?A ?B =>
      let x_i := fresh x "_i" in
      refine (forall (x_i : A) (x : B x_i), _);
      unpack_value (C (x_i; x) (index x_i x))
    | context K [(@sigT _ _)] =>
      let A' := unwrap A in
      refine (forall (x : A'), _);
      assert A as x' by rewrap x;
      unpack_value (C x') (index x')
    | _ =>
      refine (forall (x : A), _);
      unpack_value (C x) (index x)
    end
  | @sigT ?A ?B =>
    exact (B index)
  end.

Ltac unpack_type t :=
  lazymatch (eval hnf in t) with
  | forall (x : @sigT ?A ?B), @?C x =>
    let x := fresh x in
    let x_i := fresh x "_i" in
    refine (forall (x_i : A), _);
    refine (forall (x : B x_i), _);
    unpack_type (C (x_i; x))
  | forall (x : ?A), @?C x =>
    let x := fresh x in
    lazymatch A with
    | (@sigT ?A ?B) =>
      let x_i := fresh x "_i" in
      refine (forall (x_i : A), _);
      refine (forall (x : B x_i), _);
      unpack_type (C (x_i; x))
    | context K [forall _, sigT _ _] =>
      let x_i := fresh x "_i" in
      let A' := unpack_index A in
      refine (forall (x_i : A), _);
      let B' := unpack_value A x_i in
      refine (forall (x : B' x_i), _);
      assert A as x' by repack x_i x;
      unpack_type (C x')
    | context K [forall (_ : sigT _ _), _] =>
      let A' := unwrap A in
      refine (forall (x : A'), _);
      assert A as x' by rewrap x;
      unpack_type (C x')
    | _ =>
      refine (forall (x : A), _);
      unpack_type (C x)
    end
  | @eq (@sigT ?A ?B) ?x ?y =>
    exact (eq_dep A B x.1 x.2 y.1 y.2)
  | @sigT ?A ?B =>
    refine (B ?[i]);
    unshelve (instantiate (i := _))
  | _ =>
    exact t
  end.

(* Obviated by the below version but retained temporarily for debugging purposes. *)
(* (* NOTE: The current type doesn't really need to be another argument... *) *)
(* Ltac unpack_term e t := *)
(*   lazymatch (eval hnf in t) with *)
(*   | forall (x : @sigT ?A ?B), @?C x => *)
(*     let x := fresh x in *)
(*     let x_i := fresh x "_i" in *)
(*     refine (fun (x_i : A) (x : B x_i) => _); *)
(*     unpack_term (e (x_i; x)) (C (x_i; x)) *)
(*   | forall (x : ?A), @?C x => *)
(*     let x := fresh x in *)
(*     lazymatch A with *)
(*     | (@sigT ?A ?B) => *)
(*       let x_i := fresh x "_i" in *)
(*       refine (fun (x_i : A) => _); *)
(*       refine (fun (x : B x_i) => _); *)
(*       unpack_term (e (x_i; x)) (C (x_i; x)) *)
(*     | context K [forall _, sigT _ _] => *)
(*       let x_i := fresh x "_i" in *)
(*       let A' := unpack_index A in *)
(*       refine (fun (x_i : A) => _); *)
(*       let B' := unpack_value A x_i in *)
(*       refine (fun (x : B' x_i) => _); *)
(*       assert A as x' by repack x_i x; *)
(*       unpack_term (e x') (C x') *)
(*     | context K [forall (_ : sigT _ _), _] => *)
(*       let A' := unwrap A in *)
(*       refine (fun (x : A') => _); *)
(*       assert A as x' by rewrap x; *)
(*       unpack_term (e x') (C x') *)
(*     | _ => *)
(*       refine (fun (x : A) => _); *)
(*       unpack_term (e x) (C x) *)
(*     end *)
(*   | @eq (@sigT ?A ?B) ?x ?y => *)
(*     refine (eq_sigT_eq_dep A B x.1 y.1 x.2 y.2 (eq_sigT_eta e)) *)
(*   | @sigT ?A ?B => *)
(*     exact (e.2) *)
(*   | _ => *)
(*     exact e *)
(*   end. *)

Ltac unpack e :=
  let t := type of e in
  lazymatch eval hnf in t with
  | forall (x : @sigT ?A ?B), _ =>
    let x := fresh x in
    let x_i := fresh x "_i" in
    refine (fun (x_i : A) (x : B x_i) => _);
    unpack (e (x_i; x))
  | forall (x : ?A), _ =>
    let x := fresh x in
    lazymatch A with
    | (@sigT ?A ?B) =>
      let x_i := fresh x "_i" in
      refine (fun (x_i : A) => _);
      refine (fun (x : B x_i) => _);
      unpack (e (x_i; x))
    | context K [forall _, sigT _ _] =>
      let x_i := fresh x "_i" in
      let A' := unpack_index A in
      refine (fun (x_i : A) => _);
      let B' := unpack_value A x_i in
      refine (fun (x : B' x_i) => _);
      assert A as x' by repack x_i x;
      unpack (e x')
    | context K [forall (_ : sigT _ _), _] =>
      let A' := unwrap A in
      refine (fun (x : A') => _);
      assert A as x' by rewrap x;
      unpack (e x')
    | _ =>
      refine (fun (x : A) => _);
      unpack (e x)
    end
  | @eq (@sigT ?A ?B) ?x ?y =>
    refine (eq_sigT_eq_dep A B x.1 y.1 x.2 y.2 (eq_sigT_eta e))
  | @sigT ?A ?B =>
    exact (e.2)
  | _ =>
    exact e
  end.
