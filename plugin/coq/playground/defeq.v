(*
 * Thoughts on definitional equality
 *)

Require Import List Vector.
Require Import Ornamental.Ornaments.

(*
 * The first place we ever encountered definitional equality problems
 * was in lifting proofs about app. Let's give that a try for context.
 *)
Preprocess Module List as List' { opaque (* ignore these: *)
  RelationClasses
  Nat
  Coq.Init.Nat
}.
Set DEVOID lift type.
Lift list Vector.t in List'.Coq_Init_Datatypes_app as appV.

(*
 * Here is the term this generates:
 *)
Definition appV_term (A : Type) (l m : {H : nat & t A H}) : {H : nat & t A H} :=
existT (fun H : nat => t A H)
  (projT1
     (VectorDef.t_rect A
        (fun (n : nat) (_ : VectorDef.t A n) =>
         {H : nat & t A H} -> {H : nat & t A H})
        (fun m0 : {H : nat & t A H} =>
         existT (fun H : nat => t A H) (projT1 m0) (projT2 m0))
        (fun (h : A) (n : nat) (_ : VectorDef.t A n)
           (H : {H : nat & t A H} -> {H : nat & t A H})
           (m0 : {H0 : nat & t A H0}) =>
         existT (fun H0 : nat => VectorDef.t A H0)
           (S
              (projT1
                 (H (existT (fun H0 : nat => t A H0) (projT1 m0) (projT2 m0)))))
           (VectorDef.cons A h
              (projT1
                 (H (existT (fun H0 : nat => t A H0) (projT1 m0) (projT2 m0))))
              (projT2
                 (H (existT (fun H0 : nat => t A H0) (projT1 m0) (projT2 m0))))))
        (projT1 l) (projT2 l)
        (existT (fun H : nat => t A H) (projT1 m) (projT2 m))))
  (projT2
     (VectorDef.t_rect A
        (fun (n : nat) (_ : VectorDef.t A n) =>
         {H : nat & t A H} -> {H : nat & t A H})
        (fun m0 : {H : nat & t A H} =>
         existT (fun H : nat => t A H) (projT1 m0) (projT2 m0))
        (fun (h : A) (n : nat) (_ : VectorDef.t A n)
           (H : {H : nat & t A H} -> {H : nat & t A H})
           (m0 : {H0 : nat & t A H0}) =>
         existT (fun H0 : nat => VectorDef.t A H0)
           (S
              (projT1
                 (H (existT (fun H0 : nat => t A H0) (projT1 m0) (projT2 m0)))))
           (VectorDef.cons A h
              (projT1
                 (H (existT (fun H0 : nat => t A H0) (projT1 m0) (projT2 m0))))
              (projT2
                 (H (existT (fun H0 : nat => t A H0) (projT1 m0) (projT2 m0))))))
        (projT1 l) (projT2 l)
        (existT (fun H : nat => t A H) (projT1 m) (projT2 m)))).

(*
 * Note the explicit eta of packed vectors s to (existT _ (projT1 s) (projT2 s)).
 * There is a reason for this. Consider the alternative term that we get
 * when we disable the identity rule:
 *)
Definition appV_bad (A : Type) (l m : {H : nat & t A H}) : {H : nat & t A H} :=
VectorDef.t_rect A
  (fun (n : nat) (_ : VectorDef.t A n) =>
   {H : nat & t A H} -> {H : nat & t A H}) (fun m0 : {H : nat & t A H} => m0)
  (fun (h : A) (n : nat) (_ : VectorDef.t A n)
     (H : {H : nat & t A H} -> {H : nat & t A H}) 
     (m0 : {H0 : nat & t A H0}) =>
   existT (fun H0 : nat => VectorDef.t A H0) (S (projT1 (H m0)))
     (VectorDef.cons A h (projT1 (H m0)) (projT2 (H m0)))) 
  (projT1 l) (projT2 l) m.

(*
 * Indeed, this behaves the same way. But the problem happens when we look at
 * lifting definitional equalities. For example, with the identity rule we can lift
 * app_nil_r without issue:
 *)
Lift list Vector.t in List'.app_nil_r as appV_nil_r { opaque f_equal }.

(*
 * That gives us this term:
 *)
Definition appV_nil_r_term (A : Type) (l : {H : nat & t A H}) : existT (fun H : nat => t A H)
         (projT1
            (appV A (existT (fun H : nat => t A H) (projT1 l) (projT2 l))
               (existT (fun H : nat => t A H) 0 (VectorDef.nil A))))
         (projT2
            (appV A (existT (fun H : nat => t A H) (projT1 l) (projT2 l))
               (existT (fun H : nat => t A H) 0 (VectorDef.nil A)))) =
       existT (fun H : nat => t A H) (projT1 l) (projT2 l) :=
VectorDef.t_rect A
  (fun (n : nat) (t0 : VectorDef.t A n) =>
   existT (fun H : nat => t A H)
     (projT1
        (appV A
           (existT (fun H : nat => t A H) n t0)
           (existT (fun H : nat => t A H) 0 (VectorDef.nil A))))
     (projT2
        (appV A
           (existT (fun H : nat => t A H) n t0)
           (existT (fun H : nat => t A H) 0 (VectorDef.nil A)))) =
   existT (fun H : nat => t A H) n t0) eq_refl
  (fun (h : A) (n : nat) (t0 : VectorDef.t A n)
     (H : existT (fun H : nat => t A H)
            (projT1
               (appV A
                  (existT (fun H : nat => t A H) n t0)
                  (existT (fun H : nat => t A H) 0 (VectorDef.nil A))))
            (projT2
               (appV A
                  (existT (fun H : nat => t A H) n t0)
                  (existT (fun H : nat => t A H) 0 (VectorDef.nil A)))) =
          existT (fun H : nat => t A H) n t0) =>
   eq_ind
     (existT (fun H0 : nat => VectorDef.t A H0)
        (S
           (projT1
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
        (VectorDef.cons A h
           (projT1
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
           (projT2
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))))
     (fun y : {H0 : nat & t A H0} =>
      existT (fun H0 : nat => VectorDef.t A H0)
        (S
           (projT1
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
        (VectorDef.cons A h
           (projT1
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
           (projT2
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))) =
      existT (fun H0 : nat => t A H0) (projT1 y) (projT2 y))
     (eq_ind
        (fun l0 : {H0 : nat & t A H0} =>
         existT (fun H0 : nat => VectorDef.t A H0) (S (projT1 l0))
           (VectorDef.cons A h (projT1 l0) (projT2 l0)))
        (fun y : {H0 : nat & t A H0} -> {H0 : nat & t A H0} =>
         existT (fun H0 : nat => VectorDef.t A H0)
           (S
              (projT1
                 (appV A
                    (existT (fun H0 : nat => t A H0) n t0)
                    (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
           (VectorDef.cons A h
              (projT1
                 (appV A
                    (existT (fun H0 : nat => t A H0) n t0)
                    (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
              (projT2
                 (appV A
                    (existT (fun H0 : nat => t A H0) n t0)
                    (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))) =
         existT (fun H0 : nat => t A H0)
           (projT1
              (y
                 (existT (fun H0 : nat => t A H0)
                    (projT1
                       (appV A
                          (existT (fun H0 : nat => t A H0) n t0)
                          (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
                    (projT2
                       (appV A
                          (existT (fun H0 : nat => t A H0) n t0)
                          (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))))
           (projT2
              (y
                 (existT (fun H0 : nat => t A H0)
                    (projT1
                       (appV A
                          (existT (fun H0 : nat => t A H0) n t0)
                          (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
                    (projT2
                       (appV A
                          (existT (fun H0 : nat => t A H0) n t0)
                          (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))))))
        eq_refl
        (fun l0 : {H0 : nat & t A H0} =>
         existT (fun H0 : nat => VectorDef.t A H0) (S (projT1 l0))
           (VectorDef.cons A h (projT1 l0) (projT2 l0))) eq_refl)
     (existT (fun H0 : nat => VectorDef.t A H0)
        (S n)
        (VectorDef.cons A h n t0))
     (eq_ind
        (existT (fun H0 : nat => t A H0)
           (projT1
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
           (projT2
              (appV A
                 (existT (fun H0 : nat => t A H0) n t0)
                 (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
        (fun y : {H0 : nat & t A H0} =>
         existT (fun H0 : nat => VectorDef.t A H0)
           (S
              (projT1
                 (appV A
                    (existT (fun H0 : nat => t A H0) n t0)
                    (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
           (VectorDef.cons A h
              (projT1
                 (appV A
                    (existT (fun H0 : nat => t A H0) n t0)
                    (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
              (projT2
                 (appV A
                    (existT (fun H0 : nat => t A H0) n t0)
                    (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))) =
         existT (fun H0 : nat => VectorDef.t A H0) (S (projT1 y))
           (VectorDef.cons A h (projT1 y) (projT2 y))) eq_refl
        (existT (fun H0 : nat => t A H0) n t0) H))
  (projT1 l)
  (projT2 l).

(*
 * In contrast, without identity, we get this:
 *)
Fail Definition appV_nil_r_bad (A : Type) (l : {H : nat & t A H}) : appV_bad A l (existT (fun H : nat => t A H) 0 (VectorDef.nil A)) = l :=
  VectorDef.t_rect A
    (fun (n : nat) (t0 : VectorDef.t A n) =>
     appV_bad A (existT (fun H : nat => VectorDef.t A H) n t0)
       (existT (fun H : nat => t A H) 0 (VectorDef.nil A)) =
     existT (fun H : nat => VectorDef.t A H) n t0) eq_refl
    (fun (h : A) (n : nat) (t0 : VectorDef.t A n)
       (H : appV_bad A (existT (fun H : nat => VectorDef.t A H) n t0)
              (existT (fun H : nat => t A H) 0 (VectorDef.nil A)) =
            existT (fun H : nat => VectorDef.t A H) n t0) =>
     eq_ind
       (existT (fun H0 : nat => VectorDef.t A H0)
          (S
             (projT1
                (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                   (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
          (VectorDef.cons A h
             (projT1
                (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                   (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
             (projT2
                (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                   (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))))
       (fun y : {H0 : nat & t A H0} =>
        existT (fun H0 : nat => VectorDef.t A H0)
          (S
             (projT1
                (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                   (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
          (VectorDef.cons A h
             (projT1
                (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                   (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
             (projT2
                (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                   (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))) =
        y)
       (eq_ind
          (fun l0 : {H0 : nat & t A H0} =>
           existT (fun H0 : nat => VectorDef.t A H0) 
             (S (projT1 l0)) (VectorDef.cons A h (projT1 l0) (projT2 l0)))
          (fun y : {H0 : nat & t A H0} -> {H0 : nat & t A H0} =>
           existT (fun H0 : nat => VectorDef.t A H0)
             (S
                (projT1
                   (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                      (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))))
             (VectorDef.cons A h
                (projT1
                   (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                      (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
                (projT2
                   (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                      (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))) =
           y
             (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
                (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A))))
          eq_refl
          (fun l0 : {H0 : nat & t A H0} =>
           existT (fun H0 : nat => VectorDef.t A H0) 
             (S (projT1 l0)) (VectorDef.cons A h (projT1 l0) (projT2 l0)))
          eq_refl)
       (existT (fun H0 : nat => VectorDef.t A H0)
          (S (projT1 (existT (fun H0 : nat => VectorDef.t A H0) n t0)))
          (VectorDef.cons A h
             (projT1 (existT (fun H0 : nat => VectorDef.t A H0) n t0))
             (projT2 (existT (fun H0 : nat => VectorDef.t A H0) n t0))))
       (List'.Coq_Init_Logic_f_equal {H0 : nat & t A H0} 
          {H0 : nat & t A H0}
          (fun l0 : {H0 : nat & t A H0} =>
           existT (fun H0 : nat => VectorDef.t A H0) 
             (S (projT1 l0)) (VectorDef.cons A h (projT1 l0) (projT2 l0)))
          (appV_bad A (existT (fun H0 : nat => VectorDef.t A H0) n t0)
             (existT (fun H0 : nat => t A H0) 0 (VectorDef.nil A)))
          (existT (fun H0 : nat => VectorDef.t A H0) n t0) H)) 
    (projT1 l) (projT2 l).

(* Let's break these down to find the error. *)

Definition id_eta {A : Type} (s : { H : nat & t A H }) : { H : nat & t A H} :=
  existT (fun H : nat => t A H) (projT1 s) (projT2 s).

Definition nil {A : Type} :=
  existT (fun H : nat => t A H) 0 (VectorDef.nil A).

Definition cons {A : Type} (a : A) (s : { H : nat & t A H }) : { H : nat & t A H} :=
  existT _
    (S (projT1 s))
    (VectorDef.cons A a (projT1 s) (projT2 s)).

(*
 * That gives us this term:
 *)
Definition appV_nil_r_term_2 (A : Type) (l : {H : nat & t A H}) : id_eta (appV A (id_eta l) nil) = id_eta l :=
VectorDef.t_rect
  A
  (fun (n : nat) (t0 : VectorDef.t A n) =>
     id_eta (appV A (existT _ n t0) nil) = existT _ n t0)
  eq_refl
  (fun (h : A) (n : nat) (t0 : VectorDef.t A n)
       (H : id_eta (appV A (existT _ n t0) nil) = existT _ n t0) =>
   eq_ind
     (cons h (appV A (existT _ n t0) nil))
     (fun y : {H0 : nat & t A H0} =>
        cons h (appV A (existT _ n t0) nil) = id_eta y)
     eq_refl
     (cons h (existT _ n t0))
     (eq_ind
        (id_eta (appV A (existT _ n t0) nil))
        (fun y : {H0 : nat & t A H0} => cons h (appV A (existT _ n t0) nil) = cons h y)
        eq_refl
        (existT _ n t0)
        H))
  (projT1 l)
  (projT2 l).

(*
 * Phew.
 * In contrast, without identity, we get this:
 *)
Fail Definition appV_nil_r_bad_2 (A : Type) (l : {H : nat & t A H}) : appV_bad A l nil = l :=
  VectorDef.t_rect A
    (fun (n : nat) (t0 : VectorDef.t A n) =>
      appV_bad A (existT _ n t0) nil =
      existT _ n t0)
    eq_refl
    (fun (h : A) (n : nat) (t0 : VectorDef.t A n)
         (H : appV_bad A (existT _ n t0) nil = existT _ n t0) =>
     eq_ind
       (cons h (appV_bad A (existT _ n t0) nil))
       (fun y : {H0 : nat & t A H0} =>
         cons h (appV_bad A (existT _ n t0) nil) = y)
       eq_refl
       (cons h (existT _ n t0))
       (eq_ind
         (appV_bad A (existT _ n t0) nil)
         (fun y0 : {H0 : nat & t A H0}  => cons h (appV_bad A (existT _ n t0) nil) = cons h y0)
         eq_refl
         (existT _ n t0)
         H))
    (projT1 l)
    (projT2 l).

(* But the actual type is this: *)
Definition appV_nil_r_bad_2 (A : Type) (l : {H : nat & t A H}) : appV_bad A (id_eta l) nil = id_eta l :=
  VectorDef.t_rect A
    (fun (n : nat) (t0 : VectorDef.t A n) =>
      appV_bad A (existT _ n t0) nil =
      existT _ n t0)
    eq_refl
    (fun (h : A) (n : nat) (t0 : VectorDef.t A n)
         (H : appV_bad A (existT _ n t0) nil = existT _ n t0) =>
     eq_ind
       (cons h (appV_bad A (existT _ n t0) nil))
       (fun y : {H0 : nat & t A H0} =>
         cons h (appV_bad A (existT _ n t0) nil) = y)
       eq_refl
       (cons h (existT _ n t0))
       (eq_ind
         (appV_bad A (existT _ n t0) nil)
         (fun y0 : {H0 : nat & t A H0}  => cons h (appV_bad A (existT _ n t0) nil) = cons h y0)
         eq_refl
         (existT _ n t0)
         H))
    (projT1 l)
    (projT2 l).

(* 
 * So in other words, without the id rule, the type of app_nil_r lifts to:
 *
 *   appV_bad A l nil = l
 *
 * but the term of app_nil_r lifts to a term of type:
 *
 *   appV_bad A (id_eta l) nil = id_eta l 
 *)

(*
 * Why is this? It has to do with the type of our lifted eliminator:
 *)
Definition vect_dep_elim (A: Type) (P : sigT (Vector.t A) -> Type) pnil (pcons : forall h s, P s -> P (cons h s)) s :=
  Vector.t_rect
    A
    (fun n v => P (existT _ n v))
    pnil
    (fun t n (v : Vector.t A n) (IH : P (existT _ n v)) => pcons t (existT _ n v) IH)
    (projT1 s)
    (projT2 s).

(*
 * So we have (P (projT1 s) (projT2 s)).
 * When our motive is:
 *)
Definition bad_motive (A : Type) (n : nat) (v : Vector.t A n) :=
  appV_bad A (existT _ n v) nil =
  existT _ n v.
(*
 * applied to (projT1 l) (projT2 l), we get:
 *)
Definition bad_motive_app (A : Type) (l : sigT (Vector.t A)) :=
  appV_bad A (existT _ (projT1 l) (projT2 l)) nil =
  existT _ (projT1 l) (projT2 l).

Print VectorDef.t_rect.

(* So: *)

(*
 * P l                     := app A l nil = l
 * Q n v                   := appV A (existT _ n v) nilV = existT _ n v
 * Q (projT1 l) (projT2 l) := appV A (existT _ (projT1 l) (projT2 l)) nilV = existT _ (projT1 l) (projT2 l)
 *)

(*
 * Need that the type (P l) lifts to a type definitionally equal to (Q (projT1 l) (projT2 l)).
 *) 

(*
 * We could succeed this way, though:
 *)
Program Definition vect_dep_elim_2 (A : Type)
  (P : sigT (Vector.t A) -> Type)
  (f : P nil)
  (f0 : forall (h : A) (s : sigT (Vector.t A)),
        P s ->
        P (existT _ (S (projT1 s)) (Vector.cons A h (projT1 s) (projT2 s))))
  : forall (s : sigT (Vector.t A)), P s.
Proof.
  intros. induction s. induction p.
  - apply f.
  - specialize (f0 h (existT _ n p)). apply f0. apply IHp.
Defined.

Definition appV_bad_2 (A : Type) (l m : {H : nat & t A H}) : { H : nat & t A H} :=
  vect_dep_elim_2 A
  (fun _ => {H : nat & t A H} -> {H : nat & t A H})
  (fun m0 : {H : nat & t A H} => m0)
  (fun (h : A) _ (H : {H : nat & t A H} -> {H : nat & t A H}) (m0 : {H0 : nat & t A H0}) =>
    cons h (H m0))
  l
  m.

(* But then we get a problem here in a different place, notably since cons doesn't preserve the equality: *)
Fail Definition appV_nil_r_bad_3 (A : Type) (l : {H : nat & t A H}) : appV_bad_2 A l nil = l :=
  vect_dep_elim_2 A
    (fun (s : sigT (Vector.t A)) =>
      appV_bad_2 A s nil = s)
    eq_refl
    (fun (h : A) (s : sigT (Vector.t A))
         (H : appV_bad_2 A s nil = s) =>
     eq_ind
       (cons h (appV_bad_2 A s nil))
       (fun y : {H0 : nat & t A H0} =>
         cons h (appV_bad_2 A s nil) = y)
       eq_refl
       (cons h s)
       (eq_ind
         (appV_bad_2 A s nil)
         (fun y0 : {H0 : nat & t A H0}  => cons h (appV_bad_2 A s nil) = cons h y0)
         eq_refl
         s
         H))
    l.

Definition elim_id (A : Type) (s : {H : nat & t A H}) :=
  vect_dep_elim
    A
    (fun _ => {H : nat & t A H})
    nil
    (fun (h : A) _ IH =>
      cons h IH)
    s.

Definition elim_id_2 (A : Type) (s : {H : nat & t A H}) :=
  vect_dep_elim_2
   A
   (fun _ => {H : nat & t A H})
   nil
   (fun (h : A) _ IH =>
     cons h IH)
   s.

Fail Lemma foo:
  forall A h s,
    exists (H : cons h (elim_id_2 A s) = elim_id_2 A (cons h s)),
      H = eq_refl.

Lemma bar:
  forall A h s,
    exists (H : cons h (elim_id A s) = elim_id A (cons h s)),
      H = eq_refl.
Proof.
  intros. exists (eq_refl (cons h (elim_id A s))). auto.
Defined.

Lemma elim_id_good_1 :
  forall A l (f : forall (l : sigT (Vector.t A)), l = l),
    vect_dep_elim A (fun l => l = l) (f nil) (fun t s _ => f (cons t s)) l = f (id_eta l).
Proof.
  intros A l f. unfold vect_dep_elim. unfold id_eta. induction l. simpl.
  induction p; reflexivity.
Defined.

Lemma elim_id_bad_good_1 :
  forall A l (f : forall (l : sigT (Vector.t A)), l = l),
    vect_dep_elim_2 A (fun l => l = l) (f nil) (fun t s _ => f (cons t s)) l = f l.
Proof.
  intros A l f. unfold vect_dep_elim_2. induction l. simpl.
  induction p; reflexivity.
Defined.

Lemma elim_id_good_2 :
  forall A l (f : forall (l : sigT (Vector.t A)), l = l),
    vect_dep_elim A (fun l => l = l) (f nil) (fun t s _ => f (cons t s)) l = f (id_eta l).
Proof.
  intros A l f. unfold vect_dep_elim. unfold id_eta. induction l. simpl.
  induction p; reflexivity.
Defined.


(* Failed to lift List'.app_nil_end
Failed to lift List'.app_eq_nil
Failed to lift List'.app_eq_unit
Failed to lift List'.app_inj_tail
Failed to lift List'.app_inv_head
Failed to lift List'.app_inv_tail
Failed to lift List'.app_removelast_last
Failed to lift List'.removelast_app*)