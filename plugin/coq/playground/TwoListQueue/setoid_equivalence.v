Require Import Coq.Classes.SetoidClass.

Module SetoidEquivalence.

Definition is_equiv {A : Type} (eq : (A -> A -> Prop)) := True. (**replace with real condition*)
  
Record setoid_equiv : Type := mkEquiv
{ A : Type
; A_equiv : A -> A -> Prop
; A_equiv_is_equiv : (@is_equiv A A_equiv)         
; B : Type
; B_equiv : B -> B -> Prop
; B_equiv_is_equiv : (@is_equiv B B_equiv)
; f : A -> B
; g : B -> A
; f_respectful : forall (a1 a2 : A),
    A_equiv a1 a2 -> B_equiv (f a1) (f a2)
; g_respectful : forall (b1 b2 : B),
    B_equiv b1 b2 -> A_equiv (g b1) (g b2)
; section : forall (a : A),
    A_equiv a (g (f a))
; retraction : forall (b : B),
    B_equiv b (f (g b))
} .

End SetoidEquivalence.
