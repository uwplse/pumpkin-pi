Require Import Coq.Classes.SetoidClass.

Module SetoidEquivalence.
 
Record setoid_equiv (A : Type) `{setoida : Setoid A} (B : Type) `{setoidb : Setoid B} : Type := mkEquiv
{f : A -> B
; g : B -> A
; f_respectful : forall (a1 a2 : A),
    equiv a1 a2 -> equiv (f a1) (f a2)
; g_respectful : forall (b1 b2 : B),
    equiv b1 b2 -> equiv (g b1) (g b2)
; section : forall (a : A),
    equiv a (g (f a))
; retraction : forall (b : B),
    equiv b (f (g b))
}.

End SetoidEquivalence.
