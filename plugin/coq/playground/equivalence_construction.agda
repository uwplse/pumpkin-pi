{-# OPTIONS --safe --cubical #-}
module equivalence_construction where

open import Cubical.Core.Everything
open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

data Two : Set where
  first : Two
  second : Two

data True : Type where
  tt : True

R : Two -> Two -> Type
R a b = True

quot_id : Two / R -> Two / R
quot_id [ x ] = [ x ]
quot_id (eq/ a b r i) = eq/ a b r i
quot_id (squash/ x y p q i j) = squash/ (quot_id x) (quot_id y) (cong quot_id p) (cong quot_id q) i j

f : True -> Two / R
f tt = [ first ]

isPropTrue : isProp(True)
isPropTrue tt tt = refl

isSetTrue : isSet True
isSetTrue = isProp→isSet isPropTrue

isSetTwoR : isSet (Two / R)
isSetTwoR x y p q = squash/ x y p q

-- thanks to amelia liao for giving the third case
g : Two / R -> True
g [ x ] = tt
g (eq/ a b r i) = tt
g (squash/ x y p q i j) = isSetTrue (g x) (g y) (λ i → g (p i)) (λ i → g (q i)) i j

sec : section f g
sec = elimProp (λ x → isSetTwoR (f (g x)) x) lem where
  lem : (a : Two) → f (g [ a ]) ≡ [ a ]
  lem first = refl
  lem second = eq/ first second tt

ret : retract f g
ret tt = refl

TrueIsoTwoR : Iso True (Two / R)
TrueIsoTwoR = iso f g sec ret

TrueEqTwoR : True ≡ (Two / R)
TrueEqTwoR = isoToPath TrueIsoTwoR

depConstrTrue : True
depConstrTrue = tt

depConstrTwo/R : Two / R
depConstrTwo/R = [ first ]

depElimTrue : (P : True → Set) → P tt → ((t : True) → P t)
depElimTrue P Pt tt = Pt

depElimTwo/R : (P : Two / R → Set) → (∀ x → isProp (P x)) → P [ first ] → ((x : Two / R) → P x)
depElimTwo/R P prop Pf = elimProp prop lem where
  lem : (a : Two) → P [ a ]
  lem first = Pf
  lem second = subst P (eq/ first second tt) Pf

{-
sec [ first ] = refl
sec [ second ] = eq/ first second tt
sec (eq/ first first r i) = {!refl!}
sec (eq/ first second r i) = {!!}
sec (eq/ second b r i) = {!!}
sec (squash/ x y p q i j) = {!!}
-}


{-
  lem2 : p ≡ q
  lem2 = isSetTwoR x y p q
  lem : (k : I) → g (p k) ≡ g (q k)
  lem k = subst (λ z → g (p k) ≡ g (z k)) lem2 refl
-}

-- J {!λ y' p' → (g (p' i)) ≡ (g (q j))!} {!!} {!!}
