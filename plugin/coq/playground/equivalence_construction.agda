{-# OPTIONS --safe --cubical #-}
module equivalence_construction where

open import Cubical.Core.Everything
open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Agda.Builtin.Nat
open import Cubical.Data.Nat

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

first≠second : ¬ (first ≡ second)
first≠second p = subst t p tt where
  t : Two → Type
  t first = True
  t second = ⊥

second≠first : ¬ (second ≡ first)
second≠first p = subst t p tt where
  t : Two → Type
  t first = ⊥
  t second = True

discreteTwo : Discrete Two
discreteTwo first first = yes refl
discreteTwo first second = no first≠second
discreteTwo second first = no second≠first
discreteTwo second second = yes refl

isSetTwo : isSet Two
isSetTwo = Discrete→isSet discreteTwo

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

data Three : Set where
  t1 : Three
  t2 : Three
  t3 : Three

R2 : Three → Three → Type
R2 t1 t1 = True
R2 t1 t2 = ⊥
R2 t1 t3 = ⊥
R2 t2 t1 = ⊥
R2 t2 t2 = True
R2 t2 t3 = True
R2 t3 t1 = ⊥
R2 t3 t2 = True
R2 t3 t3 = True

f2 : Two → (Three / R2)
f2 first = [ t1 ]
f2 second = [ t2 ]

g2 : (Three / R2) → Two
g2 [ t1 ] = first
g2 [ t2 ] = second
g2 [ t3 ] = second
g2 (eq/ t1 t1 r i) = first
g2 (eq/ t2 t2 r i) = second
g2 (eq/ t2 t3 r i) = second
g2 (eq/ t3 t2 r i) = second
g2 (eq/ t3 t3 r i) = second
g2 (squash/ x y p q i j) = isSetTwo (g2 x) (g2 y) (λ i → g2 (p i)) (λ i → g2 (q i)) i j

isSetThree/R2 : isSet (Three / R2)
isSetThree/R2 x y p q = squash/ x y p q

sec2 : section f2 g2
sec2 = elimProp (λ x → isSetThree/R2 (f2 (g2 x)) x) lem where
  lem : (a : Three) → f2 (g2 [ a ]) ≡ [ a ]
  lem t1 = refl
  lem t2 = refl
  lem t3 = eq/ t2 t3 tt

ret2 : retract f2 g2
ret2 first = refl
ret2 second = refl

TwoIsoThree/R2 : Iso Two (Three / R2)
TwoIsoThree/R2 = iso f2 g2 sec2 ret2

TwoEquivThree/R2 : Two ≡ (Three / R2)
TwoEquivThree/R2 = isoToPath TwoIsoThree/R2

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

outOfTrue : True → True
outOfTrue = depElimTrue (λ x → True) tt

outOfTwo/R : (Two / R) → True
outOfTwo/R = depElimTwo/R (λ x → True) (λ x → isPropTrue) tt

isContrTrue : isContr True
isContrTrue = (tt , lem) where
  lem : (y : True) → tt ≡ y
  lem tt = refl

isContrTrue2 : isContr True
isContrTrue2 = (depConstrTrue , depElimTrue (λ x → depConstrTrue ≡ x) refl)

isContrTwo/R : isContr (Two / R)
isContrTwo/R = (depConstrTwo/R , depElimTwo/R (λ x → depConstrTwo/R ≡ x) (λ x → isSetTwoR depConstrTwo/R x) refl)

data Int : Set where
  pos : (n : Nat) → Int
  neg : (n : Nat) → Int

abs : Int -> Nat
abs (pos x) = x
abs (neg x) = x

rIntSign : Int -> Int -> Type
rIntSign (pos n) (pos n₁) = True
rIntSign (pos n) (neg n₁) = ⊥
rIntSign (neg n) (pos n₁) = ⊥
rIntSign (neg n) (neg n₁) = True

rNat : Nat -> Nat -> Type
rNat zero zero = True
rNat zero (suc b) = ⊥
rNat (suc a) zero = ⊥
rNat (suc a) (suc b) = rNat a b

rInt : Int -> Int -> Type
rInt a b = rNat (abs a) (abs b)

isSetInt/rInt : isSet (Int / rInt)
isSetInt/rInt x y p q = squash/ x y p q
isSetNat/rNat : isSet (Nat / rNat)
isSetNat/rNat x y p q = squash/ x y p q
{-
g' : (Int / rInt) -> Nat
g' [ a ] =  abs a
g' (eq/ a b r i) = {!!}
g' (squash/ a a₁ p q i i₁) = {!!}
-}

g'' : (Int / rInt) -> (Nat / rNat)
g'' [ a ] = [ abs a ]
g'' (eq/ a b r i) = eq/ (abs a) (abs b) r i
g'' (squash/ a b p q i j) = squash/ (g'' a) (g'' b) (cong g'' p) (cong g'' q) i j

f'' : (Nat / rNat) -> (Int / rInt)
f'' [ a ] = [ pos a ]
f'' (eq/ a b r i) = eq/ (pos a) (pos b) r i
f'' (squash/ a b p q i j) = squash/ (f'' a) (f'' b) (cong f'' p) (cong f'' q) i j


-- thoughts: is this necessary? this seems always true, metatheoretically.
-- can we try to always derive a form of this?
rNatEquiv : (a : Nat) -> (rNat a a)
rNatEquiv zero = tt
rNatEquiv (suc a) = rNatEquiv a

rIntPosNeg : (n : Nat) → (rInt (pos n) (neg n))
rIntPosNeg n = rNatEquiv n

sec'' : section f'' g''
sec'' = elimProp (λ x → isSetInt/rInt (f'' (g'' x)) x) lem where
  lem : (a : Int) → [ pos (abs a) ] ≡ [ a ]
  lem (pos n) = refl
  lem (neg zero) i = eq/ (pos zero) (neg zero) tt i
  lem (neg (suc n)) i = eq/ (pos (abs (neg (suc n)))) (neg (suc n)) (rIntPosNeg (suc n)) i

ret'' : retract f'' g''
ret'' = elimProp (λ x → isSetNat/rNat (g'' (f'' x)) x) lem where
  lem : (a : Nat) → [ a ] ≡ [ a ]
  lem a = refl

Int/rIntIsoNat/rNat : Iso (Int / rInt) (Nat / rNat)
Int/rIntIsoNat/rNat = iso g'' f'' ret'' sec''

g''' : (Nat / rNat) -> Nat
g''' [ a ] = a
g''' (eq/ zero zero r i) = zero
g''' (eq/ (suc a) (suc b) r i) = suc (g''' (eq/ a b r i))
g''' (squash/ a b p q i j) = isSetℕ (g''' a) (g''' b) (λ i → g''' (p i)) (λ i → g''' (q i)) i j


f''' : Nat -> (Nat / rNat)
f''' n = [ n ]

sec''' : section f''' g'''
sec''' = elimProp (λ x → isSetNat/rNat (f''' (g''' x)) x) lem where
  lem : (a : ℕ) → f''' a ≡ [ a ]
  lem a = refl


ret''' : retract f''' g'''
ret''' a = refl

Nat/rNatIsoNat : Iso (Nat / rNat) Nat
Nat/rNatIsoNat = iso g''' f''' ret''' sec'''

Int/rIntIsoNat : Iso (Int / rInt) Nat
Int/rIntIsoNat  = compIso Int/rIntIsoNat/rNat Nat/rNatIsoNat

{-
g2 : (Three / R2) → Two
g2 [ t1 ] = first
g2 [ t2 ] = second
g2 [ t3 ] = second
g2 (eq/ t1 t1 r i) = first
g2 (eq/ t2 t2 r i) = second
g2 (eq/ t2 t3 r i) = second
g2 (eq/ t3 t2 r i) = second
g2 (eq/ t3 t3 r i) = second
g2 (squash/ x y p q i j) = isSetTwo (g2 x) (g2 y) (λ i → g2 (p i)) (λ i → g2 (q i)) i j
-}

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
