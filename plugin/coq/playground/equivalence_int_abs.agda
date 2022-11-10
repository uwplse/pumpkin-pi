{-# OPTIONS --safe --cubical #-}
module equivalence_int_abs where

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

data True : Type where
  tt : True

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

g : (Int / rInt) -> (Nat / rNat)
g [ a ] = [ abs a ]
g (eq/ a b r i) = eq/ (abs a) (abs b) r i
g (squash/ a b p q i j) = squash/ (g a) (g b) (cong g p) (cong g q) i j

f : (Nat / rNat) -> (Int / rInt)
f [ a ] = [ pos a ]
f (eq/ a b r i) = eq/ (pos a) (pos b) r i
f (squash/ a b p q i j) = squash/ (f a) (f b) (cong f p) (cong f q) i j


-- thoughts: is this necessary? this seems always true, metatheoretically.
-- can we try to always derive a form of this?
rNatEquiv : (a : Nat) -> (rNat a a)
rNatEquiv zero = tt
rNatEquiv (suc a) = rNatEquiv a

rIntPosNeg : (n : Nat) → (rInt (pos n) (neg n))
rIntPosNeg n = rNatEquiv n

sec : section f g
sec = elimProp (λ x → isSetInt/rInt (f (g x)) x) lem where
  lem : (a : Int) → [ pos (abs a) ] ≡ [ a ]
  lem (pos n) = refl
  lem (neg zero) i = eq/ (pos zero) (neg zero) tt i
  lem (neg (suc n)) i = eq/ (pos (abs (neg (suc n)))) (neg (suc n)) (rIntPosNeg (suc n)) i

ret : retract f g
ret = elimProp (λ x → isSetNat/rNat (g (f x)) x) lem where
  lem : (a : Nat) → [ a ] ≡ [ a ]
  lem a = refl

Int/rIntIsoNat/rNat : Iso (Int / rInt) (Nat / rNat)
Int/rIntIsoNat/rNat = iso g f ret sec

g' : (Nat / rNat) -> Nat
g' [ a ] = a
g' (eq/ zero zero r i) = zero
g' (eq/ (suc a) (suc b) r i) = suc (g' (eq/ a b r i))
g' (squash/ a b p q i j) = isSetℕ (g' a) (g' b) (λ i → g' (p i)) (λ i → g' (q i)) i j

f' : Nat -> (Nat / rNat)
f' n = [ n ]

sec' : section f' g'
sec' = elimProp (λ x → isSetNat/rNat (f' (g' x)) x) lem where
  lem : (a : ℕ) → f' a ≡ [ a ]
  lem a = refl

ret' : retract f' g'
ret' a = refl

Nat/rNatIsoNat : Iso (Nat / rNat) Nat
Nat/rNatIsoNat = iso g' f' ret' sec'

Int/rIntIsoNat : Iso (Int / rInt) Nat
Int/rIntIsoNat  = compIso Int/rIntIsoNat/rNat Nat/rNatIsoNat


sucLemNat : (a : Nat) -> (b : Nat) -> suc (a + b) ≡ a + suc b
sucLemNat zero b = refl
sucLemNat (suc a) b = cong suc (sucLemNat a b)

addCommNat : (a : Nat) -> (b : Nat) -> (a + b ≡ b + a)
addCommNat zero zero = refl
addCommNat zero (suc b) = cong suc (addCommNat zero b)
addCommNat (suc a) zero = sucLemNat a zero ∙ addCommNat a 1
addCommNat (suc a) (suc b) = cong suc (addCommNat a (suc b)) ∙ cong suc (sucLemNat b a)

sucInt : Int -> Int
sucInt (pos n) = pos (suc n)
sucInt (neg n) = neg (suc n)

sucInt/rInt : (Int / rInt) -> (Int / rInt)
sucInt/rInt [ a ] = [ sucInt a ]
-- sucInt/rInt (eq/ a b r i) = eq/ (sucInt a) (sucInt b) r i                      -- why do I need to break into cases here???
sucInt/rInt (eq/ (pos a) (pos b) r i) = eq/ (sucInt (pos a)) (sucInt (pos b)) r i -- why do I need to break into cases here???
sucInt/rInt (eq/ (pos a) (neg b) r i) = eq/ (sucInt (pos a)) (sucInt (neg b)) r i
sucInt/rInt (eq/ (neg a) (pos b) r i) = eq/ (sucInt (neg a)) (sucInt (pos b)) r i
sucInt/rInt (eq/ (neg a) (neg b) r i) = eq/ (sucInt (neg a)) (sucInt (neg b)) r i
sucInt/rInt (squash/ a b p q i j) = squash/ (sucInt/rInt a) (sucInt/rInt b) (cong sucInt/rInt p) (cong sucInt/rInt q) i j


addInt/rInt : (Int / rInt) -> (Int / rInt) -> (Int / rInt)
addInt/rInt [ pos zero ] b = b
addInt/rInt [ pos (suc n) ] b = sucInt/rInt (addInt/rInt [ pos n ] b)
addInt/rInt [ neg zero ] b = b
addInt/rInt [ neg (suc n) ] b = sucInt/rInt (addInt/rInt [ neg n ] b)
addInt/rInt (eq/ (pos zero) (pos zero) r i) b = b
addInt/rInt (eq/ (pos (suc n)) (pos (suc a)) r i) b = sucInt/rInt (addInt/rInt (eq/ (pos n) (pos a) r i) b)
addInt/rInt (eq/ (pos zero) (neg zero) r i) b = b
addInt/rInt (eq/ (pos (suc n)) (neg (suc a)) r i) b = sucInt/rInt (addInt/rInt (eq/ (pos n) (neg a) r i) b)
addInt/rInt (eq/ (neg zero) (pos zero) r i) b = b
addInt/rInt (eq/ (neg (suc n)) (pos (suc a)) r i) b = sucInt/rInt (addInt/rInt (eq/ (neg n) (pos a) r i) b)
addInt/rInt (eq/ (neg zero) (neg zero) r i) b = b
addInt/rInt (eq/ (neg (suc n)) (neg (suc a)) r i) b = sucInt/rInt (addInt/rInt (eq/ (neg n) (neg a) r i) b)
addInt/rInt (squash/ a b p q i j) n = squash/ (addInt/rInt a n) (addInt/rInt b n) (cong (λ c → addInt/rInt c n) p) (cong (λ c → addInt/rInt c n) q) i j

sucLemInt/rInt : (a : Int / rInt) -> (b : Int / rInt) -> sucInt/rInt (addInt/rInt a b) ≡ (addInt/rInt a (sucInt/rInt b))
sucLemInt/rInt [ pos zero ] b = refl
sucLemInt/rInt [ pos (suc n) ] b = cong sucInt/rInt (sucLemInt/rInt [ pos n ] b)
sucLemInt/rInt [ neg zero ] b = refl
sucLemInt/rInt [ neg (suc n) ] b = cong sucInt/rInt (sucLemInt/rInt [ neg n ] b)
sucLemInt/rInt (eq/ (pos zero) (pos zero) r i) b = refl
sucLemInt/rInt (eq/ (pos zero) (neg zero) r i) b = refl
sucLemInt/rInt (eq/ (pos (suc n)) (pos (suc a)) r i) b = cong sucInt/rInt (sucLemInt/rInt (eq/ (pos n) (pos a) r i) b)
sucLemInt/rInt (eq/ (pos (suc n)) (neg (suc a)) r i) b = cong sucInt/rInt (sucLemInt/rInt (eq/ (pos n) (neg a) r i) b)
sucLemInt/rInt (eq/ (neg zero) (pos zero) r i) b = refl
sucLemInt/rInt (eq/ (neg zero) (neg zero) r i) b = refl
sucLemInt/rInt (eq/ (neg (suc n)) (pos (suc a)) r i) b = cong sucInt/rInt (sucLemInt/rInt (eq/ (neg n) (pos a) r i) b)
sucLemInt/rInt (eq/ (neg (suc n)) (neg (suc a)) r i) b = cong sucInt/rInt (sucLemInt/rInt (eq/ (neg n) (neg a) r i) b)
sucLemInt/rInt (squash/ a n p q i j) b = {!!}
  -- (sucLemInt/rInt
  --   -- (squash/ {!!} {!!} {!!} {!!} {!!} {!!})
  --   (squash/
  --     (sucInt/rInt (addInt/rInt {!!} b))
  --     (sucInt/rInt {!!})
  --     -- (addInt/rInt {!!} b)
  --     -- (addInt/rInt (sucInt/rInt {!!}) b)
  --     (λ i₁ → sucInt/rInt (addInt/rInt (p i₁) b))
  --     (λ i₁ → sucInt/rInt (addInt/rInt (q i₁) b)) i j
  --   )
  --   -- (squash/ (addInt/rInt a b) (addInt/rInt n b) (cong (λ c → addInt/rInt {! !} n) p) (cong {!!} q) i j)
  --   (addInt/rInt n b)
  -- )
  -- -- cong sucInt/rInt {!!}

addCommInt/rInt : (a : Int / rInt) -> (b : Int / rInt) -> ((addInt/rInt a b) ≡ (addInt/rInt b a))
addCommInt/rInt a b = {!!}

-- ∀ P p0 pS n (Q: P (DepConstr(1, N) n) → s),
-- Iota(1, N, Q) :
-- Q (pS n (DepElim(n, P) { p0, pS })) →
-- Q (DepElim(DepConstr(1, N) n, P) { p0, pS }).

-- addInt/rInt (squash/ a b p q i j) n = squash/ (addInt/rInt a n) (addInt/rInt b n) (cong (λ a₁ → {!!}) p) (cong (λ a₁ → {!!}) q) i j

-- sucLemInt/rInt : (a : Int / rInt) -> (b : Int / rInt) -> sucInt (sucInt/rInt a b) ≡ sucInt/rInt (a (sucInt b))
-- sucLemInt/rInt  = {!!}

-- sucLemInt/rInt : (a : Int / rInt) -> (b : Int / rInt) -> suc (a + b) ≡ a + suc b
-- sucLemInt/rInt zero b = refl
-- sucLemInt/rInt (suc a) b = cong suc (sucLem a b)


-- cong suc (addComm a b)
