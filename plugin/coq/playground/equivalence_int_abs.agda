{-# OPTIONS --safe --cubical #-}
module equivalence_int_abs where

open import Cubical.Core.Everything
open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Univalence
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

rNatEq : (a : Nat) -> (b : Nat) → (rNat a b) → a ≡ b
rNatEq zero zero x = refl
rNatEq (suc a) (suc b) x = cong suc (rNatEq a b x)

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

rIntPosNegQ : (n : Nat) -> ([_] {A = Int} {R = rInt} (pos n)  ≡ [_] {A = Int} {R = rInt} (neg n)) -- implicit args . . .
rIntPosNegQ n = eq/ (pos n) (neg n) (rIntPosNeg n)

-- todo: factor out using this lemma ^^^

sec : section f g
sec = elimProp (λ x → isSetInt/rInt (f (g x)) x) lem where
  lem : (a : Int) → [ pos (abs a) ] ≡ [ a ]
  lem (pos n) = refl
  lem (neg n) = rIntPosNegQ n

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

sucNat/rNat : (Nat / rNat) -> (Nat / rNat)
sucNat/rNat [ a ] = [ suc a ]
sucNat/rNat (eq/ a b r i) = eq/ (suc a) (suc b) r i
sucNat/rNat (squash/ a b p q i j) = squash/ (sucNat/rNat a) (sucNat/rNat b) (cong sucNat/rNat p) (cong sucNat/rNat q) i j

addNat/rNat : (Nat / rNat) -> (Nat / rNat) -> (Nat / rNat)
addNat/rNat [ zero ] b = b
addNat/rNat [ suc a ] b = addNat/rNat [ a ] (sucNat/rNat b)
addNat/rNat (eq/ zero zero r i) b = b
addNat/rNat (eq/ (suc a) (suc n) r i) b = addNat/rNat (eq/ a n r i) (sucNat/rNat b)
addNat/rNat (squash/ a b p q i j) n = squash/ (addNat/rNat a n) (addNat/rNat b n) (cong addN p) (cong addN q) i j where
  addN = (λ c → addNat/rNat c n)

addNat/rNat' : (Nat / rNat) -> (Nat / rNat) -> (Nat / rNat)
addNat/rNat' [ zero ] n = n
addNat/rNat' [ suc a ] n = sucNat/rNat (addNat/rNat' [ a ] (n))
addNat/rNat' (eq/ zero zero r i) n = n
addNat/rNat' (eq/ (suc a) (suc b) r i) n = sucNat/rNat (addNat/rNat' (eq/ a b r i) n)
addNat/rNat' (squash/ a b p q i j) n = squash/ (addNat/rNat' a n) (addNat/rNat' b n) (cong addN' p) (cong addN' q) i j where
  addN' = (λ c → addNat/rNat' c n)

-- Trying a version of this with the eliminator instead
sucLemNat/rNat'' : (a : Nat / rNat) -> (b : Nat / rNat) -> sucNat/rNat (addNat/rNat' a b) ≡ addNat/rNat' a (sucNat/rNat b)
sucLemNat/rNat'' a b = elimProp (λ x -> isSetNat/rNat (sucNat/rNat (addNat/rNat' x b)) (addNat/rNat' x (sucNat/rNat b))) (λ a -> lem a b) a where
  lem : (a : Nat) → (b : Nat / rNat) → sucNat/rNat (addNat/rNat' [ a ] b) ≡ addNat/rNat' [ a ] (sucNat/rNat b)
  lem zero b =  refl
  lem (suc a) b = cong sucNat/rNat (lem a b)


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
sucLemInt/rInt a b = elimProp (λ x → isSetInt/rInt (sucInt/rInt (addInt/rInt x b)) (addInt/rInt x (sucInt/rInt b))) (λ c → lem c b) a where
  lem : (a : Int) -> (b : Int / rInt) -> sucInt/rInt (addInt/rInt [ a ] b) ≡  (addInt/rInt [ a ] (sucInt/rInt b))
  lem (pos zero) b = refl
  lem (pos (suc n)) b = cong sucInt/rInt (lem (pos n) b)
  lem (neg zero) b = refl
  lem (neg (suc n)) b = cong sucInt/rInt (lem (neg n) b)

sucLemInt/rInt' : (a : Int / rInt) -> (b : Int / rInt) -> (addInt/rInt (sucInt/rInt a) b) ≡ sucInt/rInt (addInt/rInt a b)
sucLemInt/rInt' a b = elimProp (λ x → isSetInt/rInt (addInt/rInt (sucInt/rInt x) b) (sucInt/rInt (addInt/rInt x b))) (λ c → lem c b) a where
  lem : (a : Int) -> (b : Int / rInt) ->  (addInt/rInt (sucInt/rInt [ a ]) b) ≡ sucInt/rInt (addInt/rInt [ a ] b)
  lem (pos zero) b = refl
  lem (pos (suc n)) b = cong sucInt/rInt (lem (pos n) b)
  lem (neg zero) b = refl
  lem (neg (suc n)) b = cong sucInt/rInt (lem (neg n) b)

addCommInt/rInt : (a : Int / rInt) -> (b : Int / rInt) -> ((addInt/rInt a b) ≡ (addInt/rInt b a))
addCommInt/rInt a b = elimProp (λ x → isSetInt/rInt (addInt/rInt x b) (addInt/rInt b x)) (λ c → lem c b) a where
  lem : (a : Int) -> (b : Int / rInt) -> (addInt/rInt [ a ] b) ≡ (addInt/rInt b [ a ])
  lem a b = elimProp (λ x → isSetInt/rInt (addInt/rInt [ a ] x) (addInt/rInt x [ a ])) (λ c → lem' a c) b where
    lem' : (a : Int) -> (b : Int) -> (addInt/rInt [ a ] [ b ]) ≡ (addInt/rInt [ b ] [ a ])
    lem' (pos zero) (pos zero) = refl
    lem' (pos zero) (pos (suc n)) = cong sucInt/rInt (lem' (pos zero) (pos n))
    lem' (pos zero) (neg zero) = sym (rIntPosNegQ zero)
    lem' (pos zero) (neg (suc n)) = cong sucInt/rInt (lem' (pos zero) (neg n))
    lem' (pos (suc n)) (pos zero) = cong sucInt/rInt (lem' (pos n) (pos zero))
    lem' (pos (suc n)) (pos (suc b)) = cong sucInt/rInt (lem' (pos n) (pos (suc b))) ∙ cong sucInt/rInt (sucLemInt/rInt [ pos b ] [ pos n ])
    lem' (pos (suc n)) (neg zero) = cong sucInt/rInt (lem' (pos n) (neg zero))
    lem' (pos (suc n)) (neg (suc b)) = cong sucInt/rInt (lem' (pos n) (neg (suc b))) ∙ cong sucInt/rInt (sucLemInt/rInt [ neg b ] [ pos n ])
    lem' (neg zero) (pos zero) = rIntPosNegQ zero
    lem' (neg zero) (pos (suc n)) = cong sucInt/rInt (lem' (neg zero) (pos n))
    lem' (neg zero) (neg zero) = refl
    lem' (neg zero) (neg (suc n)) = cong sucInt/rInt (lem' (neg zero) (neg n))
    lem' (neg (suc n)) (pos zero) = cong sucInt/rInt (lem' (neg n) (pos zero))
    lem' (neg (suc n)) (pos (suc b)) = cong sucInt/rInt (lem' (neg n) (pos (suc b))) ∙ cong sucInt/rInt (sucLemInt/rInt [ pos b ] [ neg n ])
    lem' (neg (suc n)) (neg zero) = cong sucInt/rInt (lem' (neg n) (neg zero))
    lem' (neg (suc n)) (neg (suc b)) = cong sucInt/rInt (lem' (neg n) (neg (suc b))) ∙ cong sucInt/rInt (sucLemInt/rInt [ neg b ] [ neg n ])

depElimNat : (P : Nat -> Set) -> (P 0) -> (∀ n -> (P n) -> P (suc n)) -> ((x : Nat) -> P x)
depElimNat P baseCase sucCase zero = baseCase
depElimNat P baseCase sucCase (suc x) = sucCase x (depElimNat P baseCase sucCase x)

depElimNat/rNat : (P : Nat / rNat -> Set) -> (∀ x -> isProp (P x)) -> (P [ 0 ]) -> (∀ n -> (P n) -> P (sucNat/rNat n)) -> ((x : Nat / rNat) -> P x)
depElimNat/rNat P set baseCase sucCase = elimProp set lem where
  lem : (a : ℕ) → P [ a ]
  lem zero = baseCase
  lem (suc a) = sucCase [ a ] (lem a)

depElimInt/rInt : (P : Int / rInt -> Set) -> (∀ x -> isProp (P x)) -> (P [ pos 0 ]) -> (∀ n -> (P n) -> P (sucInt/rInt n)) -> ((x : Int / rInt) -> P x)
depElimInt/rInt P set baseCase sucCase = elimProp set lem where
  lem : (a : Int) → P [ a ]
  lem (pos zero) = baseCase
  lem (pos (suc n)) = sucCase [ pos n ] (lem (pos n))
  lem (neg zero) = subst P (eq/ (pos zero) (neg zero) tt) baseCase
  lem (neg (suc n)) = sucCase [ neg n ] (lem (neg n))

constantEq/Refl : {A : Type} -> {R : A -> A -> Type} -> (a : A) →  (r : R a a) → eq/ {R = R} a a r ≡ refl
constantEq/Refl a r = squash/ ([_] a) ([_] a) (eq/ a a r) refl

-- rNatEq : (a : Nat) -> (b : Nat) → (rNat a b) → a ≡ b
-- rNatEq zero zero x = refl
-- rNatEq (suc a) (suc b) x = cong suc (rNatEq a b x)

depElimSetNat/rNat : (P : Nat / rNat -> Set) -> (∀ x -> isSet (P x)) -> (P [ 0 ]) -> (∀ n -> (P n) -> P (sucNat/rNat n)) -> ((x : Nat / rNat) -> P x)
depElimSetNat/rNat P set baseCase sucCase = SetQuotients.elim set lem wellDefined where
  lem : (a : ℕ) → P [ a ]
  lem zero = baseCase
  lem (suc a) = sucCase [ a ] (lem a)
  wellDefined : (a b : ℕ) (r : rNat a b) → PathP (λ i → P (eq/ a b r i)) (lem a) (lem b) -- credit to Reed Mullanix for helping me prove this
  wellDefined zero zero tt = subst (λ x → PathP (λ i → P (x i)) baseCase baseCase) (sym (constantEq/Refl zero tt)) refl
  wellDefined (suc a) (suc b) r =
    transport
      (λ i → PathP (λ j → P (squash/ [ suc a ] [ suc b ] (λ i → [ suc (rNatEq a b r i) ]) (eq/ (suc a) (suc b) r) i j)) (sucCase [ a ] (lem a)) (sucCase [ b ] (lem b)))
      cool
    where
      cool : PathP (λ i → P (sucNat/rNat [ rNatEq a b r i ])) (sucCase [ a ] (lem a)) (sucCase [ b ] (lem b))
      cool i = sucCase [ rNatEq a b r i  ] (lem (rNatEq a b r i))


depConstrInt/rInt0 : Int / rInt
depConstrInt/rInt0 = [ pos 0 ]

depConstrInt/rIntS : Int / rInt -> Int / rInt
depConstrInt/rIntS = sucInt/rInt

rIntEq : (a : Int) -> (b : Int) -> (rInt a b) → ([_] {A = Int} {R = rInt} (a)  ≡ [_] {A = Int} {R = rInt} (b))
rIntEq a b r = eq/ a b r



rIntRefl : (a : Int) -> rInt a a
rIntRefl (pos n) = rNatEquiv n
rIntRefl (neg n) = rNatEquiv n

rIntEquiv : (a : Nat) → ([ pos a ] ≡ [ neg a ]) ≡ ([ pos a ] ≡ [ pos a ])
rIntEquiv a = subst (λ x → ([ pos a ] ≡ x) ≡ (([_] {R = rInt} (pos a)) ≡ [ pos a ])) (eq/ {R = rInt} (pos a) (neg a) (rIntPosNeg a)) refl

rIntEquivGen : (a : Int) -> (b : Int) -> (r : rInt a b) → ([ a ] ≡ [ b ]) ≡ ([ a ] ≡ [ a ])
rIntEquivGen a b r = subst (λ x → ([ a ] ≡ x) ≡ (([_] {R = rInt} a) ≡ [ a ])) (eq/ {R = rInt} a b r) refl

-- rIntTrue : { a b : Int } (p : rInt a b) -> Path {!!} (rInt a b) True
-- rIntTrue {pos zero} p = {!!}
-- rIntTrue {pos (suc n)} p = {!!}
-- rIntTrue {neg zero} p = {!!}
-- rIntTrue {neg (suc n)} p = {!!}

rIntSame : (a b : Int) -> (p : rInt a a) -> (q : rInt a b) -> PathP (λ x → {!!}) p q
rIntSame = {!!}

rIntPath : (n : ℕ) → (r1 : rInt (pos n) (neg n)) → (r2 : rInt (pos n) (pos n)) → (PathP (λ i → rIntEquiv n i) (eq/ (pos n) (neg n) r1) (eq/ (pos n) (pos n) r2))
rIntPath n r1 r2 = {!!}

rIntPathGenRefl : (a : Int) → (r : rInt a a) -> (PathP (λ i → rIntEquivGen a a r i) (eq/ a a r) (eq/ a a r))
rIntPathGenRefl a r = λ i → refl i

rIntPathGen' : (a : Int) → (r : rInt a a) -> (i : I) -> (PathP (λ i' → rIntEquivGen a a r ( i ∨ {!!})) (eq/ a a r i) [ a ])
-- rIntPathGen' : (a : Int) → (r : rInt a a) -> (i : I) -> Path (eq/ a a r i) [ a ]
rIntPathGen' a r = {!!}

rIntPathGen : (a : Int) (b : Int) → (r : rInt a b) -> (r' : rInt a a) → (PathP (λ i → rIntEquivGen a b r i) (eq/ a b r) (eq/ a a r'))
-- rIntPathGen a b r r' = transport-filler (rIntEquivGen a b r) (eq/ a b r) {!!}
rIntPathGen a b r r' = transport-filler (λ i → rIntEquivGen a b r i) (λ i → eq/ a b r i) {!!}

rIntEquivGen' : (a : Int) -> (b : Int) -> (r : rInt a b) → PathP (λ x → refl x) [ a ] [ b ]
rIntEquivGen' = λ a b r i j -> rIntEquivGen a b r j {!!}

-- rIntPathGen' : (a : Int) (b : Int) → (r : rInt a b) -> (r' : rInt a a) → (i' : I) → ((eq/ a b r i') ≡ (eq/ a a r' i'))
-- rIntPathGen' a b r r' = λ i j → rIntPathGen a b r r' {!i!}


-- λ j → rIntPathGen a b r r' {!!}
-- transport {!!} lem where
--   lem : (b : Int) -> (r : rInt a b) -> PathP (λ x → rIntEquivGen a b r x) (eq/ a b r) (eq/ a a r')
--   lem b' r' = λ i → {!!}

-- rIntEq' : (a : Nat) → PathP (λ x → Path {! !} (eq/ (pos a) (neg a) (rInt (pos a ) (neg a)) {!x!}) (eq/ (pos a) (pos a) (rInt (pos a) (pos a)) {!x!})) (eq/ (pos a) (neg a) (rInt (pos a) (neg a))) (eq/ (pos a) (pos a) (rInt (pos a) (neg a)))
-- eq/ (pos a) (neg a) {!rNat (pos a) (neg a)!} ≡ eq/ (pos a) {!pos b!} {!!} -- eq/ (pos a) (pos a) (rInt (pos a) (pos a)))

private
  variable
    ℓ ℓ' ℓ'' : Level

rrefl : ∀ x → rNat x x
rrefl zero    = tt
rrefl (suc x) = rrefl x

rJ
  : ∀ x (P : (y : Nat) → rNat x y → Type)
  → P x (rrefl x)
  → ∀ {y} r → P y r
rJ zero P pr {zero} tt = pr
rJ (suc x) P pr {suc y} r = rJ x (λ y → P (suc y)) pr r

quot : ∀ {ℓ ℓ'} {A : Type ℓ} {R : A → A → Type ℓ'} {x y : A} → R x y
    → Path (A / R) ([ x ]) ([ y ])
quot {x = x} {y = y} r = eq/ x y r

to-pathp : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
         → transport (λ i → A i) x ≡ y
         → PathP A x y
to-pathp {A = A} {x} {y} p = transport (sym (PathP≡Path A x y)) p

to-pathp⁻ : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
         → x ≡ transport (λ i → A (~ i)) y
         → PathP A x y
to-pathp⁻ {A = A} {x} {y} p = transport (sym (PathP≡Path⁻ A x y)) p

-- transport (λ i → P (eq/ _ _ (rrefl n) i)) (sucCase [ pos n ] (lem (pos n))) ≡ transport (λ i → P (eq/ (pos (suc n)) (neg (suc n)) (suc n) i)) (sucCase [ pos n ] (lem (pos n)))

depElimSetInt/rInt : (P : Int / rInt -> Set) -> (∀ x -> isSet (P x)) -> (P depConstrInt/rInt0) -> (∀ n -> (P n) -> P (depConstrInt/rIntS n)) -> ((x : Int / rInt) -> P x)
depElimSetInt/rInt P set baseCase sucCase = SetQuotients.elim set lem wellDefined where
  lem : (a : Int) → P [ a ]
  lem (pos zero) = baseCase
  lem (pos (suc n)) =  sucCase [ pos n ] (lem (pos n))
  lem (neg zero) = transport (cong P (quot (rrefl 0))) (lem (pos zero))
  lem (neg (suc n)) = transport (cong P (quot (rrefl (suc n)))) (sucCase [ pos n ] (lem (pos n))) -- sucCase [ neg n ] (lem (neg n))
  wellDefined : (a b : Int) (r : rInt a b) → PathP (λ i → P (eq/ a b r i)) (lem a) (lem b)
  wellDefined (pos x) (pos y) r = rJ x
    (λ y r → PathP (λ i → P (quot {R = rInt} r i)) (lem (pos x)) (lem (pos y)))
    (subst (λ e → PathP (λ i → P (e i)) (lem (pos x)) (lem (pos x)))
      (squash/ {R = rInt} [ pos x ] [ pos x ] refl (quot (rrefl x)))
      λ i → lem (pos x))
    r
  wellDefined (pos x) (neg y) r = rJ x
    (λ y r → PathP (λ i → P (quot {R = rInt} r i)) (lem (pos x)) (lem (neg y)))
    (to-pathp
      (Cubical.Data.Nat.elim
        {A = λ n → transport (λ i → P (quot (rrefl n) i)) (lem (pos n)) ≡ (lem (neg n))}
        refl
        (λ _ _ → refl)
        x))
    r
  wellDefined (neg x) (pos y) r = rJ x
    (λ y r → PathP (λ i → P (quot {R = rInt} r i)) (lem (neg x)) (lem (pos y)))
    (to-pathp⁻ {!!})
    r
  wellDefined (neg x) (neg y) r = rJ x
    (λ y r → PathP (λ i → P (quot {R = rInt} r i)) (lem (neg x)) (lem (neg y)))
    (subst (λ e → PathP (λ i → P (e i)) (lem (neg x)) (lem (neg x)))
      (squash/ {R = rInt} [ neg x ] [ neg x ] refl (quot (rrefl x)))
      λ i → lem (neg x))
    r

-- P i x

-- [ a ] ≡ (eq/ a b r i)
-- P [ a ] ≡ P (eq/ a b r i)

-- Goal: P [ a ] ≡ P (eq/ a b r i)
-- ————————————————————————————————————————————————————————————
-- i        : I
-- r        : rInt a b
-- b        : Int
-- a        : Int
-- sucCase  : (n : Int / rInt) → P n → P (depConstrInt/rIntS n)
-- baseCase : P depConstrInt/rInt0
-- set      : (x : Int / rInt) → isSet (P x)
-- P        : Int / rInt → Type

-- Goal: P (eq/ a b r i)
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ lem a
-- i = i1 ⊢ lem b




-- cong′ (λ x → transport (x {!i!}) {!!}) (λ i → rIntPathGen a b r (rIntRefl a)) i

  -- cong′ (λ x i → {!lem !}) {!!} {!!} -- cong {!lem!} {!!} -- (cong′  (λ x → {!P !}) {!!}) {!!}

-- (cong′ {!!} {!!})
-- P [ a ] ≡ PathP (λ i → P (eq/ a b r i)) (lem a) (lem b)

-- cong′ (λ x i → {!!}) ( λ i → rIntPathGen a b r (rIntRefl a)) {!!} -- cong (λ a₁ → {!lem!}) (rIntEquivGen a b r)
  -- rIntPathGen a b r (rIntRefl a)
-- transport (λ i₁ → cong (λ a₁ → P a₁) (rIntPathGen a b r (rIntRefl a) {!i₁ !}) {!!} ) (lem a)


  -- wellDefined (pos zero) (pos zero) r i = {!!}
  -- transport (λ i → {!PathP!}) cool
  --   where
  --     cool : PathP (λ x → P (eq/ (pos zero) (pos zero) r i)) {!baseCase!} {!lem (pos zero) !}
  --     cool = refl
-- Goal: P (eq/ (pos zero) (pos zero) r i)
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ baseCase
-- i = i1 ⊢ baseCase
-- ————————————————————————————————————————————————————————————
-- i        : I
-- r        : rInt (pos zero) (pos zero)
-- sucCase  : (n : Int / rInt) → P n → P (depConstrInt/rIntS n)
-- baseCase : P depConstrInt/rInt0
-- set      : (x : Int / rInt) → isSet (P x)
-- P        : Int / rInt → Type


  -- wellDefined (pos zero) (neg zero) r i =  transport (cong (λ a → P a) {!!}) (lem (pos zero))

-- transport (cong {!P!} (rIntEq' (pos zero) (neg zero) r i)) (lem (pos zero))
-- Goal: P [ pos zero ] ≡ P (eq/ (pos zero) (neg zero) r i)
-- ————————————————————————————————————————————————————————————
-- i        : I
-- r        : rInt (pos zero) (neg zero)
-- sucCase  : (n : Int / rInt) → P n → P (depConstrInt/rIntS n)
-- baseCase : P depConstrInt/rInt0
-- set      : (x : Int / rInt) → isSet (P x)
-- P        : Int / rInt → Type


  -- wellDefined (pos (suc a)) (pos (suc b)) r i = transport (λ i → {!!}) {!!}
  -- wellDefined (pos (suc a)) (neg (suc b)) r i = transport (λ i → {!!}) {!!}
  -- wellDefined (neg zero) (pos zero) r i = transport (λ i → {!!}) {!!}
  -- wellDefined (neg zero) (neg zero) r i = transport (λ i → {!!}) {!!}
  -- wellDefined (neg (suc a)) (pos (suc b)) r i = transport (λ i → {!!}) {!!}
  -- wellDefined (neg (suc a)) (neg (suc b)) r i = transport (λ i → {!!}) {!!}
    -- where
    --   cool : PathP (λ x → P (eq/ (neg a) b r i0)) (lem (neg a)) (lem (neg a))
    --   cool = refl

    -- transport (λ i → PathP (λ j → P (squash/ [ suc a ] [ suc b ] (λ i → [ suc (rNatEq a b r i) ]) (eq/ (suc a) (suc b) r) i j)) (sucCase [ a ] (lem a)) (sucCase [ b ] (lem b))) cool
    -- where
    --   cool : PathP (λ i → P (sucNat/rNat [ rNatEq a b r i ])) (sucCase [ a ] (lem a)) (sucCase [ b ] (lem b))
    --   cool i = sucCase [ rNatEq a b r i  ] (lem (rNatEq a b r i))
  -- where
  --   cool : PathP (λ i → P (depConstrInt/rIntS [ rNatEq a b r i ])) (sucCase [ a ] (lem a)) (sucCase [ b ] (lem b))
  --   cool = {!!}


-- Goal: PathP (λ i → P (eq/ a b r i)) (lem a) (lem b)
-- ————————————————————————————————————————————————————————————
-- r        : rInt a b
-- b        : Int
-- a        : Int
-- sucCase  : (n : Int / rInt) → P n → P (depConstrInt/rIntS n)
-- baseCase : P depConstrInt/rInt0
-- set      : (x : Int / rInt) → isSet (P x)
