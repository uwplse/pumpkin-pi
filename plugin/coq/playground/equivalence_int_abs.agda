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
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.CartesianKanOps

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

-- path equality corresponding to this isomorphism
Nat≡Int/rInt : Nat ≡ Int / rInt
Nat≡Int/rInt = sym (isoToPath Int/rIntIsoNat)

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

-- dependent set eliminator for Nat/rNat
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

-- dependent constructors for Int/rInt
depConstrInt/rInt0 : Int / rInt
depConstrInt/rInt0 = [ pos 0 ]

depConstrInt/rIntS : Int / rInt -> Int / rInt
depConstrInt/rIntS = sucInt/rInt

-- from Amelia?
rrefl : ∀ x → rNat x x
rrefl zero    = tt
rrefl (suc x) = rrefl x

-- from Amelia
rJ
  : ∀ x (P : (y : Nat) → rNat x y → Type)
  → P x (rrefl x)
  → ∀ {y} r → P y r
rJ zero P pr {zero} tt = pr
rJ (suc x) P pr {suc y} r = rJ x (λ y → P (suc y)) pr r

-- there is a path between any eq/ and its reversal
eq≡eqRev/ : ∀ (x y : Int) (r1 : rInt x y) (r2 : rInt y x) →
  (λ i → eq/ {R = rInt} x y r1 i) ≡ (λ i → eq/ {R = rInt} y x r2 (~ i))
eq≡eqRev/ x y r1 r2 =
  squash/ {R = rInt} [ x ] [ y ] (λ i → eq/ x y r1 i) (λ i → eq/ y x r2 (~ i))

-- thus, we can get between transporting in either direction
transportEq≡transportEqRev/ : ∀ n (r1 : rInt (pos n) (neg n)) (r2 : rInt (neg n) (pos n)) (req : r1 ≡ r2) (P : Int / rInt → Set) (px : P [ pos n ]) →
  transport (λ i → P (eq/ {R = rInt} (pos n) (neg n) r1 i)) px ≡ transport (λ i → P (eq/ {R = rInt} (neg n) (pos n) r2 (~ i))) px
transportEq≡transportEqRev/ n r1 r2 req P px =
  subst
    (λ (H : [ neg n ] ≡ [ pos n ]) → transport ( λ i → P (H (~ i))) px ≡ transport (λ i → P (eq/ (neg n) (pos n) r2 (~ i))) px)
    (eq≡eqRev/ (neg n) (pos n) r1 r1)
    (subst
      (λ (r : rInt (pos n) (neg n)) → transport (λ i → P (eq/ (neg n) (pos n) r1 (~ i))) px ≡ transport (λ i → P (eq/ (neg n) (pos n) r (~ i))) px)
      req
      refl)

-- dependent eliminator for Int/rInt over Set (thanks to Amelia for helping us figure this out)
depElimSetInt/rInt : (P : Int / rInt -> Set) -> (∀ x -> isSet (P x)) -> (P depConstrInt/rInt0) -> (∀ n -> (P n) -> P (depConstrInt/rIntS n)) -> ((x : Int / rInt) -> P x)
depElimSetInt/rInt P set baseCase sucCase = SetQuotients.elim set lem wellDefined where
  -- points
  lem : (a : Int) → P [ a ]
  lem (pos zero) = baseCase
  lem (pos (suc n)) =  sucCase [ pos n ] (lem (pos n))
  lem (neg zero) =
    transport
      (cong P (eq/ (pos zero) (neg zero) (rrefl 0)))
      (lem (pos zero))
  lem (neg (suc n)) =
    transport
      (cong P (eq/ (pos (suc n)) (neg (suc n)) (rrefl (suc n))))
      (sucCase [ pos n ] (lem (pos n)))
  -- paths
  wellDefined : (a b : Int) (r :  rInt a b) → PathP (λ i → P (eq/ a b r i)) (lem a) (lem b)
  wellDefined (pos x) (pos y) r = rJ x
    (λ y r → PathP (λ i → P (eq/ (pos x) (pos y) r i)) (lem (pos x)) (lem (pos y)))
    (subst
      (λ e → PathP (λ i → P (e i)) (lem (pos x)) (lem (pos x)))
      (sym (constantEq/Refl (pos x) (rrefl x)))
      (λ i → lem (pos x)))
    r
  wellDefined (neg x) (neg y) r = rJ x
    (λ y r → PathP (λ i → P (eq/ (neg x) (neg y) r i)) (lem (neg x)) (lem (neg y)))
    (subst
      (λ e → PathP (λ i → P (e i)) (lem (neg x)) (lem (neg x)))
      (sym (constantEq/Refl (neg x) (rrefl x)))
      (λ i → lem (neg x)))
    r
  wellDefined (pos x) (neg y) r = rJ x
    (λ y r → PathP (λ i → P (eq/ (pos x) (neg y) r i)) (lem (pos x)) (lem (neg y)))
    (toPathP -- transport (λ i → A i) x ≡ y → PathP A x y
      (Cubical.Data.Nat.elim
        {A = λ n → transport (λ i → P (eq/ (pos n) (neg n) (rrefl n) i)) (lem (pos n)) ≡ (lem (neg n))}
        refl
        (λ _ _ → refl)
        x))
    r
  wellDefined (neg x) (pos y) r = rJ x
    (λ y r → PathP (λ i → P (eq/ (neg x) (pos y) r i)) (lem (neg x)) (lem (pos y)))
    (toPathP⁻ -- x ≡ transport (λ i → A i) y → PathP A x y
      (Cubical.Data.Nat.elim
        {A = λ n → lem (neg n) ≡ transport {A = P [ pos n ]} {B = P [ neg n ]} (λ i → P (eq/ (neg n) (pos n) (rrefl n) (~ i))) (lem (pos n)) }
        (transportEq≡transportEqRev/ zero tt tt refl P baseCase)
        (λ n _ → transportEq≡transportEqRev/ (suc n) (rrefl (suc n)) (rrefl (suc n)) refl P (sucCase [ pos n ] (lem (pos n))))
        x))
    r

-- ι for the Set eliminator
ιInt/rInt0 : (P : Int / rInt → Set) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) →
    (Q : P depConstrInt/rInt0 → Set) → Q (depElimSetInt/rInt P pset pz ps depConstrInt/rInt0) → Q pz
ιInt/rInt0 P pset pz ps Q qz = qz 

ιInt/rIntSEq : (P : Int / rInt → Set) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS n) ≡ ps n (depElimSetInt/rInt P pset pz ps n)
ιInt/rIntSEq P pset pz ps = elimProp prop fpoint where
  fpoint : (x : Int) → depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS [ x ]) ≡ ps [ x ] (depElimSetInt/rInt P pset pz ps [ x ])
  fpoint (pos n) = refl
  fpoint (neg n) = subst (λ e → depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS e) ≡ ps e (depElimSetInt/rInt P pset pz ps e)) (rIntPosNegQ n) refl
  -- it's OK to use elimProp:
  prop : (n : Int / rInt) → isProp (depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS n) ≡ ps n (depElimSetInt/rInt P pset pz ps n))
  prop n p q = pset (depConstrInt/rIntS n) (depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS n)) (ps n (depElimSetInt/rInt P pset pz ps n)) p q

ιInt/rIntS : (P : Int / rInt → Set) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    (Q : P (depConstrInt/rIntS n) → Set) → 
    Q (depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS n)) →
    Q (ps n (depElimSetInt/rInt P pset pz ps n))
ιInt/rIntS P pset pz ps n Q Qb = subst (λ e → Q e) (ιInt/rIntSEq P pset pz ps n) Qb

ιInt/rIntS⁻ : (P : Int / rInt → Set) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    (Q : P (depConstrInt/rIntS n) → Set) → 
    Q (ps n (depElimSetInt/rInt P pset pz ps n)) →
    Q (depElimSetInt/rInt P pset pz ps (depConstrInt/rIntS n))
ιInt/rIntS⁻ P pset pz ps n Q Qb = subst (λ e → Q e) (sym (ιInt/rIntSEq P pset pz ps n)) Qb

-- ι for the Prop eliminator
ιInt/rInt0Prop : (P : Int / rInt → Set) → (pprop : ∀ x → isProp (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) →
  (Q : P depConstrInt/rInt0 → Set) → Q (depElimInt/rInt P pprop pz ps depConstrInt/rInt0) → Q pz
ιInt/rInt0Prop P pprop pz ps Q qz = qz

ιInt/rIntSPropEq : (P : Int / rInt → Set) → (pprop : ∀ x → isProp (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    depElimInt/rInt P pprop pz ps (depConstrInt/rIntS n) ≡ ps n (depElimInt/rInt P pprop pz ps n)
ιInt/rIntSPropEq P pprop pz ps = elimProp prop fpoint where
  fpoint : (x : Int) → depElimInt/rInt P pprop pz ps (depConstrInt/rIntS [ x ]) ≡ ps [ x ] (depElimInt/rInt P pprop pz ps [ x ])
  fpoint (pos n) = refl
  fpoint (neg n) = subst (λ e → depElimInt/rInt P pprop pz ps (depConstrInt/rIntS e) ≡ ps e (depElimInt/rInt P pprop pz ps e)) (rIntPosNegQ n) refl
  -- it's OK to use elimProp:
  prop : (n : Int / rInt) → isProp (depElimInt/rInt P pprop pz ps (depConstrInt/rIntS n) ≡ ps n (depElimInt/rInt P pprop pz ps n))
  prop n p q = isProp→isSet (pprop (depConstrInt/rIntS n)) (depElimInt/rInt P pprop pz ps (depConstrInt/rIntS n)) (ps n (depElimInt/rInt P pprop pz ps n)) p q

ιInt/rIntSProp : (P : Int / rInt → Set) → (pprop : ∀ x → isProp (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    (Q : P (depConstrInt/rIntS n) → Set) → 
    Q (depElimInt/rInt P pprop pz ps (depConstrInt/rIntS n)) →
    Q (ps n (depElimInt/rInt P pprop pz ps n))
ιInt/rIntSProp P pprop pz ps n Q Qb = subst (λ e → Q e) (ιInt/rIntSPropEq P pprop pz ps n) Qb

ιInt/rIntSProp⁻ : (P : Int / rInt → Set) → (pprop : ∀ x → isProp (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    (Q : P (depConstrInt/rIntS n) → Set) → 
    Q (ps n (depElimInt/rInt P pprop pz ps n)) →
    Q (depElimInt/rInt P pprop pz ps (depConstrInt/rIntS n))
ιInt/rIntSProp⁻ P pprop pz ps n Q Qb = subst (λ e → Q e) (sym (ιInt/rIntSPropEq P pprop pz ps n)) Qb

-- 3.1.6 in the HoTT book
isSetProd : ∀ {A : Type} {B : A → Type} → (∀ (a : A) → isSet (B a)) → isSet (∀ (a : A) → B a)
isSetProd {A} {B} setB =
   λ (f g : ∀ (a : A) → B a) (p q : f ≡ g) →
     cong funExt (funExt (λ (a : A) → setB a (f a) (g a) (funExt⁻ p a) (funExt⁻ q a)))

-- Porting functions to nat-like eliminators
add' : (a : ℕ) → (b : ℕ) → ℕ
add' a b =
  Cubical.Data.Nat.elim
    {A = λ _ → ℕ → ℕ} -- motive P
    (λ b → b) -- P 0
    (λ a IH b → suc (IH b)) -- ∀ n, P n → P (S n)
    a
    b

addInt/rInt' : (Int / rInt) -> (Int / rInt) -> (Int / rInt)
addInt/rInt' a b =
  depElimSetInt/rInt
    (λ _ → Int / rInt → Int / rInt) -- motive P
    (λ (_ : Int / rInt) → isSetProd (λ _ → squash/)) -- ∀ n, isSet (P n)
    (λ b → b) -- P depConstrInt/rInt0
    (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m)) -- ∀ n, P n → P (depConstrInt/rIntS n)
    a
    b

-- A couple simple tests
addOKPos : addInt/rInt' [ pos 5 ] [ pos 6 ] ≡ [ pos 11 ]
addOKPos = refl

addOKNeg : addInt/rInt' [ neg 2 ] [ neg 7 ] ≡ [ neg 9 ]
addOKNeg = refl

-- Proof of correctness of repaired function
addCorrect :
  ∀ (a b : ℕ) (a' b' : Int / rInt) →
  ∀ (pa : PathP (λ i → Nat≡Int/rInt i) a a') (pb : PathP (λ i → Nat≡Int/rInt i) b b') →
  PathP (λ i → Nat≡Int/rInt i) (add' a b) (addInt/rInt' a' b')
addCorrect a b a' b' pa pb =
  JDep
    {A = Nat}
    {B = λ _ → Int / rInt}
    (λ y p z q → PathP (λ i → Nat≡Int/rInt i) y z)
    (Cubical.Data.Nat.elim
      {A = λ a → ∀ (a' : Int / rInt) (pa : PathP (λ i → Nat≡Int/rInt i) a a') →
        PathP (λ i → Nat≡Int/rInt i) (add' a b) (addInt/rInt' (transport (λ i → Nat≡Int/rInt i) a) b')}
      (λ _ _ → pb)
      (λ a (IHa : ∀ a' pa → PathP _ (add' a b) (addInt/rInt' (transport (λ i → Nat≡Int/rInt i) a) b')) a' pa →
        toPathP
          (cong
            depConstrInt/rIntS
            (fromPathP (IHa (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl)))))
      a
      a'
      pa)
    refl
    (subst
      {x = a'}
      {y = transport Nat≡Int/rInt a}
      (λ (z : Int / rInt) → addInt/rInt' z b' ≡  addInt/rInt' a' b')
      (sym (fromPathP pa))
      refl)

{- Correctness for dependent constructors and eliminators -}

depConstr0Correct : PathP (λ i → Nat≡Int/rInt i) zero depConstrInt/rInt0
depConstr0Correct = toPathP refl

depConstr0CorrectIrrel : depConstr0Correct ≡ toPathP refl
depConstr0CorrectIrrel = refl

depConstrSCorrect :
  ∀ a b → PathP (λ i → Nat≡Int/rInt i) a b → PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)
depConstrSCorrect a b a≡b =
  toPathP (cong depConstrInt/rIntS (fromPathP a≡b))

depConstrSCorrectIrrel : ∀ (a : Nat) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) (Sa≡Sb : PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)) →
  depConstrSCorrect a b a≡b ≡ Sa≡Sb
depConstrSCorrectIrrel a b a≡b Sa≡Sb =
  subst2
    (λ (Sa≡Sb Sa≡Sb' : PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)) → Sa≡Sb' ≡ Sa≡Sb)
    (Iso.leftInv (PathPIsoPath (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)) Sa≡Sb)
    (Iso.leftInv (PathPIsoPath (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)) (depConstrSCorrect a b a≡b))
    (cong
      (toPathP {A = λ i → Nat≡Int/rInt i})
      (squash/ (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a)) (depConstrInt/rIntS b) (fromPathP (depConstrSCorrect a b a≡b)) (fromPathP Sa≡Sb)))

-- Yay! May try to simplify proof a lot, use to prove other things, think about automation
elimOK : -- based on elim_OK from the PLDI 2021 paper
  ∀ (a : Nat) (b : Int / rInt) →
  ∀ (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  ∀ (PA : Nat → Type) (PB : Int / rInt → Type) (PBSet : ∀ b → isSet (PB b)) →
  ∀ (PA≡PB : PathP (λ i → (Nat≡Int/rInt i) → Type) PA PB) →
  ∀ (PAO : PA zero) (PBO : PB depConstrInt/rInt0) →
  ∀ (PAO≡PBO : PathP (λ i → (PA≡PB i) (depConstr0Correct i)) PAO PBO) →
  ∀ (PAS : ∀ a → PA a → PA (suc a)) (PBS : ∀ b → PB b → PB (depConstrInt/rIntS b)) →
  ∀ (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB i (a≡b i)) IHa IHb) → PathP (λ i → (PA≡PB i) (depConstrSCorrect a b a≡b i)) (PAS a IHa) (PBS b IHb)) →
  PathP (λ i → (PA≡PB i) (a≡b i)) (Cubical.Data.Nat.elim {A = PA} PAO PAS a) (depElimSetInt/rInt PB PBSet PBO PBS b)
elimOK a b a≡b PA PB PBSet PA≡PB PAO PBO PAO≡PBO PAS PBS PAS≡PBS =
  J -- adjust a≡b from pathP to path to make it easy to use JDep
    (λ a≡b' (H : toPathP (fromPathP a≡b) ≡ a≡b') →
      PathP (λ i → (PA≡PB i (a≡b' i))) (Cubical.Data.Nat.elim {A = PA} PAO PAS a) (depElimSetInt/rInt PB PBSet PBO PBS b))
    (JDep -- adjust to a homogeneous PathP about proofs about a
       {A = Int / rInt}
       {B = λ (b : Int / rInt) → PB b}
       {b =  depElimSetInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)}
       (λ (b : Int / rInt) (a≡b : transport (λ i → Nat≡Int/rInt i) a ≡ b) (PBb : PB b)
          (p : PathP (λ i → PB (a≡b i)) (depElimSetInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)) PBb) →
         PathP (λ i → PA≡PB i (toPathP {A = λ i → Nat≡Int/rInt i} a≡b i)) (Cubical.Data.Nat.elim {A = PA} PAO PAS a) (depElimSetInt/rInt PB PBSet PBO PBS b))
       (Cubical.Data.Nat.elim
         {A = λ (a : Nat) →
           PathP
             (λ i → PA≡PB i (toPathP {A = λ i → Nat≡Int/rInt i} (refl {x = transport (λ i → Nat≡Int/rInt i) a}) i))
             (Cubical.Data.Nat.elim PAO PAS a)
             (depElimSetInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a))}
         PAO≡PBO -- base case holds by PAO≡PBO
         (λ (a : Nat) IHa → -- inductive case holds by ι of PAS≡PBS
           (subst -- adjust to refl
            {A = PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a))}
            {x = depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl)}
            {y = toPathP {A = λ i → Nat≡Int/rInt i} refl}
            (λ (Sa≡Sa : PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a))) →
              PathP (λ i → PA≡PB i (Sa≡Sa i)) (PAS a (Cubical.Data.Nat.elim PAO PAS a)) (depElimSetInt/rInt PB PBSet PBO PBS (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a))))
            (depConstrSCorrectIrrel a (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl) (toPathP refl))
            (ιInt/rIntS⁻ -- ι reduce the successor case for proofs about Int/rInt
              PB
              PBSet
              PBO
              PBS
              (transport (λ i → Nat≡Int/rInt i) a)
              (λ PBSa →
                PathP (λ i → PA≡PB i (depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl) i)) (PAS a (Cubical.Data.Nat.elim PAO PAS a)) PBSa)
              (PAS≡PBS a (transport (λ i → Nat≡Int/rInt i) a) (Cubical.Data.Nat.elim PAO PAS a) (depElimSetInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)) (toPathP refl) IHa))))
           a)
       {y = b}
       (fromPathP a≡b)
       {z = depElimSetInt/rInt PB PBSet PBO PBS b}
       (J -- reduce to refl
          (λ (b : Int / rInt) (a≡b : transport (λ i → Nat≡Int/rInt i) a ≡ b) →
            PathP (λ i → PB (fromPathP a≡b i)) (depElimSetInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)) (depElimSetInt/rInt PB PBSet PBO PBS b))
          refl
          (fromPathP {A = λ i → Nat≡Int/rInt i} a≡b)))
    (Iso.leftInv (PathPIsoPath (λ i → Nat≡Int/rInt i) a b) a≡b)

{- Correctness for the other derivations (needed so we can use elimOK on particular functions and proofs) -}

-- equivalence is OK by A≡B
equivOK : Nat ≡ Int / rInt
equivOK = Nat≡Int/rInt

-- application: app is OK by congP
appOK : {T : I → Type} {F : (i : I) → T i → Type}
  (f : (t : T i0) → F i0 t) (f' : (t : T i1) → F i1 t)
  (f≡f' : PathP (λ i → ∀ (t : T i) → F i t) f f')
  (t : T i0) (t' : T i1)
  (t≡t' : PathP T t t') →
  PathP (λ i → F i (t≡t' i)) (f t) (f' t')
appOK f f' f≡f' t t' t≡t' = congP (λ i a → f≡f' i a) t≡t'

-- term abstraction: lam is OK by funExtDep (TODO is this type signature correct though, or too specific?)
lamOK : {T : I → Type} {F : (i : I) → T i → Type}
  (f : (t : T i0) → F i0 t) (f' : (t : T i1) → F i1 t)
  (b≡b' : ∀ {t : T i0} {t' : T i1} (t≡t' : PathP (λ i → T i) t t') →
    PathP (λ i → F i (t≡t' i)) (f t) (f' t')) →
  PathP (λ i → ∀ (t : T i) → F i t) f f'
lamOK {T} {F} f f' b≡b' =
  funExtDep b≡b'

-- type abstraction: prod is OK by funExtDep (TODO is this type signature correct though, or too specific?)
prodOK : {T : I → Type} (F : (i : I) → T i → Type)
  (b≡b' : ∀ {t : T i0} {t' : T i1} (t≡t' : PathP (λ i → T i) t t') →
    PathP (λ i → Type) (F i0 t) (F i1 t')) →
  PathP (λ i → T i → Type) (F i0) (F i1)
prodOK {T} F b≡b' = funExtDep b≡b'

-- variables: var is OK by refl
var : ∀ {T : I → Type} (i : I) (v : T i) → v ≡ v
var {T} i v = refl

-- iota: iota is OK at 0 by QAzero≡QBzero
ιOK0 : (PA : Nat → Type) (PB : Int / rInt → Type)
  (PA≡PB : PathP (λ i → Nat≡Int/rInt i → Type) PA PB)
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → (PA≡PB i) (depConstr0Correct i)) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB i (a≡b i)) IHa IHb) → PathP (λ i → (PA≡PB i) (depConstrSCorrect a b a≡b i)) (PAS a IHa) (PBS b IHb))
  (QA : PA zero → Type) (QB : PB depConstrInt/rInt0 → Type)
  (QA≡QB : PathP (λ i → (PA≡PB i) (depConstr0Correct i) → Type) QA QB)
  (QAzero : QA PAzero) (QBzero : QB PBzero)
  (QAzero≡QBzero : PathP (λ i → (QA≡QB i) (PAzero≡PBzero i)) QAzero QBzero) → 
  PathP (λ i → (QA≡QB i) (PAzero≡PBzero i)) QAzero (ιInt/rInt0 PB PBset PBzero PBS QB QBzero)
ιOK0 PA PB PA≡PB PBSet PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS QA QB QA≡QB QAzero QBzero QAzero≡QBzero =
  QAzero≡QBzero

-- iota: iota is OK at S (it's cool to lift definitional to propositional equality) because we are eliminating into set (equality first)
ιOKSEq : (PA : Nat → Type) (PB : Int / rInt → Type)
  (PA≡PB : PathP (λ i → Nat≡Int/rInt i → Type) PA PB)
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → (PA≡PB i) (depConstr0Correct i)) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB i (a≡b i)) IHa IHb) → PathP (λ i → (PA≡PB i) (depConstrSCorrect a b a≡b i)) (PAS a IHa) (PBS b IHb))
  (a : Nat) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  PathP
    (λ i →
      elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
      PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i)
    (refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)})
    (ιInt/rIntSEq PB PBset PBzero PBS b)
ιOKSEq PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b =
  toPathP
    (PBset
      (depConstrInt/rIntS b)
      (depElimSetInt/rInt PB PBset PBzero PBS (depConstrInt/rIntS b))
      (PBS b (depElimSetInt/rInt PB PBset PBzero PBS b))
      (transport
        (λ i →
           elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
           PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i)
        refl)
      (ιInt/rIntSEq PB PBset PBzero PBS b))

-- rewrite version of the above
ιOKS : (PA : Nat → Type) (PB : Int / rInt → Type)
  (PA≡PB : PathP (λ i → Nat≡Int/rInt i → Type) PA PB)
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → (PA≡PB i) (depConstr0Correct i)) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB i (a≡b i)) IHa IHb) → PathP (λ i → (PA≡PB i) (depConstrSCorrect a b a≡b i)) (PAS a IHa) (PBS b IHb))
  (a : Nat) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  (QA : PA (suc a) → Type) (QB : PB (depConstrInt/rIntS b) → Type)
  (QA≡QB : PathP (λ i → (PA≡PB i) (depConstrSCorrect a b a≡b i) → Type) QA QB)
  (QAS : QA (Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a))) (QBS : QB (depElimSetInt/rInt PB PBset PBzero PBS (depConstrInt/rIntS b)))
  (QAS≡QBS :
    PathP
      (λ i → QA≡QB i
        (elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i))
      QAS
      QBS) →
  PathP
    (λ i → QA≡QB i
      (PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i))
    QAS
    (ιInt/rIntS PB PBset PBzero PBS b QB QBS)
ιOKS PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b QA QB QA≡QB QAS QBS QAS≡QBS =
  subst
    {x = subst (λ e → QA e) (refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)}) QAS}
    {y = QAS}
    (λ QAS' →
      PathP
        (λ i → QA≡QB i (PAS≡PBS a b (Cubical.Data.Nat.elim {A = PA} PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i))
        QAS'
        (ιInt/rIntS PB PBset PBzero PBS b QB QBS))
    (sym (subst-filler (λ e → QA e) refl QAS))
    (congP
      {A = λ i →
        elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
        PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i}
      {B = λ i p → QA≡QB i (PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i)}
      (λ (i : I) (p : elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
                      PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimSetInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i) →
        subst (λ e → QA≡QB i e) p (QAS≡QBS i))
      {x = refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)}}
      {y = ιInt/rIntSEq PB PBset PBzero PBS b}
      (ιOKSEq PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b))

{- From this, we can already prove add and the proofs about it correct -}

addCorrectBetter :
  ∀ (a b : ℕ) (a' b' : Int / rInt) →
  ∀ (pa : PathP (λ i → Nat≡Int/rInt i) a a') (pb : PathP (λ i → Nat≡Int/rInt i) b b') →
  PathP (λ i → Nat≡Int/rInt i) (add' a b) (addInt/rInt' a' b')
addCorrectBetter a b a' b' pa pb =
  appOK
    {T = λ i → Nat≡Int/rInt i}
    {F = λ i n → Nat≡Int/rInt i}
    (add' a)
    (addInt/rInt' a')
    (elimOK a a' pa
      (λ _ → ℕ → ℕ) -- motive of add'
      (λ _ → Int / rInt → Int / rInt) -- motive of addInt/rInt'
      (λ (_ : Int / rInt) → isSetProd (λ _ → squash/)) -- isSet proof of addInt/rInt'
      (λ i z → Nat≡Int/rInt i → Nat≡Int/rInt i) -- path between motives
      (λ (b : ℕ) → b) -- base case of add'
      (λ (b : Int / rInt) → b) -- base case off addInt/rInt'
      (lamOK (λ (b : ℕ) → b) (λ (b : Int / rInt) → b) (λ p → p)) -- path between base cases
      (λ a IH b → suc (IH b)) -- inductive case of add'
      (λ a IH b → depConstrInt/rIntS (IH b)) -- inductive case of addInt/rInt'
      (λ a a' (IHa : ℕ → ℕ) (IHa' : Int / rInt → Int / rInt) a≡a' IHa≡IHa' → -- path between inductive cases
        lamOK
          (λ b → suc (IHa b))
          (λ b → depConstrInt/rIntS (IHa' b))
          (λ b≡b' → depConstrSCorrect (IHa _) (IHa' _) (appOK IHa IHa' IHa≡IHa' _ _ b≡b'))))
      b
      b'
      pb

{- We can't prove ind, constr, and elim in general, but let's instantiate to a particular inductive type (WIP) -}

-- We can define a dependent vector type Vec:
data Vec (T : Set) : ℕ → Set where
  nil : Vec T zero
  cons : (n : ℕ) → (t : T) → Vec T n → Vec T (suc n)

-- Which repairs to a dependent vector type Vecz:
data Vecz (T : Set) : Int / rInt → Set where
  nilz : Vecz T depConstrInt/rInt0
  consz : (n : Int / rInt) → (t : T) → Vecz T n → Vecz T (depConstrInt/rIntS n)

-- We can define an eliminator for Vec:
elimVec :
  ∀ {T : Set} (P : ∀ (n : ℕ) → Vec T n → Set) →
    P zero nil →
    (∀ (n : ℕ) (t : T) (v : Vec T n) → P n v → P (suc n) (cons n t v)) →
    ∀ (n : ℕ) (v : Vec T n) → P n v
elimVec {T} P Pnil Pcons .zero nil =
  Pnil
elimVec {T} P Pnil Pcons .(suc n) (cons n t v) =
  Pcons n t v (elimVec P Pnil Pcons n v)

-- Which repairs to an eliminator for Vecz:
elimVecz :
  ∀ {T : Set} (P : ∀ (n : Int / rInt) → Vecz T n → Set) →
    P depConstrInt/rInt0 nilz →
    (∀ (n : Int / rInt) (t : T) (v : Vecz T n) → P n v → P (depConstrInt/rIntS n) (consz n t v)) →
    ∀ (n : Int / rInt) (v : Vecz T n) → P n v
elimVecz {T} P Pnil Pcons .depConstrInt/rInt0 nilz =
  Pnil
elimVecz {T} P Pnil Pcons .(depConstrInt/rIntS n) (consz n t v) =
  Pcons n t v (elimVecz P Pnil Pcons n v)

-- Vec and Vecz are (dependently) isomorphic
VecIsoVecz : ∀ {T : Set} (a : ℕ) →
  Iso (Vec T a) (Vecz T (transport (λ i → Nat≡Int/rInt i) a))
VecIsoVecz {T} a =
  iso
    VecToVecz
    VeczToVec
    VecVeczSection
    VecVeczRetraction
  where
    VecToVecz : ∀ {a : ℕ} → Vec T a → Vecz T (transport (λ i → Nat≡Int/rInt i) a)
    VecToVecz {a} v =
      elimVec
        {T = T}
        (λ (a : ℕ) (v : Vec T a) → Vecz T (transport (λ i → Nat≡Int/rInt i) a))
        nilz
        (λ (a : ℕ) (t : T) (v : Vec T a) IH →
          consz (transport (λ i → Nat≡Int/rInt i) a) t IH)
        a
        v
    ---
    VeczToVec : ∀ {a : ℕ} → Vecz T (transport (λ i → Nat≡Int/rInt i) a) → Vec T a
    VeczToVec {a} v =
      elimVecz
        (λ (b : Int / rInt) (v : Vecz T b) → Vec T (transport (λ i → Nat≡Int/rInt (~ i)) b))
        nil
        (λ (b : Int / rInt) (t : T) (v : Vecz T b) IH →
          subst
            (λ a → Vec T a)
            (fromPathP⁻ (depConstrSCorrect (transport (λ i → Nat≡Int/rInt (~ i)) b) b (toPathP⁻ refl)))
            (cons (transport (λ i → Nat≡Int/rInt (~ i)) b) t IH))
        (transport (λ i → Nat≡Int/rInt i) a)
        v
    ---
    VecVeczSection : ∀ (v : Vecz T (transport (λ i → Nat≡Int/rInt i) a)) → VecToVecz (VeczToVec v) ≡ v
    VecVeczSection v = {!!} -- ahhhh hard
    ---
    VecVeczRetraction : ∀ (v : Vec T a) → VeczToVec (VecToVecz v) ≡ v
    VecVeczRetraction v =
      elimVec
        (λ (a : ℕ) (v : Vec T a) → VeczToVec (VecToVecz v) ≡ v)
        refl
        (λ (a : ℕ) (t : T) (v : Vec T a) (IH : VeczToVec (VecToVecz v) ≡ v) →
          subst
            (λ (v' : Vec T a) → subst (λ a → Vec T a) (fromPathP⁻ (depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP⁻ refl))) (cons a t (VeczToVec (VecToVecz v))) ≡ cons a t v')
            IH
            (subst
              {x = refl}
              {y = fromPathP⁻ (depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP⁻ refl))}
              (λ p → subst (λ a → Vec T a) p (cons a t (VeczToVec (VecToVecz v))) ≡ cons a t (VeczToVec (VecToVecz v)))
              (isSetℕ (suc a) _ refl (fromPathP⁻ (depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP⁻ refl))))
              (substRefl {B = λ a → Vec T a} (cons a t (VeczToVec (VecToVecz v))))))
        a
        v

-- Ind is OK by isomorphism
IndOK :
  PathP (λ i → Set → Nat≡Int/rInt i → Set) Vec Vecz
IndOK =
  funExtDep
    (λ {T} {T'} T≡T' →
      subst
        (λ T' → PathP (λ i → Nat≡Int/rInt i → Set) (Vec T) (Vecz T'))
        (fromPathP T≡T')
        (funExtDep (λ {a} {b} a≡b →
          subst
            (λ b' → PathP (λ i → Set) (Vec T a) (Vecz T b'))
            (fromPathP a≡b)
            (isoToPath (VecIsoVecz a)))))
        

-- TODO prove the other three rules for vectors specifically (WIP)
-- TODO prove some functions and proofs are repaired correctly using only these pieces
-- TODO change Set to Type elsewhere too?

{- Porting proofs to nat-like eliminators -}

sucLemNat'' : (a : ℕ) → (b : ℕ) → suc (add' a b) ≡ add' a (suc b)
sucLemNat'' a b =
  Cubical.Data.Nat.elim
    {A = λ a → ∀ b → suc (add' a b) ≡ add' a (suc b)} -- motive P
    (λ b → refl) -- base case
    (λ a (IH : ∀ b → suc (add' a b) ≡ add' a (suc b)) b →
      -- want to show P (suc a) b, which is suc (add' (suc a) b) ≡ add' (suc a) (suc b)
      -- we have cong suc (IH b), where (IH b) : suc (add' a b) ≡ add' a (suc b)
      -- thus, cong suc (IH b) : suc (suc (add' a b)) ≡ suc (add' a (suc b))
      -- so our definitional equality is:
      --  (suc (add' (suc a) b) ≡ add' (suc a) (suc b)) ≝ (suc (suc (add' a b)) ≡ suc (add' a (suc b)))
      --    by δ, unfold add' everywhere
      --    this will give us an application of Cubical.Data.Nat.elim (the add' defined above)
      --    by Β, take the (λ a b → ...) that add' unfolded to, and specialize to each a, b (e.g., (suc a) b)
      --    Now we have (Cubical.Data.Nat.elim ... (suc a)) b
      --    Now by ι, we have suc ((Cubical.Data.Nat.elim ... a) b)
      --    etc.
      cong suc (IH b)) -- inductive case
    a
    b

sucLemInt/rInt'' : (a : Int / rInt) -> (b : Int / rInt) -> depConstrInt/rIntS (addInt/rInt' a b) ≡ (addInt/rInt' a (depConstrInt/rIntS b)) -- S (a + b) = a + S b
sucLemInt/rInt'' a b =
  depElimInt/rInt
    (λ (a : Int / rInt) → ∀ (b : Int / rInt) → depConstrInt/rIntS (addInt/rInt' a b) ≡ addInt/rInt' a (depConstrInt/rIntS b))
    (λ (a : Int / rInt) (p q : ∀ b → depConstrInt/rIntS (addInt/rInt' a b) ≡ addInt/rInt' a (depConstrInt/rIntS b)) i →
      isSetProd
        {B = λ b → depConstrInt/rIntS (addInt/rInt' a b) ≡ addInt/rInt' a (depConstrInt/rIntS b)}
        (λ b → isProp→isSet (squash/ _ _))
        (λ b → p b)
        (λ b → q b)
        (funExt (λ x → squash/ _ _ (p x) (q x)))
        (funExt (λ x → squash/ _ _ (p x) (q x)))
        i
        i) -- p ≡ q
    (λ b → refl) -- base case
    (λ a (IH : ∀ b → depConstrInt/rIntS (addInt/rInt' a b) ≡ addInt/rInt' a (depConstrInt/rIntS b)) b → -- inductive case
      ιInt/rIntS⁻ -- w.t.s that S (S a + b) ≡ S a + S b
        (λ _ → Int / rInt → Int / rInt)
        (λ _ → isSetProd (λ _ → squash/))
        (λ b → b)
        (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
        a
        (λ (add-Sa : Int / rInt → Int / rInt) → -- e.t.s. that S (S (a + b)) ≡ S (a + S b)
          depConstrInt/rIntS (add-Sa b) ≡ add-Sa (depConstrInt/rIntS b))
        (cong depConstrInt/rIntS (IH b))) -- which holds by cong and the IH
      a
      b

-- Some thoughts on automating the above, from Talia:
--
-- We would eventually like to be able to infer the iota applications automatically.
-- We have the corresponding proofs over nat, for which the iota reductions hold
-- definitionally. What does this mean?
--
-- It means that we know that over nat, we have:
--   Γ, IH : ∀ b → S (a + b) ≡ a + S b, b : Nat ⊢ cong S (IH b) : S (S a + b) ≡ S a + S b
-- since that is our goal shown by cong S (IH b) in the proof over Nat. But also:
--   Γ, IH : ∀ b → S (a + b) ≡ a + S b, b : Nat ⊢ cong S (IH b) : S (S (a + b)) ≡ S (a + S b)
-- before reduction of the type, just by the type signature of cong and of IH.
-- 
-- This means that we have:
--   (S (S a + b) ≡ S a + S b) ≝ (S (S (a + b)) ≡ S (a + S b))
-- So when we normalize both sides, over nat, we get the same normal form.
--
-- How do we actually get the particular normalization steps that happen, here?
-- Because we need to reify them when we move out of the original type, since
-- now these iota reductions do not hold definitionally. It would be nice to do this
-- fully automatically, rather than by hand. I see two potential paths forward:
--
-- 1. We could instrument Cubical Agda's definitional equality to track each reduction step.
-- This is probably overkill, but it doesn't require much knowledge of anything.
--
-- 2. We could figure out the normalization steps ourselves, after the fact. I think
-- we could potentially skip over knowing the entire normalization algorithm, since the
-- only thing that should change in significant ways will be the iota steps, so if it's
-- blocked it must be blocked on iota (or eta if we are yet to find that). But those iota
-- steps could be nested inside of other reductions, potentially, which might make it hard
-- to do anything unless we know everything about normalization. Maybe we can make some
-- simplifying assumptions, though.
--
-- Let us look at the example above in a bit more detail. What are the relevant ι-reduction
-- steps that happen to show:
--   (S (S a + b) ≡ S a + S b) ≝ (S (S (a + b)) ≡ S (a + S b))
-- over natural numbers? The RHS is fully normalized already, but the LHS is not.
-- δ unfolds + to an application of the Nat eliminator (we are again pretending general
-- pattern matching isn't a thing). Β-reduction a few times simplifies this to applying
-- the nat eliminator to (S a), which is when ι applies. This happens to both instances of
-- + on the LHS.
--
-- Thus, when we want to do this propositionally, what we must do is abstract every (S a) in
-- our call to ι specialized to + (over Int/rInt). Furthermore, we apply ι in the backwards
-- direction because our LHS (goal) is normalized already, but the RHS (the term we claim has the
-- type of our goal, and that indeed does when we are working over nat with definitional ι)
-- is not yet normalized, and needs those (S a) abstracted away.
--
-- OK, let's generalize. Let's say that over nat we have:
--   Γ ⊢ t : T
-- by definition, where t is the term that proves our goal T.
-- By raw syntactic type checking without normalizing, let us also say we have:
--   Γ ⊢ t : T'
-- Then over nat we can infer that:
--   Γ ⊢ T ≝ T'
-- Say we move to Int/rInt, now, and we no longer have that (lifted) T ≝ T'.
-- We want to show that (lifted) T ≡ T'. All significant changes in the equality between T and T'
-- must come from applications of of ι (unless eta is a thing; I guess we don't know yet). Thus:
--
-- 1. We should first fully normalize (lifted) T and T'. In the case of our example above,
-- this would δ-expand lifted + and Β-reduce its application.
--
-- 2. We should arrive at forms of T and T' that explicitly apply the lifted eliminator over
-- Int/rInt. Since ι is the only significant change, they should furthermore apply the lifted
-- eliminator to (S x) for some x (where S is shorthand for depConstrInt/rIntS; it is lifted S)
--
-- 3. Abstract everything definitionally equal to (S x) for some x, where that (S x) is eliminated
-- over in normalized T. This is the argument Q to ι in the backwards direction, while that x
-- is the argument n to ι in the backwards direction. Apply the ι rewrites propositionally
-- to get updated T, t.
--
-- 4. If T ≝ T', stop and return. Otherwise, abstract everything definitionally equal to (S x)
-- for some x, where that (S x) is eliminated over in normalized T'. This is the argument Q to
-- ι in the forwards direction, while that x is the argument n to ι in the forwards direction.
-- Apply the ι rewrites propositionally to get updated T', t.
--
-- 5. If T ≝ T', stop and return. Otherwise, repeat steps 1-5.
--
-- I think this is reasonable but it also means knowing how to fully normalize things in
-- between. I think we should write a constrained normalization algorithm over a restricted
-- fragment of the type theory that we define ourselves? Or something.
--
-- Maybe we can use Cubical Agda's normalization as an oracle. It remains to be seen
-- whether the information we get back from Cubical Agda is actually useful enough
-- to help us with that?

-- In any case, let us try this algorithm over the other proof
sucLemInt/rInt''' : (a : Int / rInt) → (b : Int / rInt) → (addInt/rInt' (depConstrInt/rIntS a) b) ≡ depConstrInt/rIntS (addInt/rInt' a b)
sucLemInt/rInt''' a b =
  depElimInt/rInt
    (λ a → ∀ (b : Int / rInt) → -- P
      addInt/rInt' (depConstrInt/rIntS a) b ≡ depConstrInt/rIntS (addInt/rInt' a b))
    (λ (a : Int / rInt) p q i →
      isSetProd
        (λ b → isProp→isSet (squash/ _ _))
        (λ b → p b)
        (λ b → q b)
        (funExt (λ x → squash/ _ _ (p x) (q x)))
        (funExt (λ x → squash/ _ _ (p x) (q x)))
        i
        i)
    (λ b → refl)
    (λ a (IH : ∀ b → addInt/rInt' (depConstrInt/rIntS a) b ≡ depConstrInt/rIntS (addInt/rInt' a b)) b →
      -- P (S a) b is T so
      -- T is (S S a) + b ≡ S (S a + b)
      -- cong depConstrInt/rIntS (IH b) : T', so
      -- T' is S (S a + b) ≡ S (S (a + b))
      -- Normalizing T blocks on ι in the RHS; let us abstract (S a):
      ιInt/rIntS⁻
        (λ _ → Int / rInt → Int / rInt)
        (λ _ → isSetProd (λ _ → squash/))
        (λ b → b)
        (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
        a
        (λ (add-Sa : Int / rInt → Int / rInt) →
          addInt/rInt' (depConstrInt/rIntS (depConstrInt/rIntS a)) b ≡ depConstrInt/rIntS (add-Sa b))
        ( -- We have simplified T to (S S a) + b ≡ S (S (a + b))
          -- Normalizing T further blocks on ι on the LHS; let us abstract (S (S a)):
          ιInt/rIntS⁻
            (λ _ → Int / rInt → Int / rInt)
            (λ _ → isSetProd (λ _ → squash/))
            (λ b → b)
            (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
            (depConstrInt/rIntS a) -- note that we must also instantiate argument to Q
            (λ (add-SSa : Int / rInt → Int / rInt) →
              add-SSa b ≡ depConstrInt/rIntS (depConstrInt/rIntS (addInt/rInt' a b)))
            ( -- We have simplified T to S (S a + b) ≡ S (S (a + b))
              -- I guess this points out one missed piece in our algorithm, which is
              -- we can stop preemptively if T and T' are identical
              cong depConstrInt/rIntS (IH b))))
    a
    b

-- Now let's try for commutativity
addCommNat' : (a : ℕ) → (b : ℕ) → add' a b ≡ add' b a
addCommNat' a b =
  Cubical.Data.Nat.elim
    {A = λ a → ∀ b → add' a b ≡ add' b a}
    (λ b →
      Cubical.Data.Nat.elim
        {A = λ b → add' 0 b ≡ add' b 0}
        refl
        (λ b (IHb : add' 0 b ≡ add' b 0) →
          cong suc IHb)
        b)
    (λ a (IHa : ∀ b → add' a b ≡ add' b a) b →
      cong suc (IHa b) ∙ sucLemNat'' b a) 
    a
    b

addCommInt/rInt' : (a : Int / rInt) → (b : Int / rInt) → addInt/rInt' a b ≡ addInt/rInt' b a
addCommInt/rInt' a b =
  depElimInt/rInt
    (λ a → ∀ b → addInt/rInt' a b ≡ addInt/rInt' b a)
    (λ (a : Int / rInt) p q i →
      isSetProd
        (λ b → isProp→isSet (squash/ _ _))
        (λ b → p b)
        (λ b → q b)
        (funExt (λ x → squash/ _ _ (p x) (q x)))
        (funExt (λ x → squash/ _ _ (p x) (q x)))
        i
        i)
    (λ b →
      depElimInt/rInt
        (λ b → addInt/rInt' [ pos zero ] b ≡ addInt/rInt' b [ pos zero ])
        (λ b → squash/ _ _)
        refl
        (λ b (IHb : addInt/rInt' [ pos zero ] b ≡ addInt/rInt' b [ pos zero ]) →
          -- T := P (S b) := [ pos zero ] + (S b) ≡ (S b) + [ pos zero ]
          -- cong S IHb : T', so
          -- T' := S ([ pos zero ] + b) = S (b + [ pos zero ])
          -- One backwards ι abstracting over S b
          ιInt/rIntS⁻
            (λ _ → Int / rInt → Int / rInt)
            (λ _ → isSetProd (λ _ → squash/))
            (λ b → b)
            (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
            b
            (λ add-Sb →
              addInt/rInt' [ pos zero ] (depConstrInt/rIntS b) ≡ add-Sb [ pos zero ])
            (cong depConstrInt/rIntS IHb))
        b)
    (λ a (IHa : ∀ b → addInt/rInt' a b ≡ addInt/rInt' b a) b →
      -- T := P (S a) b := S a + b ≡ b + S a
      ιInt/rIntS⁻
        (λ _ → Int / rInt → Int / rInt)
        (λ _ → isSetProd (λ _ → squash/))
        (λ b → b)
        (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
        a
        (λ add-Sa →
          add-Sa b ≡ addInt/rInt' b (depConstrInt/rIntS a))
        (cong depConstrInt/rIntS (IHa b) ∙ sucLemInt/rInt'' b a)) 
    a
    b

-- Proof of correctness of repaired proof
-- addCommCorrect : ∀ (a : ℕ) (a' : Int / rInt) (p : PathP {!!} a a') → {!!}
-- addCommCorrect = {!!}

-- addCommNat' : (a : ℕ) → (b : ℕ) → add' a b ≡ add' b a
-- addCommInt/rInt' : (a : Int / rInt) → (b : Int / rInt) → addInt/rInt' a b ≡ addInt/rInt' b a

-- TODO, show that this is correct in comparison to a nat version!
-- think about how to algorithmically generate those proofs
