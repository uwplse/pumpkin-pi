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
open import Cubical.HITs.Nullification.Properties

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
addInt/rInt' : (Int / rInt) -> (Int / rInt) -> (Int / rInt)
addInt/rInt' a b =
  depElimSetInt/rInt
    (λ _ → Int / rInt → Int / rInt) -- motive P
    (λ (_ : Int / rInt) → isSetProd (λ _ → squash/)) -- ∀ n, isSet (P n)
    (λ _ → b) -- P depConstrInt/rInt0 
    (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m)) -- ∀ n, P n → P (depConstrInt/rIntS n)
    a
    b

-- A couple simple tests
addOKPos : addInt/rInt' [ pos 5 ] [ pos 6 ] ≡ [ pos 11 ]
addOKPos = refl

addOKNeg : addInt/rInt' [ neg 2 ] [ neg 7 ] ≡ [ neg 9 ]
addOKNeg = refl

-- Porting proofs to nat-like eliminators

help1 : ∀ a b →
  depConstrInt/rIntS (addInt/rInt' a b) ≡ addInt/rInt' a (depConstrInt/rIntS b) →
  depConstrInt/rIntS (depConstrInt/rIntS (addInt/rInt' a b)) ≡ depConstrInt/rIntS (addInt/rInt' a (depConstrInt/rIntS b))
help1 a b IH = cong depConstrInt/rIntS IH

help : ∀ a b →
  depConstrInt/rIntS (addInt/rInt' a b) ≡ addInt/rInt' a (depConstrInt/rIntS b) →
  depConstrInt/rIntS (depConstrInt/rIntS (addInt/rInt' a b)) ≡ addInt/rInt' (depConstrInt/rIntS a) (depConstrInt/rIntS b)
help a b IH =
  ιInt/rIntS⁻
    (λ _ → Int / rInt → Int / rInt)
    (λ (_ : Int / rInt) → isSetProd (λ _ → squash/)) -- ∀ n, isSet (P n)
    (λ _ → b) -- P depConstrInt/rInt0 
    (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m)) -- ∀ n, P n → P (depConstrInt/rIntS n)
    a
    (λ PS → depConstrInt/rIntS (depConstrInt/rIntS (addInt/rInt' a b)) ≡ PS (depConstrInt/rIntS b))
    (help1 a b IH) -- magically fails to type check whyyyyyyy
    
sucLemInt/rInt'' : (a : Int / rInt) -> (b : Int / rInt) -> depConstrInt/rIntS (addInt/rInt' a b) ≡ (addInt/rInt' a (depConstrInt/rIntS b))
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
        (λ _ → b)
        (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
        a
        (λ (PS : Int / rInt → Int / rInt) → depConstrInt/rIntS (PS b) ≡ addInt/rInt' (depConstrInt/rIntS a) (depConstrInt/rIntS b))
        (help a b (IH b))) -- e.t.s. that S (S (a + b)) ≡ S a + S b. Probably needs one more iota, but I failed trying to find it ...
    a
    b
