{-# OPTIONS --safe --cubical #-}
module equivalence_int_abs where

open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import alternateFunExtDep

-- In this file, we do repair between two simple implementations of the natural numbers.
-- We then show that the functions and theorems we wrote were repaired correctly.

-- Our first implementation of the natural numbers is just the standard library implementation.
-- Our second implementation is the disjoint union of two copies of the natural numbers, quotiented by
-- the equivalence relation erasing the distinction between the left and right members of the disjoint union.

data Int : Set where
  pos : (n : ℕ) → Int
  neg : (n : ℕ) → Int

abs : Int -> ℕ
abs (pos x) = x
abs (neg x) = x

rInt : Int → Int → Type
rInt a b = abs a ≡ abs b

isSetInt/rInt : isSet (Int / rInt)
isSetInt/rInt x y p q = squash/ x y p q

f : ℕ → Int / rInt
f n = [ pos n ]

g : Int / rInt → ℕ
g [ n ] = abs n
g (eq/ a b r i) = r i
g (squash/ a b p q i j) = isSetℕ (g a) (g b) (cong g p) (cong g q) i j

sec : section f g
sec = elimProp (λ x → isSetInt/rInt (f (g x)) x) lem where
  lem : (a : Int) → f (abs a) ≡ [ a ]
  lem (pos n) = refl
  lem (neg n) = eq/ (pos n) (neg n) refl

ret : retract f g
ret n = refl

NatIsoInt/rInt : Iso ℕ (Int / rInt)
NatIsoInt/rInt = iso f g sec ret

-- Path equality corresponding to this isomorphism
Nat≡Int/rInt : ℕ ≡ Int / rInt
Nat≡Int/rInt = isoToPath NatIsoInt/rInt

sucLemNat : (a : ℕ) -> (b : ℕ) -> suc (a + b) ≡ a + suc b
sucLemNat zero b = refl
sucLemNat (suc a) b = cong suc (sucLemNat a b)

sucInt : Int -> Int
sucInt (pos n) = pos (suc n)
sucInt (neg n) = neg (suc n)

sucInt/rInt : (Int / rInt) -> (Int / rInt)
sucInt/rInt [ a ] = [ sucInt a ]
sucInt/rInt (eq/ (pos a) (pos b) r i) = eq/ (sucInt (pos a)) (sucInt (pos b)) (cong suc r) i
sucInt/rInt (eq/ (pos a) (neg b) r i) = eq/ (sucInt (pos a)) (sucInt (neg b)) (cong suc r) i
sucInt/rInt (eq/ (neg a) (pos b) r i) = eq/ (sucInt (neg a)) (sucInt (pos b)) (cong suc r) i
sucInt/rInt (eq/ (neg a) (neg b) r i) = eq/ (sucInt (neg a)) (sucInt (neg b)) (cong suc r) i
sucInt/rInt (squash/ a b p q i j) = squash/ (sucInt/rInt a) (sucInt/rInt b) (cong sucInt/rInt p) (cong sucInt/rInt q) i j

constantEq/Refl : {A : Type} -> {R : A -> A -> Type} -> (a : A) →  (r : R a a) → eq/ {R = R} a a r ≡ refl
constantEq/Refl a r = squash/ ([_] a) ([_] a) (eq/ a a r) refl

-- Dependent constructors for Int/rInt
depConstrInt/rInt0 : Int / rInt
depConstrInt/rInt0 = [ pos 0 ]

depConstrInt/rIntS : Int / rInt -> Int / rInt
depConstrInt/rIntS = sucInt/rInt

-- There is a path between any eq/ and its reversal
eq≡eqRev/ : ∀ (x y : Int) (r1 : rInt x y) (r2 : rInt y x) →
  (λ i → eq/ {R = rInt} x y r1 i) ≡ (λ i → eq/ {R = rInt} y x r2 (~ i))
eq≡eqRev/ x y r1 r2 =
  squash/ {R = rInt} [ x ] [ y ] (λ i → eq/ x y r1 i) (λ i → eq/ y x r2 (~ i))

-- Thus, we can get between transporting in either direction
transportEq≡transportEqRev/ : ∀ n (r1 : rInt (pos n) (neg n)) (r2 : rInt (neg n) (pos n)) (req : r1 ≡ r2) (P : Int / rInt → Type) (px : P [ pos n ]) →
  transport (λ i → P (eq/ {R = rInt} (pos n) (neg n) r1 i)) px ≡ transport (λ i → P (eq/ {R = rInt} (neg n) (pos n) r2 (~ i))) px
transportEq≡transportEqRev/ n r1 r2 req P px =
  subst
    (λ (H : [ neg n ] ≡ [ pos n ]) → transport ( λ i → P (H (~ i))) px ≡ transport (λ i → P (eq/ (neg n) (pos n) r2 (~ i))) px)
    (eq≡eqRev/ (neg n) (pos n) r1 r1)
    (subst
      (λ (r : rInt (pos n) (neg n)) → transport (λ i → P (eq/ (neg n) (pos n) r1 (~ i))) px ≡ transport (λ i → P (eq/ (neg n) (pos n) r (~ i))) px)
      req
      refl)

-- Dependent eliminator for Int / rInt over Set (thanks to Amelia Liao for helping us figure this out)
depElimInt/rInt : (P : Int / rInt -> Type) -> (∀ x -> isSet (P x)) -> (P depConstrInt/rInt0) -> (∀ n -> (P n) -> P (depConstrInt/rIntS n)) -> ((x : Int / rInt) -> P x)
depElimInt/rInt P set baseCase sucCase = SetQuotients.elim set lem wellDefined where
  -- points
  lem : (a : Int) → P [ a ]
  lem (pos zero) = baseCase
  lem (pos (suc n)) =  sucCase [ pos n ] (lem (pos n))
  lem (neg zero) =
    transport
      (cong P (eq/ (pos zero) (neg zero) (refl)))
      (lem (pos zero))
  lem (neg (suc n)) =
    transport
      (cong P (eq/ (pos (suc n)) (neg (suc n)) (refl)))
      (sucCase [ pos n ] (lem (pos n)))
  -- paths
  wellDefined : (a b : Int) (r :  rInt a b) → PathP (λ i → P (eq/ a b r i)) (lem a) (lem b)
  wellDefined (pos x) (pos y) r = J
    (λ y e → PathP (λ i → P (eq/ (pos x) (pos y) e i)) (lem (pos x)) (lem (pos y)))
    (subst
      (λ e → PathP (λ i → P (e i)) (lem (pos x)) (lem (pos x)))
      (squash/ [ pos x ] [ pos x ] refl (eq/ (pos x) (pos x) refl))
      (λ i → lem (pos x)))
    r
  wellDefined (neg x) (neg y) r = J
    (λ y e → PathP (λ i → P (eq/ (neg x) (neg y) e i)) (lem (neg x)) (lem (neg y)))
    (subst
      (λ e → PathP (λ i → P (e i)) (lem (neg x)) (lem (neg x)))
      (squash/ [ neg x ] [ neg x ] refl (eq/ (neg x) (neg x) refl))
      (λ i → lem (neg x)))
    r
  wellDefined (pos x) (neg y) r = J 
    (λ y e → PathP (λ i → P (eq/ (pos x) (neg y) e i)) (lem (pos x)) (lem (neg y)))
    (toPathP -- transport (λ i → A i) x ≡ y → PathP A x y
      (Cubical.Data.Nat.elim
        {A = λ n → transport (λ i → P (eq/ (pos n) (neg n) refl i)) (lem (pos n)) ≡ (lem (neg n))}
        refl
        (λ _ _ → refl)
        x))
    r
  wellDefined (neg x) (pos y) r = J
    (λ y e → PathP (λ i → P (eq/ (neg x) (pos y) e i)) (lem (neg x)) (lem (pos y)))
    (toPathP⁻ -- x ≡ transport (λ i → A i) y → PathP A x y
      (Cubical.Data.Nat.elim
        {A = λ n → lem (neg n) ≡ transport {A = P [ pos n ]} {B = P [ neg n ]} (λ i → P (eq/ (neg n) (pos n) refl (~ i))) (lem (pos n)) }
        (transportEq≡transportEqRev/ zero refl refl refl P baseCase)
        (λ n _ → transportEq≡transportEqRev/ (suc n) refl refl refl P (sucCase [ pos n ] (lem (pos n))))
        x))
    r

ιInt/rInt0 : (P : Int / rInt → Type) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) →
    (Q : P depConstrInt/rInt0 → Set) → Q (depElimInt/rInt P pset pz ps depConstrInt/rInt0) → Q pz
ιInt/rInt0 P pset pz ps Q qz = qz

rIntPosNegQ : (n : ℕ) -> ([_] {A = Int} {R = rInt} (pos n)  ≡ [_] {A = Int} {R = rInt} (neg n))
rIntPosNegQ n = eq/ _ _ refl

ιInt/rIntSEq : (P : Int / rInt → Type) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    depElimInt/rInt P pset pz ps (depConstrInt/rIntS n) ≡ ps n (depElimInt/rInt P pset pz ps n)
ιInt/rIntSEq P pset pz ps = elimProp prop fpoint where
  fpoint : (x : Int) → depElimInt/rInt P pset pz ps (depConstrInt/rIntS [ x ]) ≡ ps [ x ] (depElimInt/rInt P pset pz ps [ x ])
  fpoint (pos n) = refl
  fpoint (neg n) = subst (λ e → depElimInt/rInt P pset pz ps (depConstrInt/rIntS e) ≡ ps e (depElimInt/rInt P pset pz ps e)) (rIntPosNegQ n) refl
  -- it's OK to use elimProp:
  prop : (n : Int / rInt) → isProp (depElimInt/rInt P pset pz ps (depConstrInt/rIntS n) ≡ ps n (depElimInt/rInt P pset pz ps n))
  prop n p q = pset (depConstrInt/rIntS n) (depElimInt/rInt P pset pz ps (depConstrInt/rIntS n)) (ps n (depElimInt/rInt P pset pz ps n)) p q

ιInt/rIntS : (P : Int / rInt → Type) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    (Q : P (depConstrInt/rIntS n) → Set) → 
    Q (depElimInt/rInt P pset pz ps (depConstrInt/rIntS n)) →
    Q (ps n (depElimInt/rInt P pset pz ps n))
ιInt/rIntS P pset pz ps n Q Qb = subst (λ e → Q e) (ιInt/rIntSEq P pset pz ps n) Qb

ιInt/rIntS⁻ : (P : Int / rInt → Type) → (pset : ∀ x → isSet (P x)) → (pz : P depConstrInt/rInt0) → (ps : ∀ (n : Int / rInt) → (P n) → P (depConstrInt/rIntS n)) → (n : Int / rInt) →
    (Q : P (depConstrInt/rIntS n) → Set) → 
    Q (ps n (depElimInt/rInt P pset pz ps n)) →
    Q (depElimInt/rInt P pset pz ps (depConstrInt/rIntS n))
ιInt/rIntS⁻ P pset pz ps n Q Qb = subst (λ e → Q e) (sym (ιInt/rIntSEq P pset pz ps n)) Qb

-- 3.1.6 in the HoTT book
isSetProd : ∀ {A : Type} {B : A → Type} → (∀ (a : A) → isSet (B a)) → isSet (∀ (a : A) → B a)
isSetProd {A} {B} setB =
   λ (f g : ∀ (a : A) → B a) (p q : f ≡ g) →
     cong funExt (funExt (λ (a : A) → setB a (f a) (g a) (funExt⁻ p a) (funExt⁻ q a)))

isSetFunc : {A B : Set} → isSet A → isSet B → isSet (A → B)
isSetFunc {A} {B} setA setB = isSetProd {B = λ _ → B} (λ _ → setB)

-- Porting functions to nat-like eliminators
add : (a : ℕ) → (b : ℕ) → ℕ
add a b =
  Cubical.Data.Nat.elim
    {A = λ _ → ℕ → ℕ} -- motive P
    (λ b → b) -- P 0
    (λ a IH b → suc (IH b)) -- ∀ n, P n → P (S n)
    a
    b

addInt/rInt : (Int / rInt) -> (Int / rInt) -> (Int / rInt)
addInt/rInt a b =
  depElimInt/rInt
    (λ _ → Int / rInt → Int / rInt) -- motive P
    (λ (_ : Int / rInt) → isSetProd (λ _ → squash/)) -- ∀ n, isSet (P n)
    (λ b → b) -- P depConstrInt/rInt0
    (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m)) -- ∀ n, P n → P (depConstrInt/rIntS n)
    a
    b

-- A couple simple tests
addOKPos : addInt/rInt [ pos 5 ] [ pos 6 ] ≡ [ pos 11 ]
addOKPos = refl

addOKNeg : addInt/rInt [ neg 2 ] [ neg 7 ] ≡ [ neg 9 ]
addOKNeg = refl

{- Correctness for dependent constructors and eliminators -}

Nat≡Int/rIntIrrel : ∀ (a : ℕ) (b : Int / rInt) (p1 p2 : PathP (λ i → Nat≡Int/rInt i) a b) →
  p1 ≡ p2
Nat≡Int/rIntIrrel a b p1 p2 =
  subst2
    (λ p1 p2 → p1 ≡ p2)
    (Iso.leftInv (PathPIsoPath (λ i → Nat≡Int/rInt i) a b) p1)
    (Iso.leftInv (PathPIsoPath (λ i → Nat≡Int/rInt i) a b) p2)
    (cong
      (toPathP {A = λ i → Nat≡Int/rInt i})
      (squash/ _ _ (fromPathP p1) (fromPathP p2)))

depConstr0Correct : PathP (λ i → Nat≡Int/rInt i) zero depConstrInt/rInt0
depConstr0Correct = toPathP refl

depConstrSCorrect :
  ∀ a b → PathP (λ i → Nat≡Int/rInt i) a b → PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)
depConstrSCorrect a b a≡b =
  toPathP (cong depConstrInt/rIntS (fromPathP a≡b))

depConstrSCorrectIrrel : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) (Sa≡Sb : PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS b)) →
  depConstrSCorrect a b a≡b ≡ Sa≡Sb
depConstrSCorrectIrrel a b a≡b Sa≡Sb = Nat≡Int/rIntIrrel (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) Sa≡Sb

private
  variable
    ℓ ℓ' : Level

-- Proving that applications of the eliminators for Nat and Int / rInt have a path between them given that the inputs to the eliminators have paths between them.

elimOK : -- based on elim_OK from Talia Ringer's PLDI 2021 paper
  ∀ (a : ℕ) (b : Int / rInt) →
  ∀ (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  ∀ (PA : ℕ → Type) (PB : Int / rInt → Type) (PBSet : ∀ b → isSet (PB b)) →
  ∀ (PA≡PB : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) → PathP (λ i → Type) (PA a) (PB b)) →
  ∀ (PAO : PA zero) (PBO : PB depConstrInt/rInt0) →
  ∀ (PAO≡PBO : PathP (λ i → PA≡PB zero depConstrInt/rInt0 depConstr0Correct i) PAO PBO) →
  ∀ (PAS : ∀ a → PA a → PA (suc a)) (PBS : ∀ b → PB b → PB (depConstrInt/rIntS b)) →
  ∀ (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB a b a≡b i) IHa IHb) → PathP (λ i → PA≡PB (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) i) (PAS a IHa) (PBS b IHb)) →
  PathP (λ i → PA≡PB a b a≡b i) (Cubical.Data.Nat.elim {A = PA} PAO PAS a) (depElimInt/rInt PB PBSet PBO PBS b)
elimOK a b a≡b PA PB PBSet PA≡PB PAO PBO PAO≡PBO PAS PBS PAS≡PBS =
  J -- adjust a≡b from pathP to path to make it easy to use JDep
    (λ a≡b' (H : toPathP (fromPathP a≡b) ≡ a≡b') →
      PathP (λ i → PA≡PB a b a≡b' i) (Cubical.Data.Nat.elim {A = PA} PAO PAS a) (depElimInt/rInt PB PBSet PBO PBS b))
    (JDep -- adjust to a homogeneous PathP about proofs about a
       {A = Int / rInt}
       {B = λ (b : Int / rInt) → PB b}
       {b =  depElimInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)}
       (λ (b : Int / rInt) (a≡b : transport (λ i → Nat≡Int/rInt i) a ≡ b) (PBb : PB b)
          (p : PathP (λ i → PB (a≡b i)) (depElimInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)) PBb) →
         PathP (λ i → PA≡PB a b (toPathP {A = λ i → Nat≡Int/rInt i} a≡b) i) (Cubical.Data.Nat.elim {A = PA} PAO PAS a) (depElimInt/rInt PB PBSet PBO PBS b))
       (Cubical.Data.Nat.elim
         {A = λ (a : ℕ) →
           PathP
             (λ i → PA≡PB _ _ (toPathP {A = λ i → Nat≡Int/rInt i} (refl {x = transport (λ i → Nat≡Int/rInt i) a})) i)
             (Cubical.Data.Nat.elim PAO PAS a)
             (depElimInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a))}
         PAO≡PBO -- base case holds by PAO≡PBO
         (λ (a : ℕ) IHa → -- inductive case holds by ι of PAS≡PBS
           (subst -- adjust to refl
            {A = PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a))}
            {x = depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl)}
            {y = toPathP {A = λ i → Nat≡Int/rInt i} refl}
            (λ (Sa≡Sa : PathP (λ i → Nat≡Int/rInt i) (suc a) (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a))) →
              PathP (λ i → PA≡PB _ _ Sa≡Sa i) (PAS a (Cubical.Data.Nat.elim PAO PAS a)) (depElimInt/rInt PB PBSet PBO PBS (depConstrInt/rIntS (transport (λ i → Nat≡Int/rInt i) a))))
            (depConstrSCorrectIrrel a (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl) (toPathP refl))
            (ιInt/rIntS⁻ -- ι reduce the successor case for proofs about Int/rInt
              PB
              PBSet
              PBO
              PBS
              (transport (λ i → Nat≡Int/rInt i) a)
              (λ PBSa →
                PathP (λ i → PA≡PB _ _ (depConstrSCorrect a (transport (λ i → Nat≡Int/rInt i) a) (toPathP refl)) i) (PAS a (Cubical.Data.Nat.elim PAO PAS a)) PBSa)
              (PAS≡PBS a (transport (λ i → Nat≡Int/rInt i) a) (Cubical.Data.Nat.elim PAO PAS a) (depElimInt/rInt PB PBSet PBO PBS (transport (λ i → Nat≡Int/rInt i) a)) (toPathP refl) IHa))))
           a)
       {y = b}
       (fromPathP a≡b)
       {z = depElimInt/rInt PB PBSet PBO PBS b}
       (cong (depElimInt/rInt PB PBSet PBO PBS) (fromPathP a≡b)))
    (Iso.leftInv (PathPIsoPath (λ i → Nat≡Int/rInt i) a b) a≡b)

-- Next, we prove that applications of the iota rules have paths between them given that the inputs have paths between them.

-- iota: iota is OK at 0 by QAzero≡QBzero
ιOK0 : (PA : ℕ → Type) (PB : Int / rInt → Type)
  (PA≡PB : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) → PathP (λ i → Type) (PA a) (PB b)) →
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → PA≡PB _ _ depConstr0Correct i) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB _ _ a≡b i) IHa IHb) → PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i) (PAS a IHa) (PBS b IHb))
  (QA : PA zero → Type) (QB : PB depConstrInt/rInt0 → Type)
  (QA≡QB : PathP (λ i → PA≡PB _ _ depConstr0Correct i → Type) QA QB)
  (QAzero : QA PAzero) (QBzero : QB PBzero)
  (QAzero≡QBzero : PathP (λ i → (QA≡QB i) (PAzero≡PBzero i)) QAzero QBzero) → 
  PathP (λ i → (QA≡QB i) (PAzero≡PBzero i)) QAzero (ιInt/rInt0 PB PBset PBzero PBS QB QBzero)
ιOK0 PA PB PA≡PB PBSet PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS QA QB QA≡QB QAzero QBzero QAzero≡QBzero =
  QAzero≡QBzero

-- iota: iota is OK at S (it's cool to lift definitional to propositional equality) because we are eliminating into set (equality first)
ιOKSEq : (PA : ℕ → Type) (PB : Int / rInt → Type)
  (PA≡PB : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) → PathP (λ i → Type) (PA a) (PB b))
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → PA≡PB _ _ depConstr0Correct i) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB _ _ a≡b i) IHa IHb) → PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i) (PAS a IHa) (PBS b IHb))
  (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  PathP
    (λ i →
      elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
      PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i)
    (refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)})
    (ιInt/rIntSEq PB PBset PBzero PBS b)
ιOKSEq PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b =
  toPathP
    (PBset
      (depConstrInt/rIntS b)
      (depElimInt/rInt PB PBset PBzero PBS (depConstrInt/rIntS b))
      (PBS b (depElimInt/rInt PB PBset PBzero PBS b))
      (transport
        (λ i →
           elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
           PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i)
        refl)
      (ιInt/rIntSEq PB PBset PBzero PBS b))

-- rewrite version of the above
ιOKS : (PA : ℕ → Type) (PB : Int / rInt → Type)
  (PA≡PB : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) → PathP (λ i → Type) (PA a) (PB b)) →
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → PA≡PB _ _ depConstr0Correct i) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB _ _ a≡b i) IHa IHb) → PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i) (PAS a IHa) (PBS b IHb))
  (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  (QA : PA (suc a) → Type) (QB : PB (depConstrInt/rIntS b) → Type)
  (QA≡QB : PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i → Type) QA QB)
  (QAS : QA (Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a))) (QBS : QB (depElimInt/rInt PB PBset PBzero PBS (depConstrInt/rIntS b)))
  (QAS≡QBS :
    PathP
      (λ i → QA≡QB i
        (elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i))
      QAS
      QBS) →
  PathP
    (λ i → QA≡QB i
      (PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i))
    QAS
    (ιInt/rIntS PB PBset PBzero PBS b QB QBS)
ιOKS PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b QA QB QA≡QB QAS QBS QAS≡QBS =
  subst
    {x = subst (λ e → QA e) (refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)}) QAS}
    {y = QAS}
    (λ QAS' →
      PathP
        (λ i → QA≡QB i (PAS≡PBS a b (Cubical.Data.Nat.elim {A = PA} PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i))
        QAS'
        (ιInt/rIntS PB PBset PBzero PBS b QB QBS))
    (sym (subst-filler (λ e → QA e) refl QAS))
    (congP
      {A = λ i →
        elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
        PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i}
      {B = λ i p → QA≡QB i (PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i)}
      (λ (i : I) (p : elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i ≡
                      PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i) →
        subst (λ e → QA≡QB i e) p (QAS≡QBS i))
      {x = refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)}}
      {y = ιInt/rIntSEq PB PBset PBzero PBS b}
      (ιOKSEq PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b))

ιOKSEq⁻ : (PA : ℕ → Type) (PB : Int / rInt → Type)
  (PA≡PB : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) → PathP (λ i → Type) (PA a) (PB b))
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → PA≡PB _ _ depConstr0Correct i) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB _ _ a≡b i) IHa IHb) → PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i) (PAS a IHa) (PBS b IHb))
  (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  PathP
    (λ i →
      PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i ≡
      elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i)
    (refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)})
    (sym (ιInt/rIntSEq PB PBset PBzero PBS b))
ιOKSEq⁻ PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b =
  toPathP
    (PBset
      (depConstrInt/rIntS b)
      (PBS b (depElimInt/rInt PB PBset PBzero PBS b))
      (depElimInt/rInt PB PBset PBzero PBS (depConstrInt/rIntS b))
      (transport
        (λ i →
           PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i ≡
           elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i)
        refl)
      (sym (ιInt/rIntSEq PB PBset PBzero PBS b)))

ιOKS⁻ : (PA : ℕ → Type) (PB : Int / rInt → Type)
  (PA≡PB : ∀ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) → PathP (λ i → Type) (PA a) (PB b)) →
  (PBset : ∀ x → isSet (PB x))
  (PAzero : PA zero) (PBzero : PB depConstrInt/rInt0)
  (PAzero≡PBzero : PathP (λ i → PA≡PB _ _ depConstr0Correct i) PAzero PBzero)
  (PAS : ∀ n → PA n → PA (suc n)) (PBS : ∀ n → PB n → PB (depConstrInt/rIntS n))
  (PAS≡PBS : ∀ a b (IHa : PA a) (IHb : PB b) a≡b (IHa≡IHb : PathP (λ i → PA≡PB _ _ a≡b i) IHa IHb) → PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i) (PAS a IHa) (PBS b IHb))
  (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) →
  (QA : PA (suc a) → Type) (QB : PB (depConstrInt/rIntS b) → Type)
  (QA≡QB : PathP (λ i → PA≡PB _ _ (depConstrSCorrect a b a≡b) i → Type) QA QB)
  (QAS : QA (PAS a (Cubical.Data.Nat.elim {A = PA} PAzero PAS a))) (QBS : QB (PBS b (depElimInt/rInt PB PBset PBzero PBS b)))
  (QAS≡QBS : PathP
    (λ i → QA≡QB i
      (PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i))
    QAS
    QBS) →
  PathP
    (λ i → QA≡QB i
      (elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i))
    QAS
    (ιInt/rIntS⁻ PB PBset PBzero PBS b QB QBS)
ιOKS⁻ PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b QA QB QA≡QB QAS QBS QAS≡QBS =
  subst
    {x = subst (λ e → QA e) (refl {x = Cubical.Data.Nat.elim {A = PA} PAzero PAS (suc a)}) QAS}
    {y = QAS}
    (λ QAS' → PathP
      (λ i →
         QA≡QB i
         (elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b)
          PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i))
      QAS'
      (ιInt/rIntS⁻ PB PBset PBzero PBS b QB QBS))
    (sym (subst-filler (λ e → QA e) refl QAS))
    (congP
      {A = λ i →
        PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i ≡
        elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i}
      (λ i (p : PAS≡PBS a b (Cubical.Data.Nat.elim PAzero PAS a) (depElimInt/rInt PB PBset PBzero PBS b) a≡b (elimOK a b a≡b PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS) i ≡
                elimOK (suc a) (depConstrInt/rIntS b) (depConstrSCorrect a b a≡b) PA PB PBset PA≡PB PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS i)
        → subst (λ e → QA≡QB i e) p (QAS≡QBS i))
      (ιOKSEq⁻ PA PB PA≡PB PBset PAzero PBzero PAzero≡PBzero PAS PBS PAS≡PBS a b a≡b))

-- Below, we provide generic theorems allowing users to build paths inductively on terms.
-- This can be used when proving repair was conducted correctly.

-- equivalence is OK by A≡B
equivOK : ℕ ≡ Int / rInt
equivOK = Nat≡Int/rInt

-- application: app is OK by congP
appOK : {T : I → Type ℓ} {F : (i : I) → T i → Type ℓ'}
  (f : (t : T i0) → F i0 t) (f' : (t : T i1) → F i1 t)
  (f≡f' : PathP (λ i → ∀ (t : T i) → F i t) f f')
  (t : T i0) (t' : T i1)
  (t≡t' : PathP T t t') →
  PathP (λ i → F i (t≡t' i)) (f t) (f' t')
appOK f f' f≡f' t t' t≡t' = congP (λ i a → f≡f' i a) t≡t'

-- term abstraction: lam is OK by funExtDep (TODO is this type signature correct though, or too specific?)
lamOK : {T : I → Type ℓ} {F : (i : I) → T i → Type ℓ'}
  (f : (t : T i0) → F i0 t) (f' : (t : T i1) → F i1 t)
  (b≡b' : ∀ {t : T i0} {t' : T i1} (t≡t' : PathP (λ i → T i) t t') →
    PathP (λ i → F i (t≡t' i)) (f t) (f' t')) →
  PathP (λ i → ∀ (t : T i) → F i t) f f'
lamOK {T} {F} f f' b≡b' =
  funExtDep b≡b'
-- t => t', T => T', and Γ, (t : T) ⊢ b => b' || λ (t : T) . b => λ (t' : T') . b'

-- type abstraction: prod is OK by funExtDep (TODO is this type signature correct though, or too specific?)
-- credit to Amelia Liao for the below term
prodOK : {T : I → Type} (PA : (b : T i0) → Type) (PB : (b : T i1) → Type)
  (b≡b' : ∀ {t : T i0} {t' : T i1} (t≡t' : PathP (λ i → T i) t t') → PA t ≡ PB t') →
  ((b : T i0) → PA b) ≡ ((b : T i1) → PB b)
prodOK {T} PA PB b≡b' i = (b : T i) → b≡b' (λ j → alternateFunExtDep.coei→j T i j b) i
-- t => t', T => T', and Γ, (t : T) ⊢ b => b' || Π (t : T) . b => Π (t' : T') . b'

funTypeOK : {TAL TAR TBL TBR : Type} →
  TAL ≡ TBL →
  TAR ≡ TBR →
  (TAL → TAR) ≡ (TBL → TBR)
funTypeOK pL pR i = pL i → pR i

-- variables: var is OK by refl
var : ∀ {T : I → Type} (i : I) (v : T i) → v ≡ v
var {T} i v = refl

-- ind rule for path type
eqOK : {TA TB : Type} → {p : TA ≡ TB} → {AL AR : TA} → {BL BR : TB} →
  PathP (λ i → p i) AL BL →
  PathP (λ i → p i) AR BR →
  PathP (λ i → Type) (AL ≡ AR) (BL ≡ BR)
eqOK pL pR i = pL i ≡ pR i

{- From this, we can already prove add and the proofs about it correct (will do proofs at botom of file) -}

addCorrect :
  ∀ (a b : ℕ) (a' b' : Int / rInt) →
  ∀ (pa : PathP (λ i → Nat≡Int/rInt i) a a') (pb : PathP (λ i → Nat≡Int/rInt i) b b') →
  PathP (λ i → Nat≡Int/rInt i) (add a b) (addInt/rInt a' b')
addCorrect a b a' b' pa pb =
  appOK
    {T = λ i → Nat≡Int/rInt i}
    {F = λ i n → Nat≡Int/rInt i}
    (add a)
    (addInt/rInt a')
    (elimOK a a' pa
      (λ _ → ℕ → ℕ) -- motive of add
      (λ _ → Int / rInt → Int / rInt) -- motive of addInt/rInt
      (λ (_ : Int / rInt) → isSetProd (λ _ → squash/)) -- isSet proof of addInt/rInt
      (λ (a : ℕ) (b : Int / rInt) (a≡b : PathP (λ i → Nat≡Int/rInt i) a b) i → Nat≡Int/rInt i → Nat≡Int/rInt i) -- path between motives
      (λ (b : ℕ) → b) -- base case of add
      (λ (b : Int / rInt) → b) -- base case off addInt/rInt
      (lamOK (λ (b : ℕ) → b) (λ (b : Int / rInt) → b) (λ p → p)) -- path between base cases
      (λ a IH b → suc (IH b)) -- inductive case of add
      (λ a IH b → depConstrInt/rIntS (IH b)) -- inductive case of addInt/rInt
      (λ a a' (IHa : ℕ → ℕ) (IHa' : Int / rInt → Int / rInt) a≡a' IHa≡IHa' → -- path between inductive cases
        lamOK
          (λ b → suc (IHa b))
          (λ b → depConstrInt/rIntS (IHa' b))
          (λ b≡b' → depConstrSCorrect (IHa _) (IHa' _) (appOK IHa IHa' IHa≡IHa' _ _ b≡b'))))
    b
    b'
    pb

{- Porting proofs to nat-like eliminators -}

sucLemNat' : (a : ℕ) → (b : ℕ) → suc (add a b) ≡ add a (suc b)
sucLemNat' a b =
  Cubical.Data.Nat.elim
    {A = λ a → ∀ b → suc (add a b) ≡ add a (suc b)} -- motive P
    (λ b → refl) -- base case
    (λ a (IH : ∀ b → suc (add a b) ≡ add a (suc b)) b →
      -- want to show P (suc a) b, which is suc (add (suc a) b) ≡ add (suc a) (suc b)
      -- we have cong suc (IH b), where (IH b) : suc (add a b) ≡ add a (suc b)
      -- thus, cong suc (IH b) : suc (suc (add a b)) ≡ suc (add a (suc b))
      -- so our definitional equality is:
      --  (suc (add (suc a) b) ≡ add (suc a) (suc b)) ≝ (suc (suc (add a b)) ≡ suc (add a (suc b)))
      --    by δ, unfold add everywhere
      --    this will give us an application of Cubical.Data.Nat.elim (the add defined above)
      --    by Β, take the (λ a b → ...) that add unfolded to, and specialize to each a, b (e.g., (suc a) b)
      --    Now we have (Cubical.Data.Nat.elim ... (suc a)) b
      --    Now by ι, we have suc ((Cubical.Data.Nat.elim ... a) b)
      --    etc.
      cong suc (IH b)) -- inductive case
    a
    b

sucLemInt/rInt' : (a : Int / rInt) -> (b : Int / rInt) -> depConstrInt/rIntS (addInt/rInt a b) ≡ (addInt/rInt a (depConstrInt/rIntS b)) -- S (a + b) = a + S b
sucLemInt/rInt' a b =
  depElimInt/rInt
    (λ (a : Int / rInt) → ∀ (b : Int / rInt) → depConstrInt/rIntS (addInt/rInt a b) ≡ addInt/rInt a (depConstrInt/rIntS b))
    (λ (a : Int / rInt) → isSetProd (λ b → isProp→isSet (squash/ _ _)))
    (λ b → refl) -- base case
    (λ a (IH : ∀ b → depConstrInt/rIntS (addInt/rInt a b) ≡ addInt/rInt a (depConstrInt/rIntS b)) b → -- inductive case
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

-- Now, we repair a proof of commutativity
addCommNat : (a : ℕ) → (b : ℕ) → add a b ≡ add b a
addCommNat a b =
  Cubical.Data.Nat.elim
    {A = λ a → ∀ b → add a b ≡ add b a}
    (λ b →
      Cubical.Data.Nat.elim
        {A = λ b → add 0 b ≡ add b 0}
        refl
        (λ b (IHb : add 0 b ≡ add b 0) →
          cong suc IHb)
        b)
    (λ a (IHa : ∀ b → add a b ≡ add b a) b →
      cong suc (IHa b) ∙ sucLemNat' b a) 
    a
    b

addCommInt/rInt : (a : Int / rInt) → (b : Int / rInt) → addInt/rInt a b ≡ addInt/rInt b a
addCommInt/rInt a b =
  depElimInt/rInt
    (λ a → ∀ b → addInt/rInt a b ≡ addInt/rInt b a)
    (λ (a : Int / rInt) →
      isSetProd
        (λ b → isProp→isSet (squash/ _ _)))
    (λ b →
      depElimInt/rInt
        (λ b → addInt/rInt [ pos zero ] b ≡ addInt/rInt b [ pos zero ])
        (λ b → isProp→isSet (squash/ _ _))
        refl
        (λ b (IHb : addInt/rInt [ pos zero ] b ≡ addInt/rInt b [ pos zero ]) →
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
              addInt/rInt [ pos zero ] (depConstrInt/rIntS b) ≡ add-Sb [ pos zero ])
            (cong depConstrInt/rIntS IHb))
        b)
    (λ a (IHa : ∀ b → addInt/rInt a b ≡ addInt/rInt b a) b →
      -- T := P (S a) b := S a + b ≡ b + S a
      ιInt/rIntS⁻
        (λ _ → Int / rInt → Int / rInt)
        (λ _ → isSetProd (λ _ → squash/))
        (λ b → b)
        (λ _ (IH : Int / rInt → Int / rInt) (m : Int / rInt) → depConstrInt/rIntS (IH m))
        a
        (λ add-Sa →
          add-Sa b ≡ addInt/rInt b (depConstrInt/rIntS a))
        (cong depConstrInt/rIntS (IHa b) ∙ sucLemInt/rInt' b a)) 
    a
    b

-- We repair a proof that 0 is a right identity for addition
add0R : (n : ℕ) → add n 0 ≡ n
add0R =
  Cubical.Data.Nat.elim
    {A = λ n → add n 0 ≡ n}
    refl
    (λ a (IHa : add a 0 ≡ a) →
      congS suc IHa)

add0RInt/rInt : (n' : Int / rInt) → addInt/rInt n' depConstrInt/rInt0 ≡ n'
add0RInt/rInt =
  depElimInt/rInt
    (λ n' → addInt/rInt n' depConstrInt/rInt0 ≡ n')
    (λ n' → isProp→isSet (squash/ _ _))
    refl
    (λ n' (IHn' : addInt/rInt n' depConstrInt/rInt0 ≡ n') →
      ιInt/rIntS⁻
        (λ _ → Int / rInt → Int / rInt)
        (λ _ → isSetProd (λ _ → squash/))
        (λ b → b)
        (λ _ IH m → depConstrInt/rIntS (IH m))
        n'
        (λ f → f depConstrInt/rInt0 ≡ depConstrInt/rIntS n')
        (congS depConstrInt/rIntS IHn'))

-- Lemma which allows us to prove many theorems are repaired correctly easily.
repairSetEqsCorrect :
 {A B : Type} →
 (T : A ≡ B) →
 (t0 : A) (t1 : B) (t0≡t1 : PathP (λ i → T i) t0 t1) →
 (t2 : A) (t3 : B) (t2≡t3 : PathP (λ i → T i) t2 t3) →
 (P : PathP (λ i → T i) t0 t1) →
 (P2 : PathP (λ i → T i) t2 t3) →
 (PA : t0 ≡ t2) →
 (PB : t1 ≡ t3) →
 isSet A →
 (PathP
    (λ i → P i ≡ P2 i)
    PA
    PB) 
repairSetEqsCorrect {A = A} =
  J
    (λ B T →
       (t0 : A) (t1 : B) (t0≡t1 : PathP (λ i → T i) t0 t1) →
       (t2 : A) (t3 : B) (t2≡t3 : PathP (λ i → T i) t2 t3) →
       (P : PathP (λ i → T i) t0 t1) →
       (P2 : PathP (λ i → T i) t2 t3) →
       (PA : t0 ≡ t2) →
       (PB : t1 ≡ t3) →
       isSet A →
       (PathP
          (λ i → P i ≡ P2 i)
          (PA)
          (PB)))
    λ t0 t1 → J
      (λ t1 t0≡t1 →
        (t2 : A) (t3 : A) (t2≡t3 : t2 ≡ t3) →
        (P : t0 ≡ t1) →
        (P2 : t2 ≡ t3) →
        (PA : t0 ≡ t2) →
        (PB : t1 ≡ t3) →
        isSet A →
        (PathP
           (λ i → P i ≡ P2 i)
           (PA)
           (PB)))
      λ t2 t3 → J
        (λ t3 t2≡t3 →
          (P : t0 ≡ t0) →
          (P2 : t2 ≡ t3) →
          (PA : t0 ≡ t2) →
          (PB : t0 ≡ t3) →
          isSet A →
          (PathP
             (λ i → P i ≡ P2 i)
             (PA)
             (PB)))
        λ P P2 PA PB p → compPathL→PathP {p = P} {q = P2} {r = PA} {s = PB} (p t0 t2 _ _)

-- Now, we prove that add0R and addComm were repaired correctly
add0RCorrect : (n : ℕ) (n' : Int / rInt) (pn : PathP (λ i → Nat≡Int/rInt i) n n') →
  PathP (λ i → addCorrect n 0 n' depConstrInt/rInt0 pn depConstr0Correct i ≡ (pn i)) (add0R n) (add0RInt/rInt n')
add0RCorrect n n' pn =
  repairSetEqsCorrect
    Nat≡Int/rInt
    (add n 0)
    (addInt/rInt n' depConstrInt/rInt0)
    (addCorrect n 0 n' depConstrInt/rInt0 pn depConstr0Correct)
    n
    n'
    pn
    (addCorrect n 0 n' depConstrInt/rInt0 pn depConstr0Correct)
    pn
    (add0R n)
    (add0RInt/rInt n')
    isSetℕ
    
addCommCorrect :
  (a : ℕ) (a' : Int / rInt) (pa : PathP (λ i → Nat≡Int/rInt i) a a') →
  (b : ℕ) (b' : Int / rInt) (pb : PathP (λ i → Nat≡Int/rInt i) b b') →
  PathP (λ i → addCorrect a b a' b' pa pb i ≡ addCorrect b a b' a' pb pa i) (addCommNat a b) (addCommInt/rInt a' b')
addCommCorrect a a' pa b b' pb =
  repairSetEqsCorrect
    Nat≡Int/rInt
    (add a b)
    (addInt/rInt a' b')
    (addCorrect a b a' b' pa pb)
    (add b a)
    (addInt/rInt b' a')
    (addCorrect b a b' a' pb pa)
    (addCorrect a b a' b' pa pb)
    (addCorrect b a b' a' pb pa)
    (addCommNat a b)
    (addCommInt/rInt a' b')
    isSetℕ

open import Cubical.Data.Bool

-- This example demonstrates the importance of which path the PathPs are along.
-- We use the elimOK rule to construct a PathP between two applications of functions which superficially seem different.
-- This is possible because we construct the PathP using the equality notEq, the automorphism on Bool which sends true to false and false to true.
-- Thus, true at one end of the path is connected to false at the other end of the path.
-- To get correct proofs of correct repair, we need to manually ensure that the PathP is along a path indicating correct repair;
-- the presence of notEq in the first PathP argument here, as opposed to refl, indicates that this is not the case in this example.
incorrect_correctness_proof :
  PathP
    (λ i → notEq i)
    (Cubical.Data.Nat.elim {A = λ _ → Bool} true (λ _ _ → true) 0)
    (depElimInt/rInt (λ _ → Bool) (λ _ → isSetBool) false (λ _ _ → false) depConstrInt/rInt0) 
incorrect_correctness_proof =
  elimOK
    0
    depConstrInt/rInt0
    depConstr0Correct
    (λ _ → Bool)
    (λ _ → Bool)
    (λ _ → isSetBool)
    (λ _ _ _ → notEq)
    true
    false
    (toPathP refl)
    (λ _ _ → true)
    (λ _ _ → false)
    (λ _ _ _ _ _ _ → toPathP refl)
