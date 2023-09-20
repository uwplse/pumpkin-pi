{-# OPTIONS --safe --cubical #-}
module grothendieck_int_equiv where

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
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Nat as Nat
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Relation.Binary.Base

-- dependent constructors/eliminators on standard library inductive ℤ

data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

depConstrℤPos : ℕ → ℤ
depConstrℤPos n = pos n

depConstrℤNegSuc : ℕ → ℤ
depConstrℤNegSuc n = negsuc n

depElimℤ : (P : ℤ → Set) → (∀ n → P (depConstrℤPos n)) → (∀ n → P (depConstrℤNegSuc n)) → ∀ z → P z
depElimℤ P posP negP (pos n) = posP n
depElimℤ P posP negsucP (negsuc n) = negsucP n

ιℤPos : (P : ℤ → Set) → (posP : (n : ℕ) → P (depConstrℤPos n)) → (negSucP : (n : ℕ) → P (depConstrℤNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrℤPos n) → Set) → Q (depElimℤ P posP negSucP (depConstrℤPos n)) → Q (posP n)
ιℤPos P posP negSucP n Q Qp = Qp

ιℤNegSuc : (P : ℤ → Set) → (posP : (n : ℕ) → P (depConstrℤPos n)) → (negSucP : (n : ℕ) → P (depConstrℤNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrℤNegSuc n) → Set) → Q (depElimℤ P posP negSucP (depConstrℤNegSuc n)) → Q (negSucP n)
ιℤNegSuc P posP negSucP n Q Qp = Qp

-- Addition on integers, based on standard library functions.
sucℤ : ℤ → ℤ
sucℤ z = depElimℤ
           (λ _ → ℤ)
           (λ n → depConstrℤPos (suc n))
           (λ n → Nat.elim
             (depConstrℤPos zero)
             (λ m _ → depConstrℤNegSuc m )
             n)
           z

predℤ : ℤ → ℤ
predℤ z = depElimℤ
            (λ _ → ℤ)
            (λ n → Nat.elim
              (depConstrℤNegSuc zero)
              (λ m _ → depConstrℤPos m)
              n)
            (λ n → depConstrℤNegSuc (suc n))
            z

_+pos_ : ℤ → ℕ → ℤ
z +pos n = Nat.elim
             z
             (λ _ p → sucℤ p)
             n

_+negsuc_ : ℤ → ℕ → ℤ
z +negsuc n = Nat.elim
                (predℤ z)
                (λ _ p → predℤ p)
                n

_+ℤ_ : ℤ → ℤ → ℤ
m +ℤ n = depElimℤ
          (λ _ → ℤ)
          (λ p → m +pos p)
          (λ p → m +negsuc p)
          n

add0Lℤ : (z : ℤ) → z ≡ (depConstrℤPos 0) +ℤ z
add0Lℤ z = depElimℤ
                (λ z → z ≡ (depConstrℤPos 0) +ℤ z)
                (λ n → Nat.elim {A = λ m → depConstrℤPos m ≡ (depConstrℤPos 0) +ℤ (depConstrℤPos m)} refl (λ m Pm → cong sucℤ Pm) n)
                (λ n → Nat.elim {A = λ m → depConstrℤNegSuc m ≡ (depConstrℤPos 0) +ℤ (depConstrℤNegSuc m)} refl (λ m Pm → cong predℤ Pm) n)
                z

-- Grothendieck group construction of ℤ.

R : (ℕ × ℕ) → (ℕ × ℕ) → Type
R (x1 , x2) (y1 , y2) = x1 Nat.+ y2 ≡ x2 Nat.+ y1

GZ : Type
GZ = (ℕ × ℕ) / R

depConstrGZPos : ℕ → GZ
depConstrGZPos n = [ (n , 0) ]

depConstrGZNegSuc : ℕ → GZ
depConstrGZNegSuc n = [ (0 , suc n) ]

sucRPres : (n1 : ℕ) → (n2 : ℕ) → [ (suc n1 , suc n2) ] ≡ [_] {R = R} (n1 , n2)
sucRPres n1 n2 = eq/ (suc n1 , suc n2) (n1 , n2) (Rlem n1 n2) where
  Rlem : (n1 : ℕ) → (n2 : ℕ) → R (suc n1 , suc n2) (n1 , n2)
  Rlem n1 n2 = cong suc (Nat.+-comm n1 n2)

sucRPres⁻ : (n1 : ℕ) → (n2 : ℕ) → [_] {R = R} (n1 , n2) ≡ [ (suc n1 , suc n2) ]
sucRPres⁻ n1 n2 = sym (sucRPres n1 n2)

canonicalize : (ℕ × ℕ) → (ℕ × ℕ)
canonicalize (zero , n2) = (zero , n2)
canonicalize (suc n1 , zero) = (suc n1 , zero)
canonicalize (suc n1 , suc n2) = canonicalize (n1 , n2)

canonicalizePres : (p : ℕ × ℕ) → [_] {R = R} p ≡ [ canonicalize p ]
canonicalizePres (zero , n2) = refl
canonicalizePres (suc n1 , zero) = refl
canonicalizePres (suc n1 , suc n2) = (sucRPres n1 n2) ∙ (canonicalizePres (n1 , n2))

canonicalizePres⁻ : (p : ℕ × ℕ) → [_] {R = R} (canonicalize p) ≡ [ p ]
canonicalizePres⁻ p = sym (canonicalizePres p)

canonicalizeSignDec : (p : ℕ × ℕ) → (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize p ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m))))
canonicalizeSignDec (zero , zero) = inl (zero , refl)
canonicalizeSignDec (zero , suc n2) = inr ((suc n2) , (refl , (n2 , refl)))
canonicalizeSignDec (suc n1 , zero) = inl ((suc n1) , refl)
canonicalizeSignDec (suc n1 , suc n2) = canonicalizeSignDec (n1 , n2)

canonicalizeSame : (a : ℕ) → (zero , zero) ≡ canonicalize (a , a)
canonicalizeSame zero = refl
canonicalizeSame (suc a) = canonicalizeSame a

canonicalizeRZ : (a : ℕ) → canonicalize (a , zero) ≡ (a , zero)
canonicalizeRZ zero = refl
canonicalizeRZ (suc a) = refl

canonicalIsCanonical : (a b : ℕ × ℕ) → R a b → canonicalize a ≡ canonicalize b
canonicalIsCanonical (zero , a2) (zero , b2) r = ×≡ refl (sym (r ∙ (+-zero a2)))
canonicalIsCanonical (zero , zero) (suc b1 , zero) r = Cubical.Data.Empty.rec (znots r)
canonicalIsCanonical (zero , zero) (suc b1 , suc b2) r = canonicalIsCanonical ((zero , zero)) ((b1 , b2)) (injSuc r)
canonicalIsCanonical (zero , suc a2) (suc b1 , zero) r = Cubical.Data.Empty.rec (znots r)
canonicalIsCanonical (zero , suc a2) (suc b1 , suc b2) r = canonicalIsCanonical ((zero , suc a2)) ((b1 , b2)) ((injSuc r) ∙ (+-suc a2 b1))
canonicalIsCanonical (suc a1 , zero) (zero , b2) r = Cubical.Data.Empty.rec (snotz r)
canonicalIsCanonical (suc a1 , suc a2) (zero , b2) r = canonicalIsCanonical (a1 , a2) (zero , b2) (injSuc r)
canonicalIsCanonical (suc a1 , zero) (suc b1 , zero) r = ×≡ (suc a1 ≡⟨ cong suc (sym (+-zero a1)) ⟩ suc (a1 Nat.+ zero) ≡⟨ r ⟩ suc b1 ∎) refl
canonicalIsCanonical (suc a1 , zero) (suc b1 , suc b2) r = canonicalIsCanonical (suc a1 , zero) (b1 , b2) ((sym (+-suc a1 b2)) ∙ (injSuc r))
canonicalIsCanonical (suc a1 , suc a2) (suc b1 , b2) r = canonicalIsCanonical (a1 , a2) (suc b1 , b2) (injSuc r)

canonicalizeIdempotent : (p : ℕ × ℕ) → canonicalize p ≡ canonicalize (canonicalize p)
canonicalizeIdempotent (zero , p2) = refl
canonicalizeIdempotent (suc p1 , zero) = refl
canonicalizeIdempotent (suc p1 , suc p2) = canonicalizeIdempotent (p1 , p2)

isSetProd : {A B : Set} → isSet A → isSet B → isSet (A × B)
isSetProd {A} {B} setA setB = isOfHLevelProd 2 setA setB

isSetℕ×ℕ : isSet (ℕ × ℕ)
isSetℕ×ℕ = isSetProd isSetℕ isSetℕ

sumRememberEq : {A B : Set} → (x : A ⊎ B) → (Σ[ a ∈ A ] x ≡ inl a) ⊎ (Σ[ b ∈ B ] x ≡ inr b)
sumRememberEq (inl x) = inl (x , refl)
sumRememberEq (inr x) = inr (x , refl)

open BinaryRelation

-- 
-- isSetProd : {A B : Set} → isSet A → isSet B → isSet (A × B)
-- isSetProd {A} {B} setA setB = isOfHLevelProd 2 setA setB
-- 
Rprop : isPropValued R
Rprop (a1 , a2) (b1 , b2) p1 p2 = isSetℕ (a1 Nat.+ b2) (a2 Nat.+ b1) p1 p2

isReflR : isRefl R
isReflR (x1 , x2) = Nat.+-comm x1 x2
 
isSymR : isSym R
isSymR (x1 , x2) (y1 , y2) r = (Nat.+-comm y1 x2) ∙ (sym r) ∙ (Nat.+-comm x1 y2)

addBothSides : {a b c d : ℕ} → (a ≡ b) → (a + c ≡ b + d) → (c ≡ d)
addBothSides {a} {b} {c} {d} p1 p2 = inj-m+ {m = b} (subst (λ y → y + c ≡ b + d) p1 p2)

open import Cubical.Data.Vec.Base
open import Cubical.Data.FinData hiding (suc)
open import Cubical.Tactics.NatSolver.NatExpression
open import Cubical.Tactics.NatSolver.HornerForms
open import Cubical.Tactics.NatSolver.Solver
open import Cubical.Tactics.NatSolver.Reflection

open EqualityToNormalform renaming (solve to natSolve)
open IteratedHornerOperations hiding (X)

varType6 = IteratedHornerForms 6
var06 : varType6
var06 = Variable 6 (Fin.zero)

var16 : varType6
var16 = Variable 6 (Fin.suc Fin.zero)

var26 : varType6
var26 = Variable 6 (Fin.suc (Fin.suc Fin.zero))

var36 : varType6
var36 = Variable 6 (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

var46 : varType6
var46 = Variable 6 (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))

var56 : varType6
var56 = Variable 6 (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

X1 : Expr 6
X1 = ∣ Fin.zero

X2 : Expr 6
X2 = ∣ (Fin.suc Fin.zero)

Y1 : Expr 6
Y1 = ∣ (Fin.suc (Fin.suc Fin.zero))

Y2 : Expr 6
Y2 = ∣ (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

Z1 : Expr 6
Z1 = ∣ (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))

Z2 : Expr 6
Z2 = ∣ (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

isTransR : isTrans R
isTransR (x1 , x2) (y1 , y2) (z1 , z2) r1 r2 = addBothSides (sym r1) (addBothSides (sym r2) let
                                                 lhs = Y2 +' Z1 +' (X2 +' Y1 +' (X1 +' Z2)) 
                                                 rhs = Y1 +' Z2 +' (X1 +' Y2 +' (X2 +' Z1))
                                                 in natSolve lhs rhs (x1 ∷ x2 ∷ y1 ∷ y2 ∷ z1 ∷ z2 ∷ []) refl)

REquivRel : isEquivRel R
REquivRel = equivRel isReflR isSymR isTransR

RIrrel : ∀ x1 x2 (p : x1 Nat.+ x2 ≡ x2 Nat.+ x1) → p ≡ isReflR (x1 , x2)
RIrrel x1 x2 p = isSetℕ _ _ p (isReflR (x1 , x2))

depElimGZ : (P : GZ → Set) → (∀ x → isSet (P x)) → (∀ n → P (depConstrGZPos n)) → (∀ n → P (depConstrGZNegSuc n)) → ∀ z → P z
depElimGZ P set posP negsucP = SetQuotients.elim set func resp where
  func : (p : ℕ × ℕ) → P [ p ]
  func p = Sum.rec (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (snd x) ∙ refl))))
                                    (posP (fst x)))
                   (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (proj₁ (snd x))) ∙ (cong [_] (×≡ refl (snd (proj₂ (snd x))))))))
                                    (negsucP (fst (proj₂ (snd x)))))
                   (canonicalizeSignDec p)
  funcLeft : (p : ℕ × ℕ) →
             (y : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize p ≡ (n , zero)) ] (canonicalizeSignDec p ≡ inl a)) →
             func p ≡ transport (cong P (sym ((canonicalizePres p) ∙ cong [_] (snd (fst y)) ∙ refl)))
                                (posP (fst (fst y)))
  funcLeft p y = subst (λ path → Sum.rec (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (snd x) ∙ refl))))
                                                          (posP (fst x)))
                                         (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (proj₁ (snd x))) ∙ (cong [_] (×≡ refl (snd (proj₂ (snd x))))))))
                                                          (negsucP (fst (proj₂ (snd x)))))
                                         (path)
                                  ≡ transport (cong P (sym ((canonicalizePres p) ∙ cong [_] (snd (fst y)) ∙ refl)))
                                              (posP (fst (fst y))))
                       (sym (snd y))
                       refl
  funcRight : (p : ℕ × ℕ) →
              (y : Σ[ a ∈ (Σ[ n ∈ ℕ ] ((canonicalize p ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ] (canonicalizeSignDec p ≡ inr a)) →
              func p ≡ transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (proj₁ (snd (fst y)))) ∙ (cong [_] (×≡ refl (snd (proj₂ (snd (fst y)))))))))
                                 (negsucP (fst (proj₂ (snd (fst y)))))
  funcRight p y = subst (λ path → Sum.rec (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (snd x) ∙ refl))))
                                                           (posP (fst x)))
                                          (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (proj₁ (snd x))) ∙ (cong [_] (×≡ refl (snd (proj₂ (snd x))))))))
                                                           (negsucP (fst (proj₂ (snd x)))))
                                          (path)
                                  ≡ transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (proj₁ (snd (fst y)))) ∙ (cong [_] (×≡ refl (snd (proj₂ (snd (fst y)))))))))
                                              (negsucP (fst (proj₂ (snd (fst y))))))
                        (sym (snd y))
                        refl
  innerEqLeft : (p1 p2 : ℕ) →
                (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize (p1 , p2) ≡ (n , zero)) ] (canonicalizeSignDec (p1 , p2) ≡ inl a)) →
                PathP
                  (λ i → sucRPres p1 p2 i ≡ depConstrGZPos (fst (fst x)))          
                  (((sucRPres p1 p2 ∙ canonicalizePres (p1 , p2)) ∙ cong [_] (snd (fst x)) ∙ refl))          
                  (canonicalizePres (p1 , p2) ∙ cong [_] (snd (fst x)) ∙ refl)
  innerEqLeft p1 p2 x = toPathP (squash/ _ _ _ _)
  innerEqRight : (p1 p2 : ℕ) →
         (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] ((canonicalize (p1 , p2) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ] (canonicalizeSignDec (p1 , p2) ≡ inr a)) →
         PathP
          (λ i → sucRPres p1 p2 i ≡ depConstrGZNegSuc (fst (proj₂ (snd (fst x)))))
          ((sucRPres p1 p2 ∙ canonicalizePres (p1 , p2)) ∙
          cong [_] (proj₁ (snd (fst x))) ∙
          cong [_] (λ i → refl {x = zero} i , snd (proj₂ (snd (fst x))) i))
          (canonicalizePres (p1 , p2) ∙
          cong [_] (proj₁ (snd (fst x))) ∙
          cong [_] (λ i → refl {x = zero} i , snd (proj₂ (snd (fst x))) i))
  innerEqRight p1 p2 x = toPathP (squash/ _ _ _ _)
  funcCanonical : (p : ℕ × ℕ) → PathP (λ i → P (canonicalizePres p i)) (func p) (func (canonicalize p))
  funcCanonical (zero , p2) = refl
  funcCanonical (suc p1 , zero) = refl
  funcCanonical (suc p1 , suc p2) =
    compPathP'
      {B = P}
      (Sum.rec
        (λ x → subst2
          (λ y z → PathP (λ i → P (sucRPres p1 p2 i)) y z)
          (sym (funcLeft (suc p1 , suc p2) x))
          (sym (funcLeft (p1 , p2) x))
          (congP (λ i p → transport (cong P (sym p)) (posP (fst (fst x)))) (innerEqLeft p1 p2 x)))
        (λ x → subst2
          (λ y z → PathP (λ i → P (sucRPres p1 p2 i)) y z)
          (sym (funcRight (suc p1 , suc p2) x))
          (sym (funcRight (p1 , p2) x))
          (congP (λ i p → transport (cong P (sym p)) (negsucP (fst (proj₂ (snd (fst x)))))) (innerEqRight p1 p2 x)))
        (sumRememberEq (canonicalizeSignDec (p1 , p2))))
      (funcCanonical (p1 , p2))
  funcCanonical⁻ : (p : ℕ × ℕ) → PathP (λ i → P (canonicalizePres⁻ p i)) (func (canonicalize p)) (func p)
  funcCanonical⁻ p = symP (funcCanonical p)
  composedPaths : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b)) i)) (func a) (func b)
  composedPaths a b r = compPathP' {B = P} (funcCanonical a) (compPathP' {B = P} (cong func (canonicalIsCanonical a b r)) (funcCanonical⁻ b))
  typesSame : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b)) i)) (func a) (func b) ≡ PathP (λ i → P (eq/ a b r i)) (func a) (func b)
  typesSame a b r = cong (λ x → PathP (λ i → P (x i)) (func a) (func b)) (squash/ [ a ] [ b ] ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b))) (eq/ a b r))
  resp : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P (eq/ a b r i)) (func a) (func b)
  resp a b r = transport (typesSame a b r) (composedPaths a b r)

ιGZPosEq : (P : GZ → Set) → (pset : (x : GZ) → isSet (P x)) → (posP : (n : ℕ) → P (depConstrGZPos n)) → (negSucP : (n : ℕ) → P (depConstrGZNegSuc n)) → (n : ℕ) →
    depElimGZ P pset posP negSucP (depConstrGZPos n) ≡ posP n
ιGZPosEq P pset posP negSucP zero = lem ∙ (transportRefl (posP zero)) where
  lem3 : refl ≡ sym ((canonicalizePres (zero , zero)) ∙ (cong [_] (refl) ∙ refl))
  lem3 = squash/ [ zero , zero ] [ zero , zero ] _ _
  lem2 : (cong P (sym ((canonicalizePres (zero , zero)) ∙ (cong [_] (refl) ∙ refl)))) ≡ refl
  lem2 = subst (λ path → cong P path ≡ refl) lem3 refl
  lem : transport (cong P (sym ((canonicalizePres (zero , zero)) ∙ (cong [_] (refl) ∙ refl))))
                  (posP zero)
        ≡ transport refl (posP zero)
  lem = subst (λ path → transport path (posP zero) ≡ transport refl (posP zero)) (sym lem2) refl
ιGZPosEq P pset posP negSucP (suc n) = lem ∙ (transportRefl (posP (suc n))) where
  lem3 : refl ≡ sym ((canonicalizePres (suc n , zero)) ∙ (cong [_] (refl) ∙ refl))
  lem3 = squash/ [ suc n , zero ] [ suc n , zero ] _ _
  lem2 : (cong P (sym ((canonicalizePres (suc n , zero)) ∙ (cong [_] (refl) ∙ refl)))) ≡ refl
  lem2 = subst (λ path → cong P path ≡ refl) lem3 refl
  lem : transport (cong P (sym ((canonicalizePres (suc n , zero)) ∙ (cong [_] (refl) ∙ refl))))
                  (posP (suc n))
        ≡ transport refl (posP (suc n))
  lem = subst (λ path → transport path (posP (suc n)) ≡ transport refl (posP (suc n))) (sym lem2) refl

ιGZPos : (P : GZ → Set) → (pset : ∀ x → isSet (P x)) → (posP : (n : ℕ) → P (depConstrGZPos n)) → (negSucP : (n : ℕ) → P (depConstrGZNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrGZPos n) → Set) → Q (depElimGZ P pset posP negSucP (depConstrGZPos n)) → Q (posP n)
ιGZPos P pset posP negSucP n Q Qp = subst (λ e → Q e) (ιGZPosEq P pset posP negSucP n) Qp

ιGZPos⁻ : (P : GZ → Set) → (pset : ∀ x → isSet (P x)) → (posP : (n : ℕ) → P (depConstrGZPos n)) → (negSucP : (n : ℕ) → P (depConstrGZNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrGZPos n) → Set) → Q (posP n) → Q (depElimGZ P pset posP negSucP (depConstrGZPos n))
ιGZPos⁻ P pset posP negSucP n Q Qp = subst (λ e → Q e) (sym (ιGZPosEq P pset posP negSucP n)) Qp 

ιGZNegSucEq : (P : GZ → Set) → (pset : (x : GZ) → isSet (P x)) → (posP : (n : ℕ) → P (depConstrGZPos n)) → (negSucP : (n : ℕ) → P (depConstrGZNegSuc n)) → (n : ℕ) →
    depElimGZ P pset posP negSucP (depConstrGZNegSuc n) ≡ negSucP n
ιGZNegSucEq P pset posP negSucP zero = lem ∙ transportRefl (negSucP zero) where
  lem3 : refl ≡ sym ((canonicalizePres (zero , suc zero)) ∙ (cong [_] refl) ∙ (cong [_] (×≡ refl refl)))
  lem3 = squash/ [ zero , suc zero ] [ zero , suc zero ] _ _
  lem2 : (cong P (sym ((canonicalizePres (zero , suc zero)) ∙ (cong [_] refl) ∙ (cong [_] (×≡ refl refl))))) ≡ refl
  lem2 = subst (λ path → cong P path ≡ refl) lem3 refl
  lem : transport (cong P (sym ((canonicalizePres (zero , suc zero)) ∙ (cong [_] refl) ∙ (cong [_] (×≡ refl refl)))))
                  (negSucP zero)
        ≡ transport refl (negSucP zero)
  lem = subst (λ path → transport path (negSucP zero) ≡ transport refl (negSucP zero)) (sym lem2) refl
ιGZNegSucEq P pset posP negSucP (suc n) = lem ∙ transportRefl (negSucP (suc n)) where
  lem3 : refl ≡ sym ((canonicalizePres (zero , suc (suc n))) ∙ (cong [_] refl) ∙ (cong [_] (×≡ refl refl)))
  lem3 = squash/ [ zero , suc (suc n) ] [ zero , suc (suc n) ] _ _
  lem2 : (cong P (sym ((canonicalizePres (zero , suc (suc n))) ∙ (cong [_] refl) ∙ (cong [_] (×≡ refl refl))))) ≡ refl
  lem2 = subst (λ path → cong P path ≡ refl) lem3 refl
  lem : transport (cong P (sym ((canonicalizePres (zero , suc (suc n))) ∙ (cong [_] refl) ∙ (cong [_] (×≡ refl refl)))))
                  (negSucP (suc n))
        ≡ transport refl (negSucP (suc n))
  lem = subst (λ path → transport path (negSucP (suc n)) ≡ transport refl (negSucP (suc n))) (sym lem2) refl

ιGZNegSuc : (P : GZ → Set) → (pset : ∀ x → isSet (P x)) → (posP : (n : ℕ) → P (depConstrGZPos n)) → (negSucP : (n : ℕ) → P (depConstrGZNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrGZNegSuc n) → Set) → Q (depElimGZ P pset posP negSucP (depConstrGZNegSuc n)) → Q (negSucP n)
ιGZNegSuc P pset posP negSucP n Q Qp = subst (λ e → Q e) (ιGZNegSucEq P pset posP negSucP n) Qp

ιGZNegSuc⁻ : (P : GZ → Set) → (pset : ∀ x → isSet (P x)) → (posP : (n : ℕ) → P (depConstrGZPos n)) → (negSucP : (n : ℕ) → P (depConstrGZNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrGZNegSuc n) → Set) → Q (negSucP n) → Q (depElimGZ P pset posP negSucP (depConstrGZNegSuc n))
ιGZNegSuc⁻ P pset posP negSucP n Q Qp = subst (λ e → Q e) (sym (ιGZNegSucEq P pset posP negSucP n)) Qp

isSetGZ : isSet GZ
isSetGZ = squash/

-- Repaired addition function.

sucGZ : GZ → GZ
sucGZ z = depElimGZ
           (λ _ → GZ)
           (λ _ → isSetGZ)
           (λ n → depConstrGZPos (suc n))
           (λ n → Nat.elim
             (depConstrGZPos zero)
             (λ m _ → depConstrGZNegSuc m )
             n)
           z

predGZ : GZ → GZ
predGZ z = depElimGZ
             (λ _ → GZ)
             (λ _ → isSetGZ)
             (λ n → Nat.elim
               (depConstrGZNegSuc zero)
               (λ m _ → depConstrGZPos m)
               n)
             (λ n → depConstrGZNegSuc (suc n))
             z

_+posGZ_ : GZ → ℕ → GZ
z +posGZ n = Nat.elim
               z
               (λ _ p → sucGZ p)
               n

_+negsucGZ_ : GZ → ℕ → GZ
z +negsucGZ n = Nat.elim
                  (predGZ z)
                  (λ _ p → predGZ p)
                  n

_+GZ_ : GZ → GZ → GZ
m +GZ n = depElimGZ
            (λ _ → GZ)
            (λ _ → isSetGZ)
            (λ p → m +posGZ p)
            (λ p → m +negsucGZ p)
            n

-- Repaired proof that 0 is a left identity for addition.

add0LGZ : (z : GZ) → z ≡ (depConstrGZPos 0) +GZ z
add0LGZ z = depElimGZ
                (λ z → z ≡ (depConstrGZPos 0) +GZ z)
                (λ x → isProp→isSet (isSetGZ x ((depConstrGZPos 0) +GZ x)))
                (λ n → Nat.elim
                          {A = λ m → depConstrGZPos m ≡ (depConstrGZPos 0) +GZ (depConstrGZPos m)}
                          refl
                          (λ m Pm → ιGZPos
                                       (λ _ → GZ)
                                       (λ _ → isSetGZ)
                                       (λ n → depConstrGZPos (suc n))
                                       (λ n → Nat.elim
                                         (depConstrGZPos zero)
                                         (λ m _ → depConstrGZNegSuc m )
                                         n)
                                       m
                                       (λ s → s ≡ (depConstrGZPos 0) +GZ (depConstrGZPos (suc m))) --need to iota for +GZ and sucGZ separately
                                       (ιGZPos⁻
                                         (λ _ → GZ)
                                         (λ _ → isSetGZ)
                                         (λ p → depConstrGZPos 0 +posGZ p)
                                         (λ p → depConstrGZPos 0 +negsucGZ p)
                                         (suc m)
                                         (λ s → depElimGZ
                                                  (λ _ → GZ)
                                                  (λ _ → isSetGZ)
                                                  (λ n₁ → depConstrGZPos (suc n₁))
                                                  (λ n₁ → Nat.elim (depConstrGZPos zero) (λ m₁ _ → depConstrGZNegSuc m₁) n₁)
                                                  (depConstrGZPos m)
                                                 ≡ s)
                                         (ιGZPos
                                           (λ _ → GZ)
                                           (λ _ → isSetGZ)
                                           (λ p → depConstrGZPos 0 +posGZ p)
                                           (λ p → depConstrGZPos 0 +negsucGZ p)
                                           m
                                           (λ s → depElimGZ
                                                    (λ _ → GZ)
                                                    (λ _ → isSetGZ)
                                                    (λ n₁ → depConstrGZPos (suc n₁))
                                                    (λ n₁ → Nat.elim (depConstrGZPos zero) (λ m₁ _ → depConstrGZNegSuc m₁) n₁)
                                                    (depConstrGZPos m)
                                                   ≡ sucGZ s)
                                           (cong sucGZ Pm))))
                          n)
                (λ n → Nat.elim
                          {A = λ m → depConstrGZNegSuc m ≡ (depConstrGZPos 0) +GZ (depConstrGZNegSuc m)}
                          refl
                          (λ m Pm → ιGZNegSuc
                                       (λ _ → GZ)
                                       (λ _ → isSetGZ)
                                       (λ n → Nat.elim
                                         (depConstrGZNegSuc zero)
                                         (λ m _ → depConstrGZPos m)
                                         n)
                                       (λ n → depConstrGZNegSuc (suc n))
                                       m
                                       (λ s → s ≡ (depConstrGZPos 0) +GZ (depConstrGZNegSuc (suc m))) --need to iota for +GZ and predGZ separately
                                       (ιGZNegSuc⁻
                                         (λ _ → GZ)
                                         (λ _ → isSetGZ)
                                         (λ p → depConstrGZPos 0 +posGZ p)
                                         (λ p → depConstrGZPos 0 +negsucGZ p)
                                         (suc m)
                                         (λ s → depElimGZ
                                                  (λ _ → GZ)
                                                  (λ _ → isSetGZ)
                                                  (λ n → Nat.elim
                                                    (depConstrGZNegSuc zero)
                                                    (λ m _ → depConstrGZPos m)
                                                    n)
                                                  (λ n → depConstrGZNegSuc (suc n))
                                                  (depConstrGZNegSuc m)
                                                 ≡ s)
                                         (ιGZNegSuc
                                           (λ _ → GZ)
                                           (λ _ → isSetGZ)
                                           (λ p → depConstrGZPos 0 +posGZ p)
                                           (λ p → depConstrGZPos 0 +negsucGZ p)
                                           m
                                           (λ s → depElimGZ
                                                    (λ _ → GZ)
                                                    (λ _ → isSetGZ)
                                                    (λ n → Nat.elim
                                                      (depConstrGZNegSuc zero)
                                                      (λ m _ → depConstrGZPos m)
                                                      n)
                                                    (λ n → depConstrGZNegSuc (suc n))
                                                    (depConstrGZNegSuc m)
                                                   ≡ predGZ s)
                                           (cong predGZ Pm))))
                          n)
                z

addHelpFunc' : (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ)
addHelpFunc' (n1 , n2) (m1 , m2) = (n1 + m1 , n2 + m2)

open import Cubical.Data.Vec.Base
open import Cubical.Data.FinData
open import Cubical.Tactics.NatSolver.NatExpression
open import Cubical.Tactics.NatSolver.HornerForms
open import Cubical.Tactics.NatSolver.Solver
open import Cubical.Tactics.NatSolver.Reflection

open EqualityToNormalform renaming (solve to natSolve)
open IteratedHornerOperations hiding (X)

varType = IteratedHornerForms 8
var0 : varType
var0 = Variable 8 (Fin.zero)

var1 : varType
var1 = Variable 8 (suc Fin.zero)

var2 : varType
var2 = Variable 8 (suc (suc Fin.zero))

var3 : varType
var3 = Variable 8 (suc (suc (suc Fin.zero)))

var4 : varType
var4 = Variable 8 (suc (suc (suc (suc Fin.zero))))

var5 : varType
var5 = Variable 8 (suc (suc (suc (suc (suc Fin.zero)))))

var6 : varType
var6 = Variable 8 (suc (suc (suc (suc (suc (suc Fin.zero))))))

var7 : varType
var7 = Variable 8 (suc (suc (suc (suc (suc (suc (suc Fin.zero)))))))

A1 : Expr 8
A1 = ∣ Fin.zero

A2 : Expr 8
A2 = ∣ (suc Fin.zero)

A1' : Expr 8
A1' = ∣ (suc (suc Fin.zero))

A2' : Expr 8
A2' = ∣ (suc (suc (suc Fin.zero)))

B1 : Expr 8
B1 = ∣ (suc (suc (suc (suc Fin.zero))))

B2 : Expr 8
B2 = ∣ (suc (suc (suc (suc (suc Fin.zero)))))

B1' : Expr 8
B1' = ∣ (suc (suc (suc (suc (suc (suc Fin.zero))))))

B2' : Expr 8
B2' = ∣ (suc (suc (suc (suc (suc (suc (suc Fin.zero)))))))

add'Resp : (a a' b b' : ℕ × ℕ) → R a a' → R b b' → R (addHelpFunc' a b) (addHelpFunc' a' b')
add'Resp (a1 , a2) (a1' , a2') (b1 , b2) (b1' , b2') ra rb = inj-m+ {m = a2 + a1'} (inj-m+ {m = b2 + b1'} (subst2 (λ x y →  b2 + b1' + (a2 + a1' + (a1 + b1 + (a2' + b2'))) ≡
      y + (x + (a2 + b2 + (a1' + b1')))) ra rb let
                                                 lhs = B2 +' B1' +' (A2 +' A1' +' (A1 +' B1 +' (A2' +' B2'))) 
                                                 rhs = B1 +' B2' +' (A1 +' A2' +' (A2 +' B2 +' (A1' +' B1')))
                                                 in natSolve lhs rhs (a1 ∷ a2 ∷ a1' ∷ a2' ∷ b1 ∷ b2 ∷ b1' ∷ b2' ∷ []) refl))

addGZ' : GZ → GZ → GZ
addGZ' = setQuotBinOp isReflR isReflR addHelpFunc' add'Resp

addGZ'0R : (x : GZ) → addGZ' x [ 0 , 0 ] ≡ x
addGZ'0R x =
  depElimGZ
    (λ x → addGZ' x [ 0 , 0 ] ≡ x)
    (λ x → isProp→isSet (isSetGZ _ _))
    (λ n → cong (λ m → [ m , 0 ]) (+-zero n))
    (λ n → cong (λ m → [ 0 , suc m ]) (+-zero n))
    x

addGZ'NegSuc0R : (x : GZ) → addGZ' x (depConstrGZNegSuc 0) ≡ predGZ x
addGZ'NegSuc0R x =
  depElimGZ
    (λ x → addGZ' x (depConstrGZNegSuc 0) ≡ predGZ x)
    (λ x → isProp→isSet (isSetGZ _ _))
    (λ n → Nat.elim
              {A = λ n → addGZ' (depConstrGZPos n) (depConstrGZNegSuc 0) ≡ predGZ (depConstrGZPos n)}
              refl
              (λ k Pk → eq/ (suc (k + 0) , 1) (k , 0) (cong ℕ.suc (((+-zero (k + 0)) ∙ (+-zero k)))))
              n)
    (λ n → cong (λ m → [_] {R = R} (0 , m)) (cong ℕ.suc (+-suc n 0 ∙ cong ℕ.suc (+-zero n))))
    x

add+GZ0R : (x : GZ) → x ≡ x +GZ (depConstrGZPos zero)
add+GZ0R x =
  depElimGZ
    (λ x → x ≡ x +GZ (depConstrGZPos zero))
    (λ x → isProp→isSet (isSetGZ _ _))
    (λ n → refl)
    (λ n → refl)
    x

add+GZNegSuc0R : (x : GZ) → predGZ x ≡ x +GZ (depConstrGZNegSuc zero)
add+GZNegSuc0R x =
  depElimGZ
    (λ x → predGZ x ≡ x +GZ (depConstrGZNegSuc zero))
    (λ x → isProp→isSet (isSetGZ _ _))
    (λ n → Nat.elim
      {A = λ m → predGZ (depConstrGZPos m) ≡ depConstrGZPos m +GZ (depConstrGZNegSuc zero)}
      refl
      (λ k _ → refl)
      n)
    (λ n → Nat.elim
      {A = λ m → predGZ (depConstrGZNegSuc m) ≡ depConstrGZNegSuc m +GZ (depConstrGZNegSuc zero)}
      refl
      (λ k _ → refl)
      n)
    x

reduce+GZPosR : (x : GZ) (n : ℕ) → sucGZ (x +GZ depConstrGZPos n) ≡ x +GZ depConstrGZPos (suc n)
reduce+GZPosR x n =
  ιGZPos⁻
    (λ _ → GZ)
    (λ _ → isSetGZ)
    (λ p → x +posGZ p)
    (λ p → x +negsucGZ p)
    n
    (λ s → sucGZ s ≡ x +GZ (depConstrGZPos (suc n)))
    (ιGZPos
      (λ _ → GZ)
      (λ _ → isSetGZ)
      (λ p → x +posGZ p)
      (λ p → x +negsucGZ p)
      (suc n)
      (λ s → s ≡ x +GZ (depConstrGZPos (suc n)))
      refl)

reduce+GZNegSucR : (x : GZ) (n : ℕ) → predGZ (x +GZ depConstrGZNegSuc n) ≡ x +GZ depConstrGZNegSuc (suc n)
reduce+GZNegSucR x n =
  ιGZNegSuc⁻
    (λ _ → GZ)
    (λ _ → isSetGZ)
    (λ p → x +posGZ p)
    (λ p → x +negsucGZ p)
    n
    (λ s → predGZ s ≡ x +GZ (depConstrGZNegSuc (suc n)))
    (ιGZNegSuc
      (λ _ → GZ)
      (λ _ → isSetGZ)
      (λ p → x +posGZ p)
      (λ p → x +negsucGZ p)
      (suc n)
      (λ s → s ≡ x +GZ (depConstrGZNegSuc (suc n)))
      refl)

reduceSucGZDepConstrPos : (n : ℕ) → depConstrGZPos (suc n) ≡ sucGZ (depConstrGZPos n)
reduceSucGZDepConstrPos n =
  ιGZPos
    (λ _ → GZ)
    (λ _ → isSetGZ)
    (λ n → depConstrGZPos (suc n))
    (λ n → Nat.elim
      (depConstrGZPos zero)
      (λ m _ → depConstrGZNegSuc m )
      n)
    n
    (λ s → s ≡ sucGZ (depConstrGZPos n))
    refl

reduceSucGZDepConstrNegSuc : (n : ℕ) → depConstrGZNegSuc n ≡ sucGZ (depConstrGZNegSuc (suc n))
reduceSucGZDepConstrNegSuc n =
  ιGZNegSuc
    (λ _ → GZ)
    (λ _ → isSetGZ)
    (λ n → depConstrGZPos (suc n))
    (λ n → Nat.elim
      (depConstrGZPos zero)
      (λ m _ → depConstrGZNegSuc m )
      n)
    (suc n)
    (λ s → s ≡ sucGZ (depConstrGZNegSuc (suc n)))
    refl

natEq0Dec : (x : ℕ) → (x ≡ 0) ⊎ (Σ[ y ∈ ℕ ] x ≡ suc y)
natEq0Dec zero = inl refl
natEq0Dec (suc x) = inr (x , refl)

reduceSucGZ : (n m : ℕ) → [ suc n , m ] ≡ sucGZ [ n , m ]
reduceSucGZ n m =
  Sum.rec
    (λ x → subst
      (λ y → [ suc n , m ] ≡ sucGZ [ y ])
      (sym (snd x))
      (eq/ _ _ (cong
        ℕ.suc
        (effective
          Rprop
          REquivRel
          (n , m)
          (fst x , 0)
          (canonicalizePres (n , m) ∙ cong [_] (snd x))) ∙ (sym (+-suc m (fst x)))) ∙ reduceSucGZDepConstrPos (fst x))
      ∙ (sym (cong sucGZ (canonicalizePres (n , m)))))
    (λ x → let
      v = fst x
      canonicalEq = proj₁ (snd x)
      pv = fst (proj₂ (snd x))
      pvEq = snd (proj₂ (snd x)) in 
      (subst
        (λ y → [ suc n , m ] ≡ sucGZ [ y ])
        (sym canonicalEq)
        (subst
          (λ y → [ suc n , m ] ≡ sucGZ [ zero , y ])
          (sym pvEq)
          (Sum.rec
            (λ pvEq0 → subst
              (λ y → [ suc n , m ] ≡ sucGZ [ zero , suc y ])
              (sym pvEq0)
              (eq/
                _
                _
                (sym (+-suc n 0)
                ∙ subst
                    (λ y → (n + y) ≡ m + zero)
                    (pvEq ∙ cong suc pvEq0)
                    (effective
                      Rprop
                      REquivRel
                      (n , m)
                      (0 , v)
                      (canonicalizePres (n , m) ∙ cong [_] canonicalEq)))))
            (λ pvEqSuc → subst
              (λ y → [ suc n , m ] ≡ sucGZ [ zero , suc y ])
              (sym (snd pvEqSuc))
              (eq/
                _
                _
                (sym (+-suc n (suc (fst pvEqSuc)))
                ∙ subst
                    (λ y → n + y ≡ m + 0)
                    (pvEq ∙ (cong suc (snd pvEqSuc)))
                    (effective
                      Rprop
                      REquivRel
                      (n , m)
                      (0 , v)
                      ((canonicalizePres (n , m) ∙ cong [_] canonicalEq))))
              ∙ reduceSucGZDepConstrNegSuc (fst pvEqSuc)))
            (natEq0Dec pv))))
      ∙ (sym (cong sucGZ (canonicalizePres (n , m)))))
    (canonicalizeSignDec (n , m))

reduceAddGZ'Pos : (x : GZ) (n : ℕ) → addGZ' x (depConstrGZPos (suc n)) ≡ sucGZ (addGZ' x (depConstrGZPos n))
reduceAddGZ'Pos x n =
  depElimGZ
    (λ x → addGZ' x (depConstrGZPos (suc n)) ≡ sucGZ (addGZ' x (depConstrGZPos n)))
    (λ x → isProp→isSet (isSetGZ _ _))
    (λ m → cong (λ k → [ k , 0 ]) (+-suc m n) ∙ (reduceSucGZ (m + n) 0))
    (λ m → reduceSucGZ n (suc (m + 0)))
    x

reducePredGZDepConstrPos : (n : ℕ) → depConstrGZPos n ≡ predGZ (depConstrGZPos (suc n))
reducePredGZDepConstrPos n =
  ιGZPos
    (λ _ → GZ)
    (λ _ → isSetGZ)
    (λ n → Nat.elim
      (depConstrGZNegSuc zero)
      (λ m _ → depConstrGZPos m)
      n)
    (λ n → depConstrGZNegSuc (suc n))
    (suc n)
    (λ s → s ≡ predGZ (depConstrGZPos (suc n)))
    refl

reducePredGZDepConstrNegSuc : (n : ℕ) → depConstrGZNegSuc (suc n) ≡ predGZ (depConstrGZNegSuc n)
reducePredGZDepConstrNegSuc n =
  ιGZNegSuc
    (λ _ → GZ)
    (λ _ → isSetGZ)
    (λ n → Nat.elim
      (depConstrGZNegSuc zero)
      (λ m _ → depConstrGZPos m)
      n)
    (λ n → depConstrGZNegSuc (suc n))
    n
    (λ s → s ≡ predGZ (depConstrGZNegSuc n))
    refl

reducePredGZ : (n m : ℕ) → [ n , suc m ] ≡ predGZ [ n , m ]
reducePredGZ n m =
  Sum.rec
    (λ x → let
      v = fst x
      canonicalEq = snd x in
      subst
        (λ y → [ n , suc m ] ≡ predGZ [ y ])
        (sym canonicalEq)
        (Sum.rec
          (λ vEq0 → subst
            (λ y → [ n , suc m ] ≡ predGZ [ y , zero ])
            (sym vEq0)
            (eq/
              (n , suc m)
              (0 , suc zero)
              (+-suc n zero
              ∙ cong
                  ℕ.suc
                  (subst
                    (λ y → n + zero ≡ m + y)
                    vEq0
                    (effective
                      Rprop
                      REquivRel
                      (n , m)
                      (fst x , 0)
                      (canonicalizePres (n , m) ∙ cong [_] canonicalEq))))))
          (λ vEqSuc → subst
            (λ y → [ n , suc m ] ≡ predGZ [ y , zero ])
            (sym (snd vEqSuc))
            (eq/
              (n , suc m)
              (fst vEqSuc , 0)
              (subst (λ y → n + 0 ≡ m + y)
                (snd vEqSuc)
                (effective
                  Rprop
                  REquivRel
                  (n , m)
                  (v , 0)
                  (canonicalizePres (n , m) ∙ cong [_] canonicalEq))
              ∙ +-suc m (fst vEqSuc))
            ∙ reducePredGZDepConstrPos (fst vEqSuc)))
          (natEq0Dec v))
      ∙ (cong predGZ (sym (canonicalizePres (n , m)))))
    (λ x → let
      v = fst x
      canonicalEq = proj₁ (snd x)
      pv = fst (proj₂ (snd x ))
      pvEq = snd (proj₂ (snd x)) in
      subst
        (λ y → [ n , suc m ] ≡ predGZ [ y ])
        (sym canonicalEq)
        (subst
          (λ y → [ n , suc m ] ≡ predGZ [ zero , y ])
          (sym pvEq)
          (eq/
            (n , suc m)
            (0 , suc (suc pv))
            (+-suc n (suc pv)
            ∙ cong
                ℕ.suc
                (effective
                  Rprop
                  REquivRel
                  (n , m)
                  (0 , suc pv)
                  (subst
                    (λ y → [_] {R = R} (n , m) ≡ [ 0 , y ])
                    pvEq
                    (canonicalizePres (n , m) ∙ cong [_] canonicalEq))))
          ∙ reducePredGZDepConstrNegSuc pv))
      ∙ (cong predGZ (sym (canonicalizePres (n , m)))))
    (canonicalizeSignDec (n , m))

reduceAddGZ'NegSuc : (x : GZ) (n : ℕ) → addGZ' x (depConstrGZNegSuc (suc n)) ≡ predGZ (addGZ' x (depConstrGZNegSuc n))
reduceAddGZ'NegSuc x n =
  depElimGZ
    (λ x → addGZ' x (depConstrGZNegSuc (suc n)) ≡ predGZ (addGZ' x (depConstrGZNegSuc n)))
    (λ x → isProp→isSet (isSetGZ _ _))
    (λ m → reducePredGZ (m + 0) (suc n))
    (λ m → cong (λ k → [ 0 , suc k ]) (+-suc m (suc n)) ∙ reducePredGZ 0 (suc m + suc n))
    x

addEqualOnInputs : (x y : GZ) → addGZ' x y ≡ x +GZ y
addEqualOnInputs x y =
  depElimGZ
    (λ z → addGZ' x z ≡ x +GZ z)
    (λ y → isProp→isSet (isSetGZ _ _))
    (λ m → Nat.elim
      {A = λ m → addGZ' x (depConstrGZPos m) ≡ x +GZ (depConstrGZPos m)} 
      (addGZ'0R x ∙ add+GZ0R x)
      (λ k Pk → reduceAddGZ'Pos x k ∙ cong sucGZ Pk ∙ reduce+GZPosR x k)
      m)
    (λ m → Nat.elim
      {A = λ m → addGZ' x (depConstrGZNegSuc m) ≡ x +GZ (depConstrGZNegSuc m)}
      (addGZ'NegSuc0R x ∙ add+GZNegSuc0R x)
      (λ k Pk → (reduceAddGZ'NegSuc x k) ∙ (cong predGZ Pk) ∙ reduce+GZNegSucR x k)
      m)
    y

addEqual : addGZ' ≡ _+GZ_
addEqual = funExt (λ x → funExt (λ y → addEqualOnInputs x y))

add'0LGZ : (z : GZ) → z ≡ addGZ' (depConstrGZPos 0) z
add'0LGZ = subst (λ y → (z : GZ) → z ≡ y (depConstrGZPos 0) z) (sym addEqual) add0LGZ

-- Copying in proof that ℤ is a set from the standard library.
injPos : ∀ {a b : ℕ} → pos a ≡ pos b → a ≡ b
injPos {a} h = subst T h refl
  where
  T : ℤ → Type₀
  T (pos x)    = a ≡ x
  T (negsuc _) = ⊥

injNegsuc : ∀ {a b : ℕ} → negsuc a ≡ negsuc b → a ≡ b
injNegsuc {a} h = subst T h refl
  where
  T : ℤ → Type₀
  T (pos _) = ⊥
  T (negsuc x) = a ≡ x

posNotnegsuc : ∀ (a b : ℕ) → ¬ (pos a ≡ negsuc b)
posNotnegsuc a b h = subst T h 0
  where
  T : ℤ → Type₀
  T (pos _)    = ℕ
  T (negsuc _) = ⊥

negsucNotpos : ∀ (a b : ℕ) → ¬ (negsuc a ≡ pos b)
negsucNotpos a b h = subst T h 0
  where
  T : ℤ → Type₀
  T (pos _)    = ⊥
  T (negsuc _) = ℕ

discreteℤ : Discrete ℤ
discreteℤ (pos n) (pos m) with discreteℕ n m
... | yes p = yes (cong pos p)
... | no p  = no (λ x → p (injPos x))
discreteℤ (pos n) (negsuc m) = no (posNotnegsuc n m)
discreteℤ (negsuc n) (pos m) = no (negsucNotpos n m)
discreteℤ (negsuc n) (negsuc m) with discreteℕ n m
... | yes p = yes (cong negsuc p)
... | no p  = no (λ x → p (injNegsuc x))

isSetℤ : isSet ℤ
isSetℤ = Discrete→isSet discreteℤ

ℤ≡GZ : ℤ ≡ GZ
ℤ≡GZ = isoToPath (iso f g sec ret) where
  f : ℤ → GZ
  f = depElimℤ (λ _ → GZ) depConstrGZPos depConstrGZNegSuc
  g : GZ → ℤ
  g = depElimGZ (λ _ → ℤ) (λ _ → isSetℤ) depConstrℤPos depConstrℤNegSuc
  sec : section f g
  sec =
    depElimGZ
      (λ x → f (g x) ≡ x)
      (λ x → isProp→isSet (squash/ _ _))
      (λ n → ιGZPos⁻
        (λ _ → ℤ)
        (λ _ → isSetℤ)
        depConstrℤPos
        depConstrℤNegSuc
        n
        (λ z → f z ≡ depConstrGZPos n)
        refl)
      λ n → ιGZNegSuc⁻
        (λ _ → ℤ)
        (λ _ → isSetℤ)
        depConstrℤPos
        depConstrℤNegSuc
        n
        (λ z → f z ≡ depConstrGZNegSuc n)
        refl
  ret : retract f g
  ret =
    depElimℤ
      (λ x → g (f x) ≡ x)
      (λ n → ιGZPos⁻
        (λ _ → ℤ)
        (λ _ → isSetℤ)
        depConstrℤPos
        depConstrℤNegSuc
        n
        (λ z → z ≡ depConstrℤPos n )
        refl)
      λ n → ιGZNegSuc⁻
        (λ _ → ℤ)
        (λ _ → isSetℤ)
        depConstrℤPos
        depConstrℤNegSuc
        n
        (λ z → z ≡ depConstrℤNegSuc n )
        refl
  
