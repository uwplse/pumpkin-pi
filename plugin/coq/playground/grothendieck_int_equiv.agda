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

depConstrIndZPos : ℕ → ℤ
depConstrIndZPos n = pos n

depConstrIndZNegSuc : ℕ → ℤ
depConstrIndZNegSuc n = negsuc n

depElimIndZ : (P : ℤ → Set) → (∀ n → P (depConstrIndZPos n)) → (∀ n → P (depConstrIndZNegSuc n)) → ∀ z → P z
depElimIndZ P posP negP (pos n) = posP n
depElimIndZ P posP negsucP (negsuc n) = negsucP n

ιIndZPos : (P : ℤ → Set) → (posP : (n : ℕ) → P (depConstrIndZPos n)) → (negSucP : (n : ℕ) → P (depConstrIndZNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrIndZPos n) → Set) → Q (depElimIndZ P posP negSucP (depConstrIndZPos n)) → Q (posP n)
ιIndZPos P posP negSucP n Q Qp = Qp

ιIndZNegSuc : (P : ℤ → Set) → (posP : (n : ℕ) → P (depConstrIndZPos n)) → (negSucP : (n : ℕ) → P (depConstrIndZNegSuc n)) → (n : ℕ) →
    (Q : P (depConstrIndZNegSuc n) → Set) → Q (depElimIndZ P posP negSucP (depConstrIndZNegSuc n)) → Q (negSucP n)
ιIndZNegSuc P posP negSucP n Q Qp = Qp

-- Addition on integers, based on standard library functions.
sucℤ : ℤ → ℤ
sucℤ z = depElimIndZ
           (λ _ → ℤ)
           (λ n → depConstrIndZPos (suc n))
           (λ n → Nat.elim
             (depConstrIndZPos zero)
             (λ m _ → depConstrIndZNegSuc m )
             n)
           z

predℤ : ℤ → ℤ
predℤ z = depElimIndZ
            (λ _ → ℤ)
            (λ n → Nat.elim
              (depConstrIndZNegSuc zero)
              (λ m _ → depConstrIndZPos m)
              n)
            (λ n → depConstrIndZNegSuc (suc n))
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
m +ℤ n = depElimIndZ
          (λ _ → ℤ)
          (λ p → m +pos p)
          (λ p → m +negsuc p)
          n

add0LIndZ : (z : ℤ) → z ≡ (depConstrIndZPos 0) +ℤ z
add0LIndZ z = depElimIndZ
                (λ z → z ≡ (depConstrIndZPos 0) +ℤ z)
                (λ n → Nat.elim {A = λ m → depConstrIndZPos m ≡ (depConstrIndZPos 0) +ℤ (depConstrIndZPos m)} refl (λ m Pm → cong sucℤ Pm) n)
                (λ n → Nat.elim {A = λ m → depConstrIndZNegSuc m ≡ (depConstrIndZPos 0) +ℤ (depConstrIndZNegSuc m)} refl (λ m Pm → cong predℤ Pm) n)
                z

-- grothendieck group construction of ℤ

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

-- there is probably a better way to do this
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

canonicalizeSignDecCanonicalType : (p : ℕ × ℕ) → (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize p ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ≡ (Σ[ n ∈ ℕ ] (canonicalize (canonicalize p) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize (canonicalize p) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m))))
canonicalizeSignDecCanonicalType p = subst (λ x → (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize p ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ≡ (Σ[ n ∈ ℕ ] (x ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((x ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m))))) (canonicalizeIdempotent p) refl

isSetProd : {A B : Set} → isSet A → isSet B → isSet (A × B)
isSetProd {A} {B} setA setB = isOfHLevelProd 2 setA setB

isSetℕ×ℕ : isSet (ℕ × ℕ)
isSetℕ×ℕ = isSetProd isSetℕ isSetℕ

isSetCanonicalizeSignDecCanonicalType : (p : ℕ × ℕ) → isSet ((Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize p ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))))
isSetCanonicalizeSignDecCanonicalType p = isSet⊎ (isSetΣ isSetℕ (λ n → isProp→isSet (isSetℕ×ℕ (canonicalize p) ((n , zero)))))
                                                 (isSetΣ isSetℕ (λ n → isSetProd (isProp→isSet (isSetℕ×ℕ (canonicalize p) (zero , n)))
                                                                                 (isSetΣ isSetℕ (λ x → isProp→isSet (isSetℕ n (suc x))))))

canonicalizeSignDecCanonicalLeftFst : (p : ℕ × ℕ) → (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ≡ (Σ[ n ∈ ℕ ] (canonicalize (canonicalize p) ≡ (n , zero)))
canonicalizeSignDecCanonicalLeftFst p = subst (λ x → (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ≡ (Σ[ n ∈ ℕ ] (x ≡ (n , zero)))) (canonicalizeIdempotent p) refl

-- idea: construct a PathP from canonicalizeSignDec p to canonicalizeSignDec (canonicalize p), then transport across it 

canonicalizeSignDecCanonical : (p : ℕ × ℕ) → PathP (λ i → canonicalizeSignDecCanonicalType p i) (canonicalizeSignDec p) (canonicalizeSignDec (canonicalize p))
canonicalizeSignDecCanonical (zero , p2) = subst (λ x → PathP (λ i → x i) (canonicalizeSignDec (zero , p2)) (canonicalizeSignDec (canonicalize (zero , p2)))) (lem p2) refl where
  pathPLem : (p2 : ℕ) → PathP (λ i → (Σ[ n ∈ ℕ ] (canonicalize (zero , p2) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize (zero , p2) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ≡ (Σ[ n ∈ ℕ ] ((refl i) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] (((refl {x = (zero , p2)} i) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m))))) refl (canonicalizeSignDecCanonicalType (zero , p2))
  pathPLem p2 = subst-filler ((λ x → (Σ[ n ∈ ℕ ] (canonicalize (zero , p2) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize (zero , p2) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ≡ (Σ[ n ∈ ℕ ] (x ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((x ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))))) refl refl
  lem : (p2 : ℕ) → refl ≡ canonicalizeSignDecCanonicalType (zero , p2)
  lem = pathPLem
canonicalizeSignDecCanonical (suc p1 , zero) = subst (λ x → PathP (λ i → x i) (canonicalizeSignDec (suc p1 , zero)) (canonicalizeSignDec (canonicalize (suc p1 , zero)))) (lem p1) refl where
  pathPLem : (p1 : ℕ) → PathP (λ i → (Σ[ n ∈ ℕ ] (canonicalize (suc p1 , zero) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize (suc p1 , zero) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ≡ (Σ[ n ∈ ℕ ] ((refl i) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((((refl {x = (suc p1 , zero)} i)) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m))))) refl (canonicalizeSignDecCanonicalType (suc p1 , zero))
  pathPLem p1 = subst-filler ((λ x → (Σ[ n ∈ ℕ ] (canonicalize (suc p1 , zero) ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((canonicalize (suc p1 , zero) ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))) ≡ (Σ[ n ∈ ℕ ] (x ≡ (n , zero))) ⊎ (Σ[ n ∈ ℕ ] ((x ≡ (zero , n)) × (Σ[ m ∈ ℕ ] (n ≡ suc m)))))) refl refl
  lem : (p1 : ℕ) → refl ≡ canonicalizeSignDecCanonicalType (suc p1 , zero)
  lem = pathPLem
canonicalizeSignDecCanonical (suc p1 , suc p2) = canonicalizeSignDecCanonical (p1 , p2)

-- canonicalizeSignDecCanonicalLeft : (p : ℕ × ℕ) → (Σ[ y ∈ (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ] (canonicalizeSignDec p ≡ inl y)) ≡ (Σ[ y ∈ (Σ[ n ∈ ℕ ] (canonicalize (canonicalize p) ≡ (n , zero))) ] (canonicalizeSignDec (canonicalize p) ≡ inl y))
-- canonicalizeSignDecCanonicalLeft p = Σ-cong' (canonicalizeSignDecCanonicalLeftFst p) ({!!})

canonicalizeSignDecCanonicalLeft' : (p : ℕ × ℕ) → (Σ[ y ∈ (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ] (canonicalizeSignDec p ≡ inl y)) → (Σ[ y ∈ (Σ[ n ∈ ℕ ] (canonicalize (canonicalize p) ≡ (n , zero))) ] (canonicalizeSignDec (canonicalize p) ≡ inl y))
canonicalizeSignDecCanonicalLeft' p ((zero , s12) , s2) = subst (λ x → Σ-syntax (Σ-syntax ℕ
                                                                                          (λ n → canonicalize x ≡ (n , zero)))
                                                                                          (λ y → canonicalizeSignDec x ≡ inl y))
                                                                                (sym s12)
                                                                                ((zero , canonicalizeRZ zero) , refl)
canonicalizeSignDecCanonicalLeft' p ((suc s11 , s12) , s2) = subst (λ x → Σ-syntax (Σ-syntax ℕ
                                                                                             (λ n → canonicalize x ≡ (n , zero)))
                                                                                             (λ y → canonicalizeSignDec x ≡ inl y))
                                                                                   (sym s12)
                                                                                   (((suc s11) , refl) , refl)

sumRememberEq : {A B : Set} → (x : A ⊎ B) → (Σ[ a ∈ A ] x ≡ inl a) ⊎ (Σ[ b ∈ B ] x ≡ inr b)
sumRememberEq (inl x) = inl (x , refl)
sumRememberEq (inr x) = inr (x , refl)

open BinaryRelation

Rrefl : {x : ℕ × ℕ} → R x x
Rrefl {x1 , x2} = Nat.+-comm x1 x2

-- 
-- isSetProd : {A B : Set} → isSet A → isSet B → isSet (A × B)
-- isSetProd {A} {B} setA setB = isOfHLevelProd 2 setA setB
-- 
-- Rprop : isPropValued R
-- Rprop (a1 , a2) (b1 , b2) p1 p2 = isSetℕ (a1 Nat.+ b2) (a2 Nat.+ b1) p1 p2
-- 
-- 
isReflR : isRefl R
isReflR x = Rrefl
-- 
-- isSymR : isSym R
-- isSymR (x1 , x2) (y1 , y2) r = (Nat.+-comm y1 x2) ∙ (sym r) ∙ (Nat.+-comm x1 y2)
-- 
-- isTransR : isTrans R
-- isTransR (x1 , x2) (y1 , y2) (z1 , z2) r1 r2 = {!!}
-- 
-- REquivRel : isEquivRel R
-- REquivRel = equivRel isReflR {!!} {!!}
-- 
-- rFromPath : {a b : ℕ × ℕ } → [ a ] ≡ [ b ] → R a b
-- rFromPath {a} {b} p = effective Rprop REquivRel a b p
--

--R : (ℕ × ℕ) → (ℕ × ℕ) → Type
--R (x1 , x2) (y1 , y2) = x1 Nat.+ y2 ≡ x2 Nat.+ y1

RIrrel : ∀ x1 x2 (p : x1 Nat.+ x2 ≡ x2 Nat.+ x1) → p ≡ Rrefl {x1 , x2}
RIrrel x1 x2 p = isSetℕ _ _ p (Rrefl {x1 , x2})

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

addHelpFunc : (ℕ × ℕ) → (ℕ × ℕ) → GZ
addHelpFunc (n1 , n2) (m1 , m2) = [ n1 + m1 , n2 + m2 ]

addHelpRespLem : (n1 n2 a1 a2 b1 b2 : ℕ) → (r : R (a1 , a2) (b1 , b2)) → n1 + a1 + (n2 + b2) ≡ n2 + a2 + (n1 + b1)
addHelpRespLem n1 n2 a1 a2 b1 b2 r = (+-comm (n1 + a1) (n2 + b2))
                                     ∙ sym (+-assoc n2 b2 (n1 + a1))
                                     ∙ cong
                                         (λ x → n2 + x)
                                         ((+-comm b2 (n1 + a1))
                                           ∙ ((sym (+-assoc n1 a1 b2))
                                           ∙ (((cong
                                               (λ x → n1 + x)
                                               (r
                                               ∙ (+-comm a2 b1)))
                                           ∙ (+-assoc n1 b1 a2))
                                           ∙ (sym (+-comm a2 (n1 + b1))))))
                                       ∙ +-assoc n2 a2 (n1 + b1)

addHelpResp : (n a b : ℕ × ℕ) (r : R a b) → addHelpFunc n a ≡ addHelpFunc n b
addHelpResp (n1 , n2) (a1 , a2) (b1 , b2) r = eq/ (n1 + a1 , n2 + a2) (n1 + b1 , n2 + b2) (addHelpRespLem n1 n2 a1 a2 b1 b2 r)

addHelp : GZ → (ℕ × ℕ) → GZ
addHelp z (n1 , n2) = SetQuotients.rec isSetGZ (addHelpFunc (n1 , n2)) (addHelpResp (n1 , n2)) z

lem : (a b : ℕ × ℕ) (r : R a b) → addHelpFunc a ≡ addHelpFunc b
lem a b r = funExt λ x → lem2 a b x r where
  lem2 : (a b n : ℕ × ℕ) (r : R a b) → addHelpFunc a n ≡ addHelpFunc b n
  lem2 (a1 , a2) (b1 , b2) (n1 , n2) r = eq/ (a1 + n1 , a2 + n2) (b1 + n1 , b2 + n2) (lem3 a1 a2 b1 b2 n1 n2 r) where
    lem3 : (a1 a2 b1 b2 n1 n2 : ℕ) (r : R (a1 , a2) (b1 , b2)) → a1 + n1 + (b2 + n2) ≡ a2 + n2 + (b1 + n1)
    lem3 a1 a2 b1 b2 n1 n2 r = {!!} --- this won't be hard, focusing on the rest first

--- try using this for lem4?
lem5 : (a b c : ℕ × ℕ) (r : R a b) (r2 : R c c) → PathP (λ i → (lem a b r i) c ≡ (lem a b r i) c) (addHelpResp a c c r2) (addHelpResp b c c r2)
lem5 a b c r r2 = subst2 (λ x y → PathP (λ i → lem a b r i c ≡ lem a b r i c) x y) (squash/ _ _ _ _) (squash/ _ _ _ _) lem10 where
  lem10 : PathP (λ i → lem a b r i c ≡ lem a b r i c) refl refl
  lem10 i = refl

lem8 : (a c d : ℕ × ℕ) (r : R c c) (r2 : R c d) → PathP (λ i → addHelpFunc a c ≡ (refl ∙ addHelpResp a c d r2) i) (addHelpResp a c c r) (addHelpResp a c d r2)
lem8 (a1 , a2) (c1 , c2) (d1 , d2) r r2 =
  compPathP'
    {B = λ x → addHelpFunc (a1 , a2) (c1 , c2) ≡ x}
    (squash/ [ a1 + c1 , a2 + c2 ] [ a1 + c1 , a2 + c2 ] (addHelpResp (a1 , a2) (c1 , c2) (c1 , c2) r) refl)
    λ i j → addHelpResp (a1 , a2) (c1 , c2) (d1 , d2) r2 (i ∧ j)

lem6 : (a c d : ℕ × ℕ) (r : R c c) (r2 : R c d) → PathP (λ i → addHelpFunc a c ≡ addHelpResp a c d r2 i) (addHelpResp a c c r) (addHelpResp a c d r2)
lem6 a c d r r2 =
  subst (λ x → PathP (λ i → addHelpFunc a c ≡ x i) (addHelpResp a c c r) (addHelpResp a c d r2)) (sym (lUnit (addHelpResp a c d r2))) (lem8 a c d r r2)

lem7 : (a b c d : ℕ × ℕ) (r : R a b) (r2 : R c d) → PathP (λ i → (sym (λ i → addHelpFunc a c ≡ addHelpResp a c d r2 i) ∙ ((λ i → (lem a b r i) c ≡ (lem a b r i) c) ∙ λ i → addHelpFunc b c ≡ addHelpResp b c d r2 i)) i) (addHelpResp a c d r2) (addHelpResp b c d r2)
lem7 a b c d r r2 =
  compPathP
  (symP (lem6 a c d Rrefl r2))
  (compPathP
    (lem5 a b c r Rrefl)
    (lem6 b c d Rrefl r2))

lem4 : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → (c d : ℕ × ℕ) (r2 : R c d) → (lem a b r i) c ≡ (lem a b r i) d) (addHelpResp a) (addHelpResp b)
lem4 a b r =
  funExt
    λ c → funExt
      (λ d → funExt
        λ r2 → subst
         ((λ x → PathP (λ i → x i) (addHelpResp a c d r2) (addHelpResp b c d r2)))
         (lem9 a b c d r r2)
         (lem7 a b c d r r2)) where
    lem9 : (a b c d : ℕ × ℕ) (r : R a b) (r2 : R c d) → (sym (λ i → addHelpFunc a c ≡ addHelpResp a c d r2 i) ∙ ((λ i → (lem a b r i) c ≡ (lem a b r i) c) ∙ λ i → addHelpFunc b c ≡ addHelpResp b c d r2 i)) ≡ (λ i → (lem a b r i) c ≡ (lem a b r i) d)
    lem9 (a1 , a2) (b1 , b2) (c1 , c2) (d1 , d2) r r2 = lem11 _ _ where  --- ([a], [b]) ≡ ([a], [b]) is a singleton type; this is a path on a singleton type and hence is trivial
      lem11 : isProp (([ (a1 + c1) , (a2 + c2) ] ≡ [ (a1 + d1) , (a2 + d2) ]) ≡ ([ (b1 + c1) , (b2 + c2) ] ≡ [ (b1 + d1) , (b2 + d2) ]))
      lem11 p1 p2 = {!!}

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

_fastAddGZ_ : GZ → GZ → GZ
_fastAddGZ_ z1 z2 = SetQuotients.rec isSetGZ (addHelp z1) (resp z1) z2 where
  resp : (z : GZ) (a b : ℕ × ℕ) (r : R a b) → addHelp z a ≡ addHelp z b
  resp z (a1 , a2) (b1 , b2) r i = SetQuotients.rec isSetGZ (lem (a1 , a2) (b1 , b2) r i) (lem4 (a1 , a2) (b1 , b2) r i) z
  