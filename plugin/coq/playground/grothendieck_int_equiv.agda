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
open import Cubical.Data.Int
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.GroupoidLaws

-- dependand constructors/eliminators on standard library inductive ℤ

depConstrIndZPos : ℕ → ℤ
depConstrIndZPos n = pos n

depConstrIndZNegSuc : ℕ → ℤ
depConstrIndZNegSuc n = negsuc n

depElimIndZ : (P : ℤ → Set) → (∀ n → P (depConstrIndZPos n)) → (∀ n → P (depConstrIndZNegSuc n)) → ∀ z → P z
depElimIndZ P posP negP (pos n) = posP n
depElimIndZ P posP negsucP (negsuc n) = negsucP n

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

canonicalizeSignDecCanonicalLeft : (p : ℕ × ℕ) → (Σ[ y ∈ (Σ[ n ∈ ℕ ] (canonicalize p ≡ (n , zero))) ] (canonicalizeSignDec p ≡ inl y)) ≡ (Σ[ y ∈ (Σ[ n ∈ ℕ ] (canonicalize (canonicalize p) ≡ (n , zero))) ] (canonicalizeSignDec (canonicalize p) ≡ inl y))
canonicalizeSignDecCanonicalLeft p = Σ-cong' (canonicalizeSignDecCanonicalLeftFst p) ({!!})

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

-- open BinaryRelation
-- 
-- isSetProd : {A B : Set} → isSet A → isSet B → isSet (A × B)
-- isSetProd {A} {B} setA setB = isOfHLevelProd 2 setA setB
-- 
-- Rprop : isPropValued R
-- Rprop (a1 , a2) (b1 , b2) p1 p2 = isSetℕ (a1 Nat.+ b2) (a2 Nat.+ b1) p1 p2
-- 
-- 
-- isReflR : isRefl R
-- isReflR x = Rrefl
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

Rrefl : {x : ℕ × ℕ} → R x x
Rrefl {x1 , x2} = Nat.+-comm x1 x2

--R : (ℕ × ℕ) → (ℕ × ℕ) → Type
--R (x1 , x2) (y1 , y2) = x1 Nat.+ y2 ≡ x2 Nat.+ y1

RIrrel : ∀ x1 x2 (p : x1 Nat.+ x2 ≡ x2 Nat.+ x1) → p ≡ Rrefl {x1 , x2}
RIrrel x1 x2 p = isSetℕ _ _ p (Rrefl {x1 , x2})

JR : ∀ (x : ℕ × ℕ) (P : ∀ y → R x y → Set) →
  P x Rrefl →
  ∀ {y : ℕ × ℕ} (r : R x y) → P y r
-- going to start with an obviously inefficient proof, and then simplify after
JR (zero , zero) P d {zero , zero} r =
  subst {A = R (zero , zero) (zero , zero)} (λ d' → P (zero , zero) d') (sym (RIrrel zero zero r)) d
JR (zero , zero) P d {zero , suc y₂} r = Cubical.Data.Empty.rec (snotz r)
JR (zero , zero) P d {suc y₁ , zero} r = Cubical.Data.Empty.rec (snotz (sym r))
JR (zero , zero) P d {suc y₁ , suc y₂} r = {!!}
JR (zero , suc x₂) P d {zero , zero} r = Cubical.Data.Empty.rec (snotz (sym r))
JR (zero , suc x₂) P d {zero , suc y₂} r = {!!}
JR (zero , suc x₂) P d {suc y₁ , zero} r = Cubical.Data.Empty.rec (snotz (sym r))
JR (zero , suc x₂) P d {suc y₁ , suc y₂} r = {!!}
JR (suc x₁ , zero) P d {zero , zero} r = Cubical.Data.Empty.rec (snotz r)
JR (suc x₁ , zero) P d {zero , suc y₂} r = Cubical.Data.Empty.rec (snotz r)
JR (suc x₁ , zero) P d {suc y₁ , zero} r = {!!}
JR (suc x₁ , zero) P d {suc y₁ , suc y₂} r = {!!}
JR (suc x₁ , suc x₂) P d {zero , zero} r = {!!}
JR (suc x₁ , suc x₂) P d {zero , suc y₂} r = {!!}
JR (suc x₁ , suc x₂) P d {suc y₁ , zero} r = {!!}
JR (suc x₁ , suc x₂) P d {suc y₁ , suc y₂} r = {!!}

depElimGZNegSuc : (P : GZ → Set) → (∀ x → isSet (P x)) → (∀ n → P (depConstrGZPos n)) → (∀ n → P (depConstrGZNegSuc n)) → ∀ z → P z
depElimGZNegSuc P set posP negsucP = SetQuotients.elim set func resp where
  func : (p : ℕ × ℕ) → P [ p ]
  func p = Sum.rec (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (snd x) ∙ refl))))
                                    (posP (fst x)))
                   (λ x → transport (cong P (sym ([ p ] ≡⟨ canonicalizePres p ⟩ [ canonicalize p ]
                                                        ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
                                                        ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
                                    (negsucP (fst (proj₂ (snd x)))))
                   (canonicalizeSignDec p)
  funcLeft : (p : ℕ × ℕ) →
             (y : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize p ≡ (n , zero)) ] (canonicalizeSignDec p ≡ inl a)) →
             func p ≡ transport (cong P (sym ((canonicalizePres p) ∙ cong [_] (snd (fst y)) ∙ refl)))
                                (posP (fst (fst y)))
  funcLeft p y = subst (λ path → Sum.rec (λ x → transport (cong P (sym ((canonicalizePres p) ∙ (cong [_] (snd x) ∙ refl))))
                                                          (posP (fst x)))
                                         (λ x → transport (cong P (sym ([ p ] ≡⟨ canonicalizePres p ⟩ [ canonicalize p ]
                                                                              ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
                                                                              ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
                                                          (negsucP (fst (proj₂ (snd x)))))
                                         (path)
                                  ≡ transport (cong P (sym ((canonicalizePres p) ∙ cong [_] (snd (fst y)) ∙ refl)))
                                              (posP (fst (fst y))))
                       (sym (snd y))
                       refl
  lem3 : (p1 p2 : ℕ) →
         (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize (p1 , p2) ≡ (n , zero)) ] (canonicalizeSignDec (p1 , p2) ≡ inl a)) →
         PathP
          (λ i → sucRPres p1 p2 i ≡ [ (p1 , p2) ])          
          (sucRPres p1 p2)
          refl
  lem3 p1 p2 x = toPathP (squash/ [ p1 , p2 ] [ p1 , p2 ] _ refl)
  lem4 : (p1 p2 : ℕ) →
         (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize (p1 , p2) ≡ (n , zero)) ] (canonicalizeSignDec (p1 , p2) ≡ inl a)) →
          PathP
            (λ i → sucRPres p1 p2 i ≡ [ canonicalize (p1 , p2) ])
            (sucRPres p1 p2 ∙ canonicalizePres (p1 , p2))
            (refl ∙ canonicalizePres (p1 , p2))
  lem4 p1 p2 x = congP (λ i p → p ∙ (canonicalizePres (p1 , p2))) (lem3 p1 p2 x)
  lem2 : (p1 p2 : ℕ) →
         (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize (p1 , p2) ≡ (n , zero)) ] (canonicalizeSignDec (p1 , p2) ≡ inl a)) →
          PathP
            (λ i → sucRPres p1 p2 i ≡ [ canonicalize (p1 , p2) ])
            (sucRPres p1 p2 ∙ canonicalizePres (p1 , p2))
            (canonicalizePres (p1 , p2))
  lem2 p1 p2 x = subst (λ y → PathP
                                (λ i → sucRPres p1 p2 i ≡ [ canonicalize (p1 , p2) ])
                                (sucRPres p1 p2 ∙ canonicalizePres (p1 , p2))
                                y)
                        (sym (lUnit (canonicalizePres (p1 , p2))))
                        (lem4 p1 p2 x)
  lem : (p1 p2 : ℕ) →
        (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize (p1 , p2) ≡ (n , zero)) ] (canonicalizeSignDec (p1 , p2) ≡ inl a)) →
        PathP
          (λ i → sucRPres p1 p2 i ≡ depConstrGZPos (fst (fst x)))          
          (((sucRPres p1 p2 ∙ canonicalizePres (p1 , p2)) ∙ cong [_] (snd (fst x)) ∙ refl))          
          (canonicalizePres (p1 , p2) ∙ cong [_] (snd (fst x)) ∙ refl)
  lem p1 p2 x = congP (λ i p → _∙_ p ((cong [_] (snd (fst x))) ∙ refl)) (lem2 p1 p2 x)
  lem5 : (p1 p2 : ℕ) →
         (x : Σ[ a ∈ (Σ[ n ∈ ℕ ] canonicalize (p1 , p2) ≡ (n , zero)) ] (canonicalizeSignDec (p1 , p2) ≡ inl a)) →
         PathP
          (λ i → P (sucRPres p1 p2 i))
          (transport
           (cong P
            (sym
             ((sucRPres p1 p2 ∙ canonicalizePres (p1 , p2)) ∙ cong [_] (snd (fst x)) ∙ refl)))
           (posP (fst (fst x))))
          (transport
           (cong P
            (sym (canonicalizePres (p1 , p2) ∙ cong [_] (snd (fst x)) ∙ refl)))
           (posP (fst (fst x))))
  lem5 p1 p2 x = congP (λ i p → transport (cong P (sym p)) (posP (fst (fst x)))) (lem p1 p2 x)
  funcCanonical : (p : ℕ × ℕ) → PathP (λ i → P (canonicalizePres p i)) (func p) (func (canonicalize p))
  funcCanonical (zero , p2) = refl
  funcCanonical (suc p1 , zero) = refl
  funcCanonical (suc p1 , suc p2) =
    compPathP'
      (Sum.rec
        (λ x → subst2
          (λ y z → PathP (λ i → P (sucRPres p1 p2 i)) y z)
          (sym (funcLeft (suc p1 , suc p2) x))
          (sym (funcLeft (p1 , p2) x))
          (lem5 p1 p2 x))
        {!!}
        (sumRememberEq (canonicalizeSignDec (p1 , p2))))
      (funcCanonical (p1 , p2))





-- Sum.rec (λ s → toPathP (transport (λ v → P (canonicalizePres p v)) (func p) ≡⟨ refl ⟩
  --                                           transport (λ v → P (canonicalizePres p v))
  --                                               (Sum.rec (λ x → transport (cong P (sym ([ p ] ≡⟨ (canonicalizePres p) ⟩ [ canonicalize p ]
  --                                                                                             ≡⟨ (cong [_] (snd x)) ⟩ (depConstrGZPos (fst x)) ∎)))
  --                                                                         (posP (fst x)))
  --                                                        (λ x → transport (cong P (sym ([ p ] ≡⟨ canonicalizePres p ⟩ [ canonicalize p ]
  --                                                                                             ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
  --                                                                                             ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
  --                                                                         (negsucP (fst (proj₂ (snd x)))))
  --                                                        (canonicalizeSignDec p)) ≡⟨ cong (λ y → transport (λ v → P (canonicalizePres p v))
  --                                                                                                          (Sum.rec (λ x → transport (cong P (sym ([ p ] ≡⟨ (canonicalizePres p) ⟩ [ canonicalize p ]
  --                                                                                                                                                        ≡⟨ (cong [_] (snd x)) ⟩ (depConstrGZPos (fst x)) ∎)))
  --                                                                                                                                    (posP (fst x)))
  --                                                                                                                   (λ x → transport (cong P (sym ([ p ] ≡⟨ canonicalizePres p ⟩ [ canonicalize p ]
  --                                                                                                                                                        ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
  --                                                                                                                                                        ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
  --                                                                                                                                    (negsucP (fst (proj₂ (snd x)))))
  --                                                                                                                   (y))) (snd s) ⟩
  --                                          transport (λ v → P (canonicalizePres p v))
  --                                                    (transport (cong P (sym ([ p ] ≡⟨ (canonicalizePres p) ⟩ [ canonicalize p ]
  --                                                                                   ≡⟨ (cong [_] (snd (fst s))) ⟩ (depConstrGZPos (fst (fst s))) ∎)))
  --                                                               (posP (fst (fst s)))) ≡⟨ {!!} ⟩
  --                                          {!!} ≡⟨ {!!} ⟩
  --                                          transport (cong P (sym ([ canonicalize p ] ≡⟨ (canonicalizePres (canonicalize p)) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                     ≡⟨ (cong [_] (snd (fst (canonicalizeSignDecCanonicalLeft' p s)))) ⟩ (depConstrGZPos (fst (fst (canonicalizeSignDecCanonicalLeft' p s)))) ∎)))
  --                                                    (posP (fst (fst (canonicalizeSignDecCanonicalLeft' p s)))) ≡⟨ {!!} ⟩
  --                                          Sum.rec (λ x → transport (cong P (sym ([ canonicalize p ] ≡⟨ (canonicalizePres (canonicalize p)) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                                    ≡⟨ (cong [_] (snd x)) ⟩ (depConstrGZPos (fst x)) ∎)))
  --                                                                   (posP (fst x)))
  --                                                  (λ x → transport (cong P (sym ([ canonicalize p ] ≡⟨ canonicalizePres (canonicalize p) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                                    ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
  --                                                                                                    ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
  --                                                                   (negsucP (fst (proj₂ (snd x)))))
  --                                                  (transport (λ i → canonicalizeSignDecCanonicalType p i) (canonicalizeSignDec p)) ≡⟨ refl ⟩
  --                                          Sum.rec (λ x → transport (cong P (sym ([ canonicalize p ] ≡⟨ (canonicalizePres (canonicalize p)) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                                    ≡⟨ (cong [_] (snd x)) ⟩ (depConstrGZPos (fst x)) ∎)))
  --                                                                   (posP (fst x)))
  --                                                  (λ x → transport (cong P (sym ([ canonicalize p ] ≡⟨ canonicalizePres (canonicalize p) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                                    ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
  --                                                                                                    ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
  --                                                                   (negsucP (fst (proj₂ (snd x)))))
  --                                                  (canonicalizeSignDec (canonicalize p)) ≡⟨ refl ⟩
  --                                          func (canonicalize p) ∎))
  --                           (λ s → compPathP' {!!} (congP {!λ i a → Sum.rec (λ x → transport (cong P (sym ([ canonicalize p ] ≡⟨ (canonicalizePres (canonicalize p)) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                                    ≡⟨ (cong [_] (snd x)) ⟩ (depConstrGZPos (fst x)) ∎)))
  --                                                                   (posP (fst x)))
  --                                                  (λ x → transport (cong P (sym ([ canonicalize p ] ≡⟨ canonicalizePres (canonicalize p) ⟩ [ canonicalize (canonicalize p) ]
  --                                                                                                    ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
  --                                                                                                    ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
  --                                                                   (negsucP (fst (proj₂ (snd x)))))
  --                                                  (a)!} (canonicalizeSignDecCanonical p)))
  --                           (sumRememberEq (canonicalizeSignDec p))
  funcCanonical⁻ : (p : ℕ × ℕ) → PathP (λ i → P (canonicalizePres⁻ p i)) (func (canonicalize p)) (func p)
  funcCanonical⁻ p = symP (funcCanonical p)
  composedPaths : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b)) i)) (func a) (func b)
  composedPaths a b r = compPathP' {B = P} (funcCanonical a) (compPathP' {B = P} (cong func (canonicalIsCanonical a b r)) (funcCanonical⁻ b))
  typesSame : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b)) i)) (func a) (func b) ≡ PathP (λ i → P (eq/ a b r i)) (func a) (func b)
  typesSame a b r = cong (λ x → PathP (λ i → P (x i)) (func a) (func b)) (squash/ [ a ] [ b ] ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b))) (eq/ a b r))
  resp : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P (eq/ a b r i)) (func a) (func b)
  resp a b r = transport (typesSame a b r) (composedPaths a b r)


