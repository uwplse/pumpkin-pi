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
canonicalizePres (suc n1 , suc n2) =
  [ suc n1 , suc n2 ] ≡⟨ sucRPres n1 n2 ⟩
  [ n1 , n2 ] ≡⟨ canonicalizePres (n1 , n2) ⟩
  [ canonicalize (n1 , n2) ] ∎

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

depElimGZNegSuc : (P : GZ → Set) → (∀ x → isSet (P x)) → (∀ n → P (depConstrGZPos n)) → (∀ n → P (depConstrGZNegSuc n)) → ∀ z → P z
depElimGZNegSuc P set posP negsucP = SetQuotients.elim set func resp where
  func : (p : ℕ × ℕ) → P [ p ]
  func p = Sum.rec (λ x → transport (cong P (sym ([ p ] ≡⟨ (canonicalizePres p) ⟩ [ canonicalize p ]
                                                  ≡⟨ (cong [_] (snd x)) ⟩ (depConstrGZPos (fst x)) ∎)))
                                    (posP (fst x)))
                   (λ x → transport (cong P (sym ([ p ] ≡⟨ canonicalizePres p ⟩ [ canonicalize p ]
                                                        ≡⟨ cong [_] (proj₁ (snd x)) ⟩ [ (zero , (fst x)) ]
                                                        ≡⟨ cong [_] (×≡ refl (snd (proj₂ (snd x)))) ⟩ (depConstrGZNegSuc (fst (proj₂ (snd x)))) ∎)))
                                    (negsucP (fst (proj₂ (snd x)))))
                   (canonicalizeSignDec p)
  funcCanonical : (p : ℕ × ℕ) → PathP (λ i → P (canonicalizePres p i)) (func p) (func (canonicalize p))
  funcCanonical p = {!!}
  funcCanonical⁻ : (p : ℕ × ℕ) → PathP (λ i → P (canonicalizePres⁻ p i)) (func (canonicalize p)) (func p)
  funcCanonical⁻ p = symP (funcCanonical p)
  composedPaths : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b)) i)) (func a) (func b)
  composedPaths a b r = compPathP' {B = P} (funcCanonical a) (compPathP' {B = P} (cong func (canonicalIsCanonical a b r)) (funcCanonical⁻ b))
  typesSame : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b)) i)) (func a) (func b) ≡ PathP (λ i → P (eq/ a b r i)) (func a) (func b)
  typesSame a b r = cong (λ x → PathP (λ i → P (x i)) (func a) (func b)) (squash/ [ a ] [ b ] ((canonicalizePres a ∙ (cong [_] (canonicalIsCanonical a b r) ∙ canonicalizePres⁻ b))) (eq/ a b r))
  resp : (a b : ℕ × ℕ) (r : R a b) → PathP (λ i → P (eq/ a b r i)) (func a) (func b)
  resp a b r = transport (typesSame a b r) (composedPaths a b r)


