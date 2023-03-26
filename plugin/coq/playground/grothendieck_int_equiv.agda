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
open import Cubical.Data.Sum
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

depElimGZNegSuc : (P : GZ → Set) → (∀ x → isSet (P x)) → (∀ n → P (depConstrGZPos n)) → (∀ n → P (depConstrGZNegSuc n)) → ∀ z → P z
depElimGZNegSuc P set posP negsucP = SetQuotients.elim set {!!} {!!}
