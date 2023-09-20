{-# OPTIONS --safe --cubical #-}
module alternateFunExtDep where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

-- This module implements a definitionally simpler version of funExtDep. The code comes from this pull request:
-- https://github.com/agda/cubical/pull/1001#issuecomment-1724869895
-- We copy it here so we can use it without modifying our version of the library. 

erp : I → I → I → I
erp t i j = (~ t ∧ i) ∨ (t ∧ j) ∨ (i ∧ j)

private
  eqI : I → I → I
  eqI i j = (i ∧ j) ∨ (~ i ∧ ~ j)
  variable
    ℓ ℓ₁ : Level

coei→j : ∀ {ℓ} (A : I → Type ℓ) (i j : I) → A i → A j
coei→j A i j a = transp (λ k → A (erp k i j)) (eqI i j) a

coei→1 : ∀ {ℓ} (A : I → Type ℓ) (i : I) → A i → A i1
coei→1 A i a = coei→j A i i1 a

coei→i : ∀ {ℓ} (A : I → Type ℓ) (i : I) (a : A i) → coei→j A i i a ≡ a
coei→i A i a j = transp (λ _ → A i) (erp j (i ∨ ~ i) i1) a
  where
  -- note: coei→i is almost just transportRefl (but the φ for the
  -- transp is i ∨ ~ i, not i0)
  _ : Path (PathP (λ i → A i → A i) (λ a → a) (λ a → a))
           (λ i a → coei→j A i i a)
           (λ i a → transp (λ _ → A i) (i ∨ ~ i) a)
  _ = refl

funExtDep : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
  {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ({x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁) → PathP (λ i → B i (p i)) (f x₀) (g x₁))
  → PathP (λ i → (x : A i) → B i x) f g
funExtDep {A = A} {B} {f} {g} h i x =
  transp (λ k → B i (coei→i A i x k)) (i ∨ ~ i) (h (λ j → coei→j A i j x) i)

-- Credit to Tom in the Univalent Agda discord server for the below term.
removeFunExtDep :
 {A B : Type} →
 (T : A ≡ B) →
 (PAType : A → Type) →
 (PBType : B → Type) →
 (P : (t0 : A) (t1 : B) → (t0≡t1 : PathP (λ i → T i) t0 t1) → PathP (λ i → Type) (PAType t0) (PBType t1)) →
 (PA : (t0 : A) → PAType t0) →
 (PB : (t1 : B) → PBType t1) →
 ((t0 : A) (t1 : B) (t0≡t1 : PathP (λ i → T i) t0 t1) →
   PathP
    (λ i → P t0 t1 t0≡t1 i)
    (PA t0)
    (PB t1)) →
 ((t0 : A) (t1 : B) (t0≡t1 : PathP (λ i → T i) t0 t1) →
   PathP
    (λ i → funExtDep (λ {t0} {t1} t0≡t1 → P t0 t1 t0≡t1) i (t0≡t1 i))
    (PA t0)
    (PB t1))
removeFunExtDep {A = A} = J (λ B T → (PAType : A → Type) →
             (PBType : B → Type) →
             (P : (t0 : A) (t1 : B) → (t0≡t1 : PathP (λ i → T i) t0 t1) → PathP (λ i → Type) (PAType t0) (PBType t1)) →
             (PA : (t0 : A) → PAType t0) →
             (PB : (t1 : B) → PBType t1) →
             ((t0 : A) (t1 : B) (t0≡t1 : PathP (λ i → T i) t0 t1) →
               PathP
                (λ i → P t0 t1 t0≡t1 i)
                (PA t0)
                (PB t1)) →
             ((t0 : A) (t1 : B) (t0≡t1 : PathP (λ i → T i) t0 t1) →
               PathP
                (λ i → funExtDep (λ {t0} {t1} t0≡t1 → P t0 t1 t0≡t1) i (t0≡t1 i))
                (PA t0)
                (PB t1)))
    λ PAType PBType P PA PB h t0 t1 →
    J (λ t1 t0≡t1 → PathP (λ i → funExtDep (λ {t0} {t1} t0≡t1 → P t0 t1 t0≡t1) i (t0≡t1 i)) (PA t0) (PB t1))
      (transp
        (λ t → PathP (λ i → P (transp (λ k → A) (~ i ∨ ~ t) t0)
                              (transp (λ k → A) (i ∨ ~ t) t0)
                              (λ j → transp (λ k → A) (((i ∧ j) ∨ ~ i ∧ ~ j) ∨ ~ t) t0)
                              i)
                     (PA t0)
                     (PB t0))
        i0
        (h t0 t0 refl))
