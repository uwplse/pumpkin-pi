{-# OPTIONS --safe --cubical #-}
module equivalence_queue where

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
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Prod
-- open import Cubical.Data.List
-- open import Agda.Builtin.Equality renaming (_≡_ to _≡'_; refl to refl')
open import Cubical.Data.Equality renaming (
  _≡_ to _≡'_
  ; refl to refl'
  ; sym to sym'
  ; _∙_ to _dot'_
  )

-- record Pair {ℓ} {ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ')
-- record Pair A B where
--   constructor _,_
--   field fst : A
--         snd : B

data List {ℓ} (A : Set ℓ) : Set ℓ where
  []   : List A
  _::_ : A -> List A -> List A

record Queue {ℓ} : Set (ℓ-suc ℓ) where
-- record Queue {ℓ} (A : Set ℓ) : Set (ℓ-suc ℓ) where
  field
    A : Set ℓ
    Q : Set ℓ
    null : Q
    enqueue : A → Q → Q
    dequeue : Q → Maybe (Q × A) -- similiar to the Cubical lib def but with Maybe bc monads


-- bind : (Maybe B) -- → (B -> Maybe B) -> Maybe B
-- bind = {!!}

module OneList where
    bind : (Maybe (List Nat × Nat)) → ((List Nat × Nat) → (Maybe (List Nat × Nat))) → Maybe (List Nat × Nat)
    bind (just x) f = f x
    bind nothing f = nothing

    last : List Nat → Maybe (List Nat × Nat)
    last [] = nothing
    last (x :: []) = just ([] ,  x)
    last (x :: (x₁ :: x')) = bind (last (x₁ :: x')) (help x)
       where
       help : Nat → (List Nat × Nat) → (Maybe (List Nat × Nat))
       help x (xs , res) = just ((x :: xs) , res)

    OneList = record { A = Nat; Q = List Nat ; null = [] ; enqueue = λ x x' → (x :: x') ; dequeue = last }

module TwoList where
    enqueue : Nat → (List Nat × List Nat) → (List Nat × List Nat)
    enqueue x (x₁ , x₂) = (x :: x₁ , x₂)

    reverse : List Nat → List Nat
    reverse l = go l [] where
        go : List Nat → List Nat → List Nat
        go [] x₁ = x₁
        go (x :: xs) x₁ = go xs (x :: x₁)


    dequeue : (List Nat × List Nat) → Maybe ((List Nat × List Nat) × Nat)
    dequeue (x , []) = let xs = reverse x in help xs where
      help : List Nat → Maybe ((List Nat × List Nat) × Nat)
      help [] = nothing
      help (x :: x₁) = just ((([] , x₁)), x)
    dequeue (x , (x₁ :: x')) = just ((((x , x')) , x₁))

    TwoList = record { A = Nat; Q = (List Nat × List Nat) ; null = ([] , []) ; enqueue = enqueue ; dequeue = dequeue }



-- record Queue {ℓ} (A : Set ℓ) : Set (ℓ-suc ℓ) where
--   field Q : Set ℓ
--         enqueue : A → Q → Q
--         dequeue : Q → (Q , A)
