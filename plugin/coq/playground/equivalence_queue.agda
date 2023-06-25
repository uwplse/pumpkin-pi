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
-- open import Cubical.Data.Bool
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

data True : Type where
  tt : True

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


module OneList where
    Q = List Nat
    A = Nat

    bind : (Maybe (Q × A)) → ((Q × A) → (Maybe (Q × A))) → Maybe (Q × A)
    bind (just x) f = f x
    bind nothing f = nothing

    last : Q → Maybe (Q × A)
    last [] = nothing
    last (x :: []) = just ([] ,  x)
    last (x :: (x₁ :: x')) = bind (last (x₁ :: x')) (help x)
       where
       help : A → (Q × A) → (Maybe (Q × A))
       help x (xs , res) = just ((x :: xs) , res)


    OneList = record { A = A; Q = Q ; null = [] ; enqueue = λ x x' → x :: x' ; dequeue = last }

    depConstrEmpty : Q
    depConstrEmpty = []

    depConstrInsert : A → Q → Q
    depConstrInsert x x' = x :: x'

    depElimOneList : (P : Q -> Type) -> (P depConstrEmpty) -> (∀ a q -> (P q) -> P (depConstrInsert a q)) -> ((x : Q) -> P x)
    depElimOneList P baseCase consCase [] = baseCase
    depElimOneList P baseCase consCase (x :: l) = consCase x l (depElimOneList P baseCase consCase l)

module TwoList where
    Q = (List Nat × List Nat)
    A = Nat

    reverse : List A → List A
    reverse l = go l [] where
        go : List A → List A → List A
        go [] x₁ = x₁
        go (x :: xs) x₁ = go xs (x :: x₁)

    dequeue : Q → Maybe (Q × A)
    dequeue (x , []) = let xs = reverse x in help xs where
      help : List A → Maybe (Q × A)
      help [] = nothing
      help (x :: x₁) = just ((([] , x₁)), x)
    dequeue (x , (x₁ :: x')) = just ((((x , x')) , x₁))

    enqueue : A → Q → Q
    enqueue x (x₁ , x₂) = (x :: x₁ , x₂)

    TwoList = record { A = A; Q = Q; null = ([] , []); enqueue = enqueue ; dequeue = dequeue }

    -- tail-recursive canonicalization func
    -- canonicalize : Q → OneList.Q
    -- canonicalize q = go q OneList.depConstrEmpty where
    --   go : Q → OneList.Q → OneList.Q
    --   go input output with dequeue input
    --   ...      | just (q , x) = go q (OneList.depConstrInsert x output)
    --   ...      | nothing = output

    canonicalizeTerm : List A → List A → OneList.Q
    canonicalizeTerm q q' = go q q' OneList.depConstrEmpty where
      go : List A → List A → OneList.Q → OneList.Q -- inlined dequeue here to make term checking happy
      go [] [] output = output
      go (x :: xs) [] output with reverse (x :: xs)
      ...               | [] = output
      ...               | (y :: ys) = go [] ys (OneList.depConstrInsert y output)
      go in1 (x :: xs) output = go in1 xs (OneList.depConstrInsert x output)

    canonicalize : Q → OneList.Q
    canonicalize (x , x₁) = canonicalizeTerm x x₁

    canonicalizeInv : OneList.Q → Q
    canonicalizeInv x = ([] , x)

    _and_ : Type → Type → Type
    _and_ x x₁ = True

    defEquivN : Nat → Nat → Type
    defEquivN zero zero = True
    defEquivN zero (suc b) = ⊥
    defEquivN (suc a) zero = ⊥
    defEquivN (suc a) (suc b) = defEquivN a b

    defEquivL : List Nat → List Nat → Type
    defEquivL [] [] = True
    defEquivL [] (x :: x') = ⊥
    defEquivL (x :: x₂) [] = ⊥
    defEquivL (zero :: x₂) (zero :: x'') = defEquivL x₂ x''
    defEquivL (zero :: x₂) (suc x' :: x'') = ⊥
    defEquivL (suc x :: x₂) (zero :: x'') = ⊥
    defEquivL (suc x :: x₂) (suc x' :: x'') = defEquivL (x :: x₂) (x' :: x'')

    defEquivQ : Q → Q → Type
    defEquivQ ([] , x₂) ([] , x₃) = defEquivL x₂ x₃
    defEquivQ ([] , x₂) ((x :: x') , x₃) = ⊥
    defEquivQ ((x :: x₄) , x₂) ([] , x₃) = ⊥
    defEquivQ ((zero :: x₄) , x₂) ((zero :: x') , x₃) = defEquivQ (x₄ , x₂) (x' , x₃)
    defEquivQ ((zero :: x₄) , x₂) ((suc x'' :: x') , x₃) = ⊥
    defEquivQ ((suc x :: x₄) , x₂) ((zero :: x') , x₃) = ⊥
    defEquivQ ((suc x :: x₄) , x₂) ((suc x'' :: x') , x₃) = defEquivQ ((x :: x₄) , x₂) ((x'' :: x') , x₃)

    quotient : Q → Q → Type
    quotient x x' = defEquivQ (genCanon x) (genCanon x') where
      genCanon : Q → Q
      genCanon x = canonicalizeInv (canonicalize x)
