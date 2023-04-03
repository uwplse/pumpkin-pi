{-# OPTIONS --safe --cubical #-}
module equivalence_map_impls where

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


data List {ℓ} (A : Set ℓ) : Set ℓ where
  []   : List A
  _::_ : A -> List A -> List A

-- data Vec (A : Set) : ℕ → Set where
--   []  : Vec A zero
--   _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)


-- KVStore interface (maybe force the user to provide some correctness theorems as well?)
record KVStore {ℓ''} (A : Set ℓ'') : Set (ℓ-suc ℓ'') where
  field
    KV : Set ℓ''
    null : KV
    insert : ℕ → A → KV → KV
    delete : ℕ → KV → KV
    find : ℕ → KV → Maybe A

record Pair {ℓ} {ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ-max ℓ ℓ')
record Pair A B where
  constructor _,_
  field fst : A
        snd : B

module NaiveList {ℓ} (A : Set ℓ) where

  find : (x : ℕ) → (L : List (Pair ℕ A)) → Maybe A
  find x [] = Maybe.nothing
  find x ((fst , snd) :: L) = if x == fst then Maybe.just snd else find x L

  insert' : (x : ℕ) → (y : A) → (L : List (Pair ℕ A)) → (List (Pair ℕ A))
  insert' x y L =  (x , y) :: L

  delete : (x : ℕ) → (L : List (Pair ℕ A)) → List (Pair ℕ A)
  delete x [] = []
  delete x ((fst , snd) :: L) = if x == fst then L else ((fst , snd) :: delete x L)

  -- do not allow dup keys; if dup, will overwrite
  insert : (x : ℕ) → (y : A) → (L : List (Pair ℕ A)) → (List (Pair ℕ A))
  insert x y L = insert' x y (delete x L)

  store : KVStore A
  store = record { KV = List (Pair ℕ A); null = []; insert = insert; delete = delete; find = find }

  insertFindGood : (k : ℕ) (v : A) (l : store A) → find k (insert k v l) ≡ Maybe.just v
  insertFindGood = {!!}

data Tree (A : Set) : Set where
   leaf : (Pair ℕ A) → Tree A
   node : (Pair ℕ A) → Tree A → Tree A → Tree A

module NaiveTree {ℓ} (A : Set) (sA : isSet A) where
  find : {A : Set} (x : ℕ) → (L : Tree A) → Maybe A
  find x (leaf (fst , snd)) = if x == fst then Maybe.just snd else Maybe.nothing
  find x (node (fst , snd) L L') =
    if x == fst
    then Maybe.just snd
    else (if x < fst
      then find x L
      else find x L')

  insert : {A : Set} (x : ℕ) → (y : A) → (L : Tree A) → Tree A
  insert x y (leaf (fst , snd)) = if x == fst then leaf (x , y) else {!!}
  insert x y (node (fst , snd) L L') = if x == fst then node (x , y) L L' else {!!}

  delete : {A : Set} (x : ℕ) → (L : Tree A) → Tree A
  delete = {!!}

  store : KVStore A
  store = record { KV = Tree A ; null = {!!}; insert = {!!}; delete = {!!}; find = {!!} }


-- data Map (A : Set) : List (Pair ℕ A) → Set where
--   null : Map A []
--   insert''' : ∀ {L} (x : ℕ) (y : A) → Map A L → Map A ((x , y) :: L)
  -- delete : ∀ {L} (x :)
  -- find : ∀ {L} (x : A) → Map A L → find' x L → Maybe A
  -- delete : ∀ {L} (x : A) (y : B) → Map A B L → Map A B ((x , y) :: L)


-- mapInsertFind3 : find (insert 3 null)
