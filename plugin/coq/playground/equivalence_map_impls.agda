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
open import Cubical.Data.Empty

data ⊤ : Type where
  tt : ⊤

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


module lib (A : Set) where
  if_then_else_true : (x y : Maybe A) -> (if true then x else y) ≡ x
  if_then_else_true x y = refl

  equalIsTrue : (x : ℕ) -> (x == x) ≡ true
  equalIsTrue zero = refl
  equalIsTrue (suc x) = equalIsTrue x

{--
  not : Bool → Bool
  not = {!!}
--}


  -- ifElimTrue : (x y : Maybe A) (b : Bool) -> (b ≡ true) -> (if b then x else y) ≡ x
  -- ifElimTrue x y b proofTrue = cong (λ b -> if b then x else y) proofTrue
  ifElimTrue : {A : Set} (x y : A) (b : Bool) -> (b ≡ true) -> (if b then x else y) ≡ x
  ifElimTrue x y b proofTrue = cong (λ b -> if b then x else y) proofTrue

  ifElimFalse : (x y : Maybe A) (b : Bool) -> (b ≡ false) -> (if b then x else y) ≡ y
  ifElimFalse x y b proofTrue = cong (λ b -> if b then x else y) proofTrue

  -- in the future, maybe generalize to types with decidable equalities
  ifLifted_equal_then_else_ : {B : Set} (x y : ℕ) -> (((x == y) ≡ true ) → B) → (((x == y) ≡ false ) → B) → B
  ifLifted zero equal zero then ifEqual else ifNotEqual = ifEqual refl
  ifLifted zero equal suc y then ifEqual else ifNotEqual = ifNotEqual refl
  ifLifted suc x equal zero then ifEqual else ifNotEqual = ifNotEqual refl 
  ifLifted suc x equal suc y then ifEqual else ifNotEqual = ifLifted x equal y then ifEqual else ifNotEqual

  ifElimEitherWay : {B : Set} (x y : ℕ) -> (branchTrue branchFalse : B) -> (branchTrue ≡ branchFalse) -> ((if x == y then branchTrue else branchFalse) ≡ branchTrue)
  ifElimEitherWay = {!!}

  ifElimEitherWay' : {B : Set} (x y : ℕ) -> (branchTrue branchFalse : B) -> (branchTrue ≡ branchFalse) -> ((if x == y then branchTrue else branchFalse) ≡ branchFalse)
  ifElimEitherWay' = {!!}


  module NaiveList where

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

    insertFindGood : (k : ℕ) (v : A) (l : List (Pair ℕ A)) → find k (insert k v l) ≡ Maybe.just v
    insertFindGood k v [] = ifElimTrue (just v) nothing (k == k) (equalIsTrue k)
    insertFindGood zero v ((zero , snd) :: l) = refl
    insertFindGood zero v ((suc fst , snd) :: l) = refl
    insertFindGood (suc k) v ((zero , snd) :: l) = insertFindGood (suc k) v l
    insertFindGood (suc k) v ((suc fst , snd) :: l) = ifElimTrue (Maybe.just v)
      (find (suc k) (if k == fst then l else ((suc fst , snd) :: delete (suc k) l)))
      (k == k)
      (equalIsTrue k)

  module SortedList where
    length : List (Pair ℕ A) → ℕ -- todo: when compiling, swap out with O(1) impl
    length [] = 0
    length (x :: x₁) = 1 + length x₁

    nth : (x : ℕ) → (L : List (Pair ℕ A)) -> Maybe (Pair ℕ A) -- todo: when compiling, swap out with O(1) Array impl
    nth x [] = Maybe.nothing
    nth zero (x₁ :: L) = Maybe.just x₁
    nth (suc x) (x₁ :: L) = nth x L

    isJust : Maybe (Pair ℕ A) → Type
    isJust (just x) = ⊤
    isJust nothing = ⊥

    isNothing : Maybe A → Type
    isNothing (just x) = ⊥
    isNothing nothing = ⊤

    nthLengthGood : (l : List (Pair ℕ A)) → (x n : ℕ) → ((n == length l) ≡ true) → (((x < n) or (x == n)) ≡ true) → isJust (nth x l)
    nthLengthGood [] x n nIsLength xLeqN = {!!}
    nthLengthGood (x₁ :: l) x n nIsLength xLeqN = {!!}

    -- same as NaiveList
    findNaive : (x : ℕ) → (L : List (Pair ℕ A)) → Maybe A
    findNaive x [] = Maybe.nothing
    findNaive x ((fst , snd) :: L) = if x == fst then Maybe.just snd else findNaive x L

    findFast : (x : ℕ) → (L : List (Pair ℕ A)) → Maybe A
    findFast = {!!}

    insert : (x : ℕ) → (y : A) → (L : List (Pair ℕ A)) → (List (Pair ℕ A))
    insert x y [] =  (x , y) :: []
    insert x y ((x' , y') :: L) = if x == x' then ((x , y) :: L) else {!!}

  data Tree (A : Set) : Set where
    null : Tree A
    leaf : (Pair ℕ A) → Tree A
    node : (Pair ℕ A) → Tree A → Tree A → Tree A

  -- left child is smaller, right child is greater than

  -- absurd : true ≡ false -> empty
  -- absurd = {!!}

  -- unbalanced tree
  module NaiveTree where
    find : {A : Set} (x : ℕ) → (L : Tree A) → Maybe A
    find x null = Maybe.nothing
    find x (leaf (fst , snd)) = if x == fst then Maybe.just snd else Maybe.nothing
    find x (node (fst , snd) L L') =
      if x == fst
      then Maybe.just snd
      else (if x < fst
        then find x L
        else find x L')

    -- overwrite if key already exists
    insert : {A : Set} (x : ℕ) → (y : A) → (L : Tree A) → Tree A
    insert x y (null) = leaf (x , y)
    insert x y (leaf (fst , snd)) = if x == fst then leaf (x , y) else (if x < fst then node (x , y) (leaf (fst , snd)) null else node (x , y) null (leaf (fst , snd)))
    insert x y (node (fst , snd) L L') = if x == fst then node (x , y) L L' else (if x < fst then node (fst , snd) (insert x y L ) L' else node (fst , snd) L (insert x y L'))

    isEmpty : {A : Set} (L : Tree A) -> Bool
    isEmpty null = true
    isEmpty (leaf x) = false
    isEmpty (node x L L₁) = false

    boolEq : Bool → Bool → Bool
    boolEq false false = true
    boolEq false true = false
    boolEq true false = false
    boolEq true true = true

    -- get rightmmost val
    removeNextVal : {A : Set} (x : ℕ) → (L : Tree A) → isEmpty L ≡ false → Pair (Tree A) (Pair ℕ A)
    removeNextVal x null proofNotEmpty = Cubical.Data.Empty.elim {A = {!!}} (true≢false proofNotEmpty)
    removeNextVal x (leaf (fst , snd)) proofNotEmpty = (null , (fst , snd))
    removeNextVal x (node x₁ L₁ null) proofNotEmpty = (L₁ , x₁)
    removeNextVal x (node x₁ L₁ (leaf x₂)) proofNotEmpty = ((node x₁ null L₁) , x₂)
    removeNextVal x (node x₁ L₁ (node x₂ L L₂)) proofNotEmpty = let (L' , a) = removeNextVal x (node x₂ L L₂) refl in ((node x₁ L' L₁), a) -- needed to inline isEmpty

    removeNextValHacky : {A : Set} (x : ℕ) → (default : A) → (L : Tree A) → Pair (Tree A) (Pair ℕ A)
    removeNextValHacky x default null = (null , (x , default)) --  Cubical.Data.Empty.elim (true≢false proofNotEmpty)
    removeNextValHacky x default (leaf (fst , snd)) = (null , (fst , snd))
    removeNextValHacky x default (node x₁ null L₁) = (L₁ , x₁)
    removeNextValHacky x default (node x₁ (leaf x₂) L₁) = ((node x₁ null L₁) , x₂)
    removeNextValHacky x default (node x₁ (node x₂ L L₂) L₁) = let (L' , a) = removeNextValHacky x default (node x₂ L L₂) in ((node x₁ L' L₁), a) -- needed to inline isEmpty

    delete : {A : Set} (x : ℕ) → (L : Tree A) → Tree A
    delete x null = null
    delete x (leaf (fst , snd)) = if x == fst then null else leaf (fst , snd)
    delete x (node (fst , snd) null L') = if x == fst then L' else (if x < fst then (node (fst , snd) null L') else (node (fst , snd) null (delete x L')))
    delete x (node (fst , snd) (leaf (fst' , snd')) L') =
      if x == fst
      then node (fst' , snd') null L'
      else
        (if x < fst
        then (node (fst , snd) (delete x (leaf (fst' , snd'))) L')
        else
        (node (fst , snd) (leaf (fst' , snd')) (delete x L')))
    delete x (node (fst , snd) (node (fst' , snd') L L₁) L') = -- replace with the leftmost val
      let (removedLeftTree , nextNode) = removeNextVal x (node (fst' , snd') L L₁) refl in
      if x == fst
      then node nextNode removedLeftTree L'
      else
        (if x < fst then (node (fst , snd) (delete x (node (fst' , snd') L L₁)) L') else (node (fst , snd) (node (fst' , snd') L L₁) (delete x L')))


    sucMaybe : Maybe A -> Maybe A
    sucMaybe (just x) = just {!suc x!}
    sucMaybe nothing = {!!}


    insertFindGood : (k : ℕ) (v : A) (l : Tree A) → find k (insert k v l) ≡ Maybe.just v
    insertFindGood k v null = ifElimTrue (just v) nothing (k == k) (equalIsTrue k)
    insertFindGood k v (leaf (k' , v')) = {!!}
    {--
    insertFindGood k v (leaf (k' , v')) = ifLifted k equal k' then
      (λ proofEqual → cong (λ a → find k {!a!}) (ifElimTrue (leaf (k , v)) {!!} (k == k') proofEqual))
      else
      (λ proofNotEqual → {!!}) --}
{--
Goal: find k
      (if k == k' then leaf (k , v) else
       (if k < k' then node (k , v) (leaf (k' , v')) null else
        node (k , v) null (leaf (k' , v'))))
      ≡ just v
      --}
    insertFindGood k v (node x l l₁) = {!!}
    {--
    insertFindGood zero v (leaf (zero , snd₁)) = refl
    insertFindGood zero v (leaf (suc fst , snd₁)) = refl
    insertFindGood (suc k) v (leaf (zero , snd)) = ifElimTrue (just v) (if k < k then nothing else nothing) (k == k) (equalIsTrue k)
    insertFindGood (suc k) v (leaf (suc fst , snd)) =  if suc k == suc fst then {!!} else {!!} -- (λ x → insertFindGood k v (leaf (fst , snd))) {!suc k!} -- (insertFindGood k v (leaf (fst , snd)))
    --}

-- Goal: find (suc k)
--       (if k == fst then leaf (suc k , v) else
--        (if k < fst then node (suc k , v) (leaf (suc fst , snd)) null else
--         node (suc k , v) null (leaf (suc fst , snd)))
--       )
--       ≡ just v


  -- data Map (A : Set) : List (Pair ℕ A) → Set where
  --   null : Map A []
  --   insert''' : ∀ {L} (x : ℕ) (y : A) → Map A L → Map A ((x , y) :: L)
    -- delete : ∀ {L} (x :)
    -- find : ∀ {L} (x : A) → Map A L → find' x L → Maybe A
    -- delete : ∀ {L} (x : A) (y : B) → Map A B L → Map A B ((x , y) :: L)


  -- mapInsertFind3 : find (insert 3 null)
