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

  cmpLifted_equal_then_ge_le_ : {B : Set} (x y : ℕ) -> (((x == y) ≡ true ) → B) → ((((x == y) or (not (x < y))) ≡ true ) → B) → (((x < y) ≡ true ) → B) → B
  cmpLifted zero equal zero then ifEqual ge ifGe le ifLe = ifEqual refl
  cmpLifted zero equal suc y then ifEqual ge ifGe le ifLe = ifLe refl
  cmpLifted suc x equal zero then ifEqual ge ifGe le ifLe = ifGe refl
  cmpLifted suc x equal suc y then ifEqual ge ifGe le ifLe = cmpLifted x equal y then ifEqual ge ifGe le ifLe

  -- ifElimEitherWay : {B : Set} (x y : ℕ) -> (branchTrue branchFalse : B) -> (branchTrue ≡ branchFalse) -> ((if x == y then branchTrue else branchFalse) ≡ branchTrue)
  -- ifElimEitherWay = {!!}

  -- ifElimEitherWay' : {B : Set} (x y : ℕ) -> (branchTrue branchFalse : B) -> (branchTrue ≡ branchFalse) -> ((if x == y then branchTrue else branchFalse) ≡ branchFalse)
  -- ifElimEitherWay' = {!!}


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

    -- computes n / m, with rounding
    _div_ : ℕ → ℕ → ℕ
    _div_ n zero = zero -- error, undefined
    _div_ n (suc m) = div-helper 0 m n m

    _div_withP_ : (n m : ℕ) → ((m == 0) ≡ false) → ℕ -- divsion with proof of well-defined
    _div_withP_ n zero proofNotZero = Cubical.Data.Empty.elim {A = λ _ → ℕ} (true≢false proofNotZero)
    _div_withP_ n (suc m) proofNotZero = div-helper 0 m n m

    divTest1 : 10 div 5 ≡ 2
    divTest1 = refl

    divTest2 : 11 div 5 ≡ 2
    divTest2 = refl

    divTest3 : 12 div 2 ≡ 6
    divTest3 = refl

    divTest4 : (4 + 5) div 2 ≡ 4
    divTest4 = refl

    divTest5 : (5 + 6) div 2 ≡ 5
    divTest5 = refl

    -- div-helper 0 1 10 1

    nth : (x : ℕ) → (L : List (Pair ℕ A)) -> Maybe (Pair ℕ A) -- todo: when compiling, swap out with O(1) Array impl
    nth x [] = Maybe.nothing
    nth zero (x₁ :: L) = Maybe.just x₁
    nth (suc x) (x₁ :: L) = nth x L

    isJust : Maybe (Pair ℕ A) → Type
    isJust (just x) = ⊤
    isJust nothing = ⊥

    isJustExtract : (a : Maybe (Pair ℕ A)) → isJust a -> (Pair ℕ A)
    isJustExtract (just x₁) x = x₁

    isNothing : Maybe A → Type
    isNothing (just x) = ⊥
    isNothing nothing = ⊤

    1st : Pair ℕ A → ℕ
    1st (fst₁ , snd₁) = fst₁

    2nd : Pair ℕ A → A
    2nd (fst₁ , snd₁) = snd₁

    _<=_ : ℕ → ℕ → Bool
    zero <= x' = true
    suc x <= zero = false
    suc x <= suc x' = x <= x'

    boundsGood : (l : List (Pair ℕ A)) → (x : ℕ) → Type
    boundsGood l x  = if x < length l then ⊤ else ⊥

    nthLengthGood : (l : List (Pair ℕ A)) → (x : ℕ) → boundsGood l x → isJust (nth x l)
    nthLengthGood [] (suc x) ()
    nthLengthGood (x₁ :: l) zero boundGoodProof = tt
    nthLengthGood (x₁ :: l) (suc x) boundGoodProof = nthLengthGood l x boundGoodProof

    nthLengthGood' : (l : List (Pair ℕ A)) → (x n : ℕ) → ((n == length l) ≡ true) → ((x < n) ≡ true) → isJust (nth x l)
    nthLengthGood' [] x zero nIsLength xLeqN = true≢false (sym xLeqN)
    nthLengthGood' [] x (suc n) nIsLength xLeqN = true≢false (sym nIsLength)
    nthLengthGood' (x₁ :: l) zero n nIsLength xLeqN = tt
    nthLengthGood' (x₁ :: l) (suc x) zero nIsLength xLeqN = Cubical.Data.Empty.elim {A = λ _ → isJust (nth (suc x) (x₁ :: l))} (true≢false (sym xLeqN))
    nthLengthGood' (x₁ :: l) (suc x) (suc n) nIsLength xLeqN = nthLengthGood' l x n nIsLength xLeqN

    -- same as NaiveList
    findNaive : (x : ℕ) → (L : List (Pair ℕ A)) → Maybe A
    findNaive x [] = Maybe.nothing
    findNaive x ((fst , snd) :: L) = if x == fst then Maybe.just snd else findNaive x L

    findFastHelper : (key start end : ℕ) → (L : List (Pair ℕ A)) → (boundsGood L start) → (boundsGood L end) → Maybe A
    findFastHelper key start end [] startBoundGood endBoundGood = Maybe.nothing
    findFastHelper key start end (x₁ :: L) startBoundGood endBoundGood = cmpLifted (1st halfNth) equal key then (λ x → Maybe.just (2nd halfNth))
      ge (λ x' → ifLifted start equal end then (λ _ → Maybe.nothing) else λ x → findFastHelper key start middleOfSearch (x₁ :: L) startBoundGood {!!})
      le  λ x' → ifLifted start equal end then (λ _ → Maybe.nothing) else λ x → findFastHelper key middleOfSearch end (x₁ :: L) {!!} endBoundGood where
     -- ifLifted start equal end then {!!} else {!!} where
      middleOfSearch : ℕ
      middleOfSearch = (start + end) div 2 withP refl -- note: proof might slow things down, maybe remove later?
      halfNthMaybe : Maybe (Pair ℕ A)
      halfNthMaybe = nth middleOfSearch (x₁ :: L)
      lengthOfL : ℕ
      lengthOfL = length (x₁ :: L)
      halfNth : Pair ℕ A
      halfNth = isJustExtract halfNthMaybe (nthLengthGood' (x₁ :: L) middleOfSearch lengthOfL (equalIsTrue (length L)) {!!})
      boundsPreservedByMiddleLem : (n m middle : ℕ) → boundsGood (x₁ :: L) n → boundsGood (x₁ :: L) m → (middle ≡ (n + m) div 2 withP refl) → boundsGood (x₁ :: L) middle
      boundsPreservedByMiddleLem zero zero middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L) x) (sym middleRefl) tt
      boundsPreservedByMiddleLem zero (suc m) middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L) x) (sym middleRefl) {!tt!}
      boundsPreservedByMiddleLem (suc n) zero middle nBoundGood mBoundGood middleRefl = {!!}
      boundsPreservedByMiddleLem (suc n) (suc m) middle nBoundGood mBoundGood middleRefl = {!!}
      boundsPreservedByMiddle : boundsGood (x₁ :: L) middleOfSearch
      boundsPreservedByMiddle = {!tt!}

    findFast : (x : ℕ) → (L : List (Pair ℕ A)) → Maybe A
    findFast x [] = Maybe.nothing
    findFast x (x₁ :: L) = findFastHelper x 0 (length L) (x₁ :: L) tt {!tt!}
    {--
    findFast x [] = Maybe.nothing
    findFast x (x' :: l) = {!!} where
      halfOfLengthOfL : ℕ
      halfOfLengthOfL = lengthOfL div 2 withP refl  where
        lengthOfL : ℕ
        lengthOfL = length l
      --}

    -- insert : (x : ℕ) → (y : A) → (L : List (Pair ℕ A)) → (List (Pair ℕ A))
    -- insert x y [] =  (x , y) :: []
    -- insert x y ((x' , y') :: L) = if x == x' then ((x , y) :: L) else {!!}

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
    removeNextVal : (x : ℕ) → (L : Tree A) → isEmpty L ≡ false → Pair (Tree A) (Pair ℕ A)
    removeNextVal x null proofNotEmpty = Cubical.Data.Empty.elim {A = λ _ → Pair (Tree A) (Pair ℕ A)} (true≢false proofNotEmpty)
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

    delete : (x : ℕ) → (L : Tree A) → Tree A
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


    -- commented out to make things compile
    -- sucMaybe : Maybe A -> Maybe A
    -- sucMaybe (just x) = just {!suc x!}
    -- sucMaybe nothing = {!!}


    -- commented out to make things compile
    -- insertFindGood : (k : ℕ) (v : A) (l : Tree A) → find k (insert k v l) ≡ Maybe.just v
    -- insertFindGood k v null = ifElimTrue (just v) nothing (k == k) (equalIsTrue k)
    -- insertFindGood k v (leaf (k' , v')) = {!!}
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
    -- insertFindGood k v (node x l l₁) = {!!}

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
