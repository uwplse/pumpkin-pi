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

test : ℕ → ℕ
test x = x

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

    -- we need the values to have decidable equality to define the quotient relation
    sorted : (l : List (Pair ℕ ℕ)) → Type
    sorted [] = ⊤
    sorted (x :: []) = ⊤
    sorted ((zero , snd) :: ((fst' , snd') :: l)) = sorted ((fst' , snd') :: l)
    sorted ((suc fst , snd) :: ((zero , snd') :: l)) = ⊥
    sorted ((suc fst , snd) :: ((suc fst' , snd') :: l)) = sorted ((fst , snd) :: ((fst' , snd') :: l))

    insertionSort : (k : ℕ ) → (v : ℕ ) →  List (Pair ℕ ℕ) → List (Pair ℕ ℕ)
    insertionSort k v [] = (k , v) :: []
    insertionSort k v ((k' , v') :: l) with (k == k')
    ...                                   | true = (k , v) :: ((k' , v') :: l)
    ...                                   | false with (k < k')
    ...                                     | true =  (k , v) :: ((k' , v') :: l)
    ...                                     | false = (k' , v') :: insertionSort k v l

    sort : List (Pair ℕ ℕ) → List (Pair ℕ ℕ)
    sort [] = []
    sort ((fst₁ , snd₁) :: l) = insertionSort fst₁ snd₁ (sort l)

    listEqual : List (Pair ℕ ℕ) → List (Pair ℕ ℕ) → Type
    listEqual [] [] = ⊤
    listEqual [] (x :: l') = ⊥
    listEqual (x :: l) [] = ⊥
    listEqual ((zero , zero) :: l) ((zero , zero) :: l') = listEqual l l'
    listEqual ((zero , zero) :: l) ((zero , suc snd') :: l') = ⊥
    listEqual ((zero , suc snd₁) :: l) ((zero , zero) :: l') = ⊥
    listEqual ((zero , suc snd₁) :: l) ((zero , suc snd') :: l') = listEqual ((zero , snd₁) :: l) ((zero , snd') :: l')
    listEqual ((zero , snd) :: l) ((suc fst' , snd') :: l') = ⊥
    listEqual ((suc fst₁ , snd) :: l) ((zero , snd') :: l') = ⊥
    listEqual ((suc fst₁ , snd) :: l) ((suc fst' , snd') :: l') = listEqual ((fst₁ , snd) :: l) ((fst' , snd') :: l')

    rSort : (List (Pair ℕ ℕ)) → (List (Pair ℕ ℕ)) → Type
    rSort l l' = listEqual (sort l) (sort l')

    isSetList/sort : isSet (List (Pair ℕ ℕ) / rSort)
    isSetList/sort = squash/

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

    data FuelStatus (a : Set) : Set where
      outOfFuel : FuelStatus a
      hasFuel   : a -> FuelStatus a

    isFueled : FuelStatus (Maybe A) → Type
    isFueled outOfFuel = ⊥
    isFueled (hasFuel x) = ⊤

    findFastHelper : (key start end : ℕ) → (L : List (Pair ℕ A)) → (fuel : ℕ) → FuelStatus (Maybe A)
    findFastHelper key start end [] fuel = hasFuel Maybe.nothing
    findFastHelper key start end (x₁ :: L) 0 = outOfFuel
    findFastHelper key start end (x₁ :: L) (suc fuel) with (let middleOfSearch = ((start + end) div 2) in
                                                      (nth middleOfSearch (x₁ :: L)))
    ...                                               | Maybe.just (fst , snd) with (key == fst) | (key < fst)
    ...                                                 | true | _ = hasFuel (Maybe.just snd)
    ...                                                 | false | true = findFastHelper key start (let middleOfSearch = ((start + end) div 2 withP refl) in middleOfSearch) (x₁ :: L) fuel -- key is in first half
    ...                                                 | false | false = findFastHelper key (let middleOfSearch = ((start + end) div 2 withP refl) in middleOfSearch) end (x₁ :: L) fuel -- key is in second half
    findFastHelper key start end (x₁ :: L) (suc fuel) | Maybe.nothing = hasFuel Maybe.nothing

    -- if cmpLifted (1st {!!}) equal key then (λ x → Maybe.just (2nd {!!}))
    --   ge (λ x' → ifLifted start equal end then (λ _ → Maybe.nothing) else λ x → findFastHelper key start middleOfSearch (x₁ :: L) fuel )
    --   le  λ x' → ifLifted start equal end then (λ _ → Maybe.nothing) else λ x → findFastHelper key middleOfSearch end (x₁ :: L) fuel where
    --   middleOfSearch : ℕ
    --   middleOfSearch = (start + end) div 2 withP refl -- note: proof might slow things down, maybe remove later?
    --   halfNth : Maybe (Pair ℕ A)
    --   halfNth = {!!}
    -- proofs should get erased at compile-time, hopefully
    -- findFastHelper : (key start end : ℕ) → (L : List (Pair ℕ A)) → (fuel : ℕ) → ((fuel == 0) ≡ false) → (boundsGood L start) → (boundsGood L end) → Maybe A
    findFastHelperWithP : (key start end : ℕ) → (L : List (Pair ℕ A)) → (fuel : ℕ) → (((end - start) < fuel) ≡ true) → (boundsGood L start) → (boundsGood L end) → Maybe A
    findFastHelperWithP key start end [] fuel fuelNotEmpty startBoundGood endBoundGood = Maybe.nothing
    findFastHelperWithP key start end (x₁ :: L) 0 fuelNotEmpty startBoundGood endBoundGood = Cubical.Data.Empty.elim {A = λ _ → Maybe A} (true≢false (sym fuelNotEmpty))
    findFastHelperWithP key start end (x₁ :: L) (suc fuel) fuelNotEmpty startBoundGood endBoundGood = cmpLifted (1st halfNth) equal key then (λ x → Maybe.just (2nd halfNth))
      ge (λ x' → ifLifted start equal end then (λ _ → Maybe.nothing) else λ x → findFastHelperWithP key start middleOfSearch (x₁ :: L) fuel {!!} startBoundGood boundsPreservedByMiddle)
      le  λ x' → ifLifted start equal end then (λ _ → Maybe.nothing) else λ x → findFastHelperWithP key middleOfSearch end (x₁ :: L) fuel {!!} boundsPreservedByMiddle endBoundGood where
     -- ifLifted start equal end then {!!} else {!!} where
      middleOfSearch : ℕ
      middleOfSearch = (start + end) div 2 withP refl -- note: proof might slow things down, maybe remove later?
      lengthOfL : ℕ
      lengthOfL = length (x₁ :: L)

      div2AlwaysSmaller : (n : ℕ) → ((n == 0) ≡ false) → (n div 2 withP refl < n) ≡ true
      div2AlwaysSmaller zero notZeroProof = Cubical.Data.Empty.elim {A = λ _ → (zero div 2 withP refl < zero) ≡ true} (true≢false notZeroProof)
      div2AlwaysSmaller (suc zero) notZeroProof = refl
      div2AlwaysSmaller (suc (suc zero)) notZeroProof = refl
      div2AlwaysSmaller (suc (suc (suc n))) notZeroProof = cong (λ a → {!!}) (div2AlwaysSmaller (suc n) refl) -- {!!} ∙ div2AlwaysSmaller (suc n) refl ∙ refl

      sucSucDiv2IsJustSuc : (n m : ℕ) → (suc n + suc m) div 2 withP refl ≡ suc ((n + m) div 2 withP refl) -- (s n + s m) / 2 = s ((n + m) /2)
      sucSucDiv2IsJustSuc zero zero = refl
      sucSucDiv2IsJustSuc (suc n) zero = {!!} ∙ (sucSucDiv2IsJustSuc zero (suc n)) ∙ cong (λ a → suc (div-helper 0 1 a 0)) (sym (+-comm n zero))
      sucSucDiv2IsJustSuc zero (suc m) = sucSucDiv2IsJustSuc 1 m
      -- +-comm n zero
      sucSucDiv2IsJustSuc (suc n) (suc m) = {!!}

      boundsPreservedByMiddleLem : (n m middle : ℕ) → boundsGood (x₁ :: L) n → boundsGood (x₁ :: L) m → (middle ≡ (n + m) div 2 withP refl) → boundsGood (x₁ :: L) middle
      boundsPreservedByMiddleLem zero zero middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L) x) (sym middleRefl) tt
      boundsPreservedByMiddleLem zero (suc zero) middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L) x) (sym middleRefl) tt
      boundsPreservedByMiddleLem zero (suc (suc m)) middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L) x) (sym middleRefl) {!!}
-- subst : {y..1 : Level} {A = A₁ : Type y..1} {ℓ' : Level}
-- {x = x₂ : A₁} {y : A₁} (B : A₁ → Type ℓ') →
-- x₂ ≡ y → B x₂ → B y
-- Goal: boundsGood (x₁ :: L) (div-helper 0 1 (n + zero) 0)
      boundsPreservedByMiddleLem (suc n) zero middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L) x) (sym middleRefl)
                                                      (subst (λ x' → boundsGood (x₁ :: L) (div-helper 0 1 x' 0)) (sym (+-comm n zero))
-- middle != div-helper 0 1 n 0 of type ℕ
                                                      (boundsPreservedByMiddleLem zero (suc n) {!!} mBoundGood nBoundGood ({!!}∙ middleRefl ∙ cong (λ x → div-helper 0 1 x 0) (+-comm n zero)))) --  (+-comm n zero) (boundsPreservedByMiddleLem zero (suc n) middle mBoundGood nBoundGood (middleRefl ∙ cong (λ x → div-helper 0 1 x 0) (+-comm n zero))))
      boundsPreservedByMiddleLem (suc n) (suc m) middle nBoundGood mBoundGood middleRefl = subst (λ x → boundsGood (x₁ :: L ) x) (sym (sucSucDiv2IsJustSuc n m) ∙ sym middleRefl ∙ refl) {!!}

      boundsPreservedByMiddle : boundsGood (x₁ :: L) middleOfSearch
      boundsPreservedByMiddle = boundsPreservedByMiddleLem start end middleOfSearch startBoundGood endBoundGood refl
      halfNthMaybe : Maybe (Pair ℕ A)
      halfNthMaybe = nth middleOfSearch (x₁ :: L)
      halfNth : Pair ℕ A
      halfNth = isJustExtract halfNthMaybe (nthLengthGood (x₁ :: L) middleOfSearch boundsPreservedByMiddle)



    findFast : (x : ℕ) → (L : List (Pair ℕ A)) → FuelStatus (Maybe A)
    findFast x [] = hasFuel (Maybe.nothing)
    findFast x (x₁ :: L) = findFastHelper x 0 (length L) (x₁ :: L) (length (x₁ :: L))

    findFastNeverRunOutOfFuel : (x : ℕ) → (L : List (Pair ℕ A)) → isFueled (findFast x L)
    findFastNeverRunOutOfFuel x [] = tt
    findFastNeverRunOutOfFuel x (x₁ :: L) = {!!}

    isFueledExtract : (a : FuelStatus (Maybe A)) → isFueled a → Maybe A
    isFueledExtract (hasFuel x₁) x = x₁

    findFastExtracted : (x : ℕ) → (L : List (Pair ℕ A)) → Maybe A
    findFastExtracted x l = isFueledExtract (findFast x l) (findFastNeverRunOutOfFuel x l)



    -- findFast x (x₁ :: L) = findFastHelperWithP x 0 (length L) (x₁ :: L) (length (x₁ :: L)) (sucAlwaysGreater (length (x₁ :: L))) tt {!tt!} where
    --   sucAlwaysGreater : (n : ℕ) → (n < suc n) ≡ true
    --   sucAlwaysGreater zero = refl
    --   sucAlwaysGreater (suc n) = sucAlwaysGreater n
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
