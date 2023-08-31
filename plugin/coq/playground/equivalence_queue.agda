{-# OPTIONS --safe --cubical #-}
module equivalence_queue where

open import Cubical.Core.Everything
open import Cubical.HITs.SetQuotients as SetQuotients
open import Cubical.Foundations.HLevels
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
open import Cubical.Data.Maybe
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Bool.Properties
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Prod
open import Cubical.Data.Bool
open import Cubical.Data.List
-- open import Agda.Builtin.Equality renaming (_≡_ to _≡'_; refl to refl')

record Queue {ℓ} : Set (ℓ-suc ℓ) where
-- record Queue {ℓ} (A : Set ℓ) : Set (ℓ-suc ℓ) where
  field
    A : Set ℓ
    Q : Set ℓ
    null : Q
    enqueue : A → Q → Q
    dequeue : Q → Maybe (Q × A) -- similiar to the Cubical lib def but with Maybe bc monads


module OneList where
    Q = List ℕ
    A = ℕ

    bind : (Maybe (Q × A)) → ((Q × A) → (Maybe (Q × A))) → Maybe (Q × A)
    bind (just x) f = f x
    bind nothing f = nothing

    last : Q → Maybe (Q × A)
    last [] = nothing
    last (x ∷ []) = just ([] ,  x)
    last (x ∷ (x₁ ∷ x')) = bind (last (x₁ ∷ x')) (help x)
       where
       help : A → (Q × A) → (Maybe (Q × A))
       help x (xs , res) = just ((x ∷ xs) , res)

    enqueue : A → Q → Q
    enqueue x x' = x ∷ x'

    dequeue : Q → Maybe (Q × A)
    dequeue [] = nothing
    dequeue (x ∷ xs) with (dequeue xs)
    ...                    | nothing = just ([] , x)
    ...                    | just (q , a) = just (x ∷ q , a)

    OneList = record { A = A; Q = Q ; null = [] ; enqueue = enqueue; dequeue = dequeue}

    depConstrEmpty : Q
    depConstrEmpty = []

    depConstrInsert : A → Q → Q
    depConstrInsert x x' = x ∷ x'

    enqueueDequeueEmptyOk : (a : A) → dequeue (enqueue a depConstrEmpty) ≡ just (depConstrEmpty , a)
    enqueueDequeueEmptyOk a = refl

    depElimOneList : (P : Q -> Type) -> (P depConstrEmpty) -> (∀ a q -> (P q) -> P (depConstrInsert a q)) -> ((x : Q) -> P x)
    depElimOneList P baseCase consCase [] = baseCase
    depElimOneList P baseCase consCase (x ∷ l) = consCase x l (depElimOneList P baseCase consCase l)


    isSetQ : isSet Q
    isSetQ = isOfHLevelList 0 isSetℕ

module TwoList where
    Q = (List ℕ × List ℕ)
    A = ℕ

    dequeue : Q → Maybe (Q × A)
    dequeue (x , []) = let xs = rev x in help xs where
      help : List A → Maybe (Q × A)
      help [] = nothing
      help (x ∷ x₁) = just ((([] , x₁)), x)
    dequeue (x , (x₁ ∷ x')) = just ((((x , x')) , x₁))

    enqueue : A → Q → Q
    enqueue x (x₁ , x₂) = (x ∷ x₁ , x₂)

    TwoList = record { A = A; Q = Q; null = ([] , []); enqueue = enqueue ; dequeue = dequeue }

    insOrder : Q → List A
    insOrder (l1 , l2) = l1 ++ (rev l2)

    canonicalize : Q → Q
    canonicalize q = (insOrder q , [])

    insOrderCanonicalizeResp : (q : Q) → insOrder q ≡ insOrder (canonicalize q)
    insOrderCanonicalizeResp q = sym (++-unit-r (insOrder q))

    isEmpty : List ℕ → Bool
    isEmpty [] = true
    isEmpty (x ∷ x₁) = false

    head : List ℕ → ℕ
    head [] = 0
    head (x ∷ x₁) = x
    tail : List ℕ → List ℕ
    tail [] = []
    tail (x ∷ xs) = xs

    last : List ℕ → ℕ
    last [] = 0
    last (x ∷ []) = x
    last (x ∷ xs ∷ xs') = last (xs ∷ xs')
    allButLast : List ℕ → List ℕ
    allButLast [] = []
    allButLast (x ∷ []) = []
    allButLast (x ∷ xs ∷ xs') = x ∷ allButLast (xs ∷ xs')

    π₁ : Q → List ℕ
    π₁ (x , x₁) = x
    π₂ : Q → List ℕ
    π₂ (x , x₁) = x₁

    R : Q → Q → Type
    R q1 q2 = insOrder q1 ≡ insOrder q2

    TLQ : Type
    TLQ = Q / R

    depConstrEmpty : Q / R
    depConstrEmpty = _/_.[ ([] , []) ]

    canonicalizeResp : (q : Q) → _/_.[_] {R = R} q ≡ _/_.[ canonicalize q ]
    canonicalizeResp (l1 , l2) = eq/ (l1 , l2) (canonicalize (l1 , l2)) (insOrderCanonicalizeResp (l1 , l2))

    canonicalizeResp⁻ : (q : Q) → _/_.[ canonicalize q ] ≡ _/_.[_] {R = R} q
    canonicalizeResp⁻ q = sym (canonicalizeResp q)

    canonicalizeIdempotent : (q : Q) →  canonicalize q ≡ canonicalize (canonicalize q)
    canonicalizeIdempotent q = ×≡ (sym (++-unit-r (insOrder q))) refl

    enqCanonicalResp : (a : A) → (q : Q) → _/_.[_] {R = R} (enqueue a q) ≡ _/_.[ enqueue a (canonicalize q) ]
    enqCanonicalResp a (l1 , l2) = {!!}

    insOrderCons : (a : A) → (l1 l2 : List A) → a ∷ insOrder (l1 , l2) ≡ insOrder (a ∷ l1 , l2)
    insOrderCons a l1 l2 = refl

    insOrderEnq : (a : A) → (q : Q) → a ∷ insOrder q ≡ insOrder (enqueue a q)
    insOrderEnq a (l1 , l2) = refl

    enqResp : (a : A) → (q1 q2 : Q) → R q1 q2 → _/_.[_] {R = R} (enqueue a q1) ≡ _/_.[ enqueue a q2 ]
    enqResp a (l1 , l2) (l3 , l4) r = eq/ (a ∷ l1 , l2) (a ∷ l3 , l4) (cong (λ l → a ∷ l) r)

    depConstrInsert : A → (Q / R) → (Q / R)
    depConstrInsert a = SetQuotients.rec squash/ (λ q → _/_.[ enqueue a q ] ) (enqResp a)

    isSetProd : ∀ {A : Type} {B : A → Type} → (∀ (a : A) → isSet (B a)) → isSet (∀ (a : A) → B a)
    isSetProd {A} {B} setB = λ (f g : ∀ (a : A) → B a) (p q : f ≡ g) → cong funExt (funExt (λ (a : A) → setB a (f a) (g a) (funExt⁻ p a) (funExt⁻ q a)))

    isSetFunc : {A B : Set} → isSet A → isSet B → isSet (A → B)
    isSetFunc {A} {B} setA setB = isSetProd {B = λ _ → B} (λ _ → setB)

    isSetFunc' : {A : Set} (B : A → Set) → ((a : A) → isSet (B a)) → isSet ((a : A) → (B a))
    isSetFunc' {A} B resultIsSet = isSetProd resultIsSet

    revSwap : (l : List ℕ ) → _/_.[_] (rev l , []) ≡ _/_.[ [] , l ]
    revSwap l = refl

    lem : (P : (Q / R) → Set) → P depConstrEmpty → ((q : Q / R) → (a : A) → P q → P (depConstrInsert a q)) → (l : List A) → P _/_.[ (l , []) ]
    lem P baseCase insertCase [] = baseCase
    lem P baseCase insertCase (a ∷ l) = insertCase _/_.[ l , [] ] a (lem P baseCase insertCase l)

    depElimQ : (P : (Q / R) → Set) → (∀ x → isSet (P x)) → P depConstrEmpty → ((q : Q / R) → (a : A) → P q → P (depConstrInsert a q)) → ∀ q' → P q'
    depElimQ P set baseCase insertCase = SetQuotients.elim set func wellDefined where
      func : (q : Q) → P _/_.[ q ]
      func q = transport (cong P (canonicalizeResp⁻ q)) (lem P baseCase insertCase (insOrder q))
      lem2 : (q : Q) → PathP (λ i → P ((canonicalizeResp⁻ q) i)) (lem P baseCase insertCase (insOrder q)) (transport (cong P (sym (canonicalizeResp q))) (lem P baseCase insertCase (insOrder q)))
      lem2 q = transport-filler (cong P (canonicalizeResp⁻ q)) (lem P baseCase insertCase (insOrder q))
      lemResp : (q1 q2 : Q) → (r : R q1 q2) → PathP (λ i → P (cong (λ l → _/_.[ (l , []) ]) r i)) (lem P baseCase insertCase (insOrder q1)) (lem P baseCase insertCase (insOrder q2))
      lemResp q1 q2 r = congP (λ i a → lem P baseCase insertCase a) r
      -- lem4 : (q1 q2 : Q) → (r : R q1 q2) → PathP (λ i → P ((cong (λ l → _/_.[ (l , []) ]) r ∙ canonicalizeResp⁻ q2) i)) (lem (insOrder q1)) (func q2)
      -- lem4 q1 q2 r = compPathP' {B = P} {p = cong (λ l → _/_.[ (l , []) ]) r} {q = canonicalizeResp⁻ q2} (lemResp q1 q2 r) (lem2 q2)
      composedPaths : (q1 q2 : Q) → (r : R q1 q2) → PathP (λ i → P (((canonicalizeResp q1) ∙ (λ j → _/_.[ (r j , []) ]) ∙ (canonicalizeResp⁻ q2)) i)) (func q1) (func q2)
      composedPaths q1 q2 r = compPathP' {B = P} (symP (lem2 q1)) (compPathP' {B = P} (lemResp q1 q2 r) (lem2 q2))
      pathsEq : (q1 q2 : Q) → (r : R q1 q2) → ((canonicalizeResp q1) ∙ (λ j → _/_.[ (r j , []) ]) ∙ (canonicalizeResp⁻ q2)) ≡ eq/ q1 q2 r
      pathsEq q1 q2 r = squash/ _/_.[ q1 ] _/_.[ q2 ] _ _
      typesSame : (q1 q2 : Q) → (r : R q1 q2) →
        PathP (λ i → P (((canonicalizeResp q1) ∙ (λ j → _/_.[ (r j , []) ]) ∙ (canonicalizeResp⁻ q2)) i)) (func q1) (func q2)
        ≡ PathP (λ i → P (eq/ q1 q2 r i)) (func q1) (func q2)
      typesSame q1 q2 r = cong (λ x → PathP (λ i → P (x i)) (func q1) (func q2)) (pathsEq q1 q2 r)
      wellDefined : (q1 q2 : Q) (r : R q1 q2) → PathP (λ i → P (eq/ q1 q2 r i)) (func q1) (func q2)
      wellDefined q1 q2 r = transport (typesSame q1 q2 r) (composedPaths q1 q2 r)

    ιTLQEmptyEq : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrInsert a q)) →
      depElimQ P pset emptyP insertP depConstrEmpty ≡ emptyP
    ιTLQEmptyEq P pset emptyP insertP =
      cong
        (λ x → transport (λ i → P (x i)) emptyP)
        (squash/ {R = R}
          depConstrEmpty
          depConstrEmpty
          (sym (eq/ ([] , []) ([] , []) refl))
          refl)
      ∙ transportRefl emptyP

    ιTLQEmpty : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrInsert a q)) →
      (Q : P depConstrEmpty → Set) → Q (depElimQ P pset emptyP insertP depConstrEmpty) → Q emptyP
    ιTLQEmpty P pset emptyP insertP Q Qp = transport (cong Q (ιTLQEmptyEq P pset emptyP insertP)) Qp

    ιTLQEmpty⁻ : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrInsert a q)) →
      (Q : P depConstrEmpty → Set) → Q emptyP → Q (depElimQ P pset emptyP insertP depConstrEmpty)
    ιTLQEmpty⁻ P pset emptyP insertP Q Qp = transport (cong Q (sym (ιTLQEmptyEq P pset emptyP insertP))) Qp

    ιTLQInsertEq : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrInsert a q)) →
      (a : A) → (q : TLQ) →
      depElimQ P pset emptyP insertP (depConstrInsert a q)
      ≡ insertP q a (depElimQ P pset emptyP insertP q)
    ιTLQInsertEq P pset emptyP insertP a =
      SetQuotients.elim
        (λ x → isProp→isSet ((pset (depConstrInsert a x)) (depElimQ P pset emptyP insertP (depConstrInsert a x)) (insertP x a (depElimQ P pset emptyP insertP x))) )
        (λ q → lem3 q)
        λ q1 q2 r → {!!} where
      lem3 : (q : Q) → transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                         (lem P emptyP insertP
                           (insOrder (enqueue a q)))
                       ≡ insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (lem P emptyP insertP (insOrder q)))
      lem3 q = {!!}

    enqueue/R : A → TLQ → TLQ
    enqueue/R x _/_.[ a ] = _/_.[ enqueue x a ]
    enqueue/R x (eq/ a b r i) =  ?
    enqueue/R x (squash/ q q₁ p q₂ i i₁) = {!!}

    dequeue/R : TLQ → Maybe (TLQ × A)
    dequeue/R _/_.[ a ] = {! !}
    dequeue/R (eq/ a b r i) = {!!}
    dequeue/R (squash/ x x₁ p q i i₁) = {!!}

    enqueueDequeueEmptyOk : (a : A) → dequeue/R (enqueue/R a depConstrEmpty) ≡ just (depConstrEmpty , a)
    enqueueDequeueEmptyOk a = {!!}


    -- OneListIsoTwoList : Iso OneList.Q Q
    -- Iso.fun OneListIsoTwoList = canonicalizeInv
    -- Iso.inv OneListIsoTwoList = canonicalize
    -- Iso.rightInv OneListIsoTwoList ([] , []) = refl
    -- Iso.rightInv OneListIsoTwoList ([] , (x ∷ x')) = congPath (λ a → help x a) (Iso.rightInv OneListIsoTwoList ([] , x')) where
    --   help : A → Q → Q
    --   help x (x₁ , x₂) = (x₁ , {!x ∷ {!!}!})
    -- Iso.rightInv OneListIsoTwoList ((x ∷ x₂) , x₁) = {!!}
    -- Iso.leftInv OneListIsoTwoList [] = refl
    -- Iso.leftInv OneListIsoTwoList (x ∷ a) = {!!}

{-
    quotientCanonicalizeLifted : (a b : Q) → quotient a b → canonicalize a ≡ canonicalize b
    quotientCanonicalizeLifted a b x = canonicalizeInvEquiv (canonicalize a) (canonicalize b) (quotientGenCanonLifted a b x)
-}

    -- canonicalizeQ : (Q / quotient) → OneList.Q
    -- canonicalizeQ [ a ] = canonicalize a
    -- canonicalizeQ (eq/ a b r i) = canonicalizeInvEquiv (canonicalize a) (canonicalize b) (quotientGenCanonLifted a b r) i
    -- canonicalizeQ (squash/ a b p q i j) = canonicalizeInvEquiv
    --   (canonicalizeInvEquiv (canonicalizeQ a) (canonicalizeQ b) (cong canonicalizeInv {!!}) i)
    --   (canonicalizeInvEquiv (canonicalizeQ a) (canonicalizeQ b) (cong canonicalizeInv {!!}) i)
    --   refl
    --   j where
    --     help : p ≡ q
    --     help = squash/ a b p q
    -- canonicalizeQ : (Q / quotient) → OneList.Q
    -- canonicalizeQ = SetQuotients.rec OneList.isSetQ canonicalize quotientCanonicalizeLifted

{-
    canonicalizeInvQ : OneList.Q → (Q / quotient)
    canonicalizeInvQ x = _/_.[ canonicalizeInv x ]

    OneListIsoTwoList' : Iso OneList.Q (Q / quotient)
    Iso.fun OneListIsoTwoList' = canonicalizeInvQ
    Iso.inv OneListIsoTwoList' = canonicalizeQ
    Iso.rightInv OneListIsoTwoList' [ a ] = eq/ (genCanon a) a (defEquivLLower (canonicalize a ++ []) (canonicalize a) (++-unit-r (canonicalize a)))
    Iso.rightInv OneListIsoTwoList' (eq/ a b r i) = {!!}
-- canonicalizeInvQ (canonicalizeQ (eq/ a b r i)) ≡ eq/ a b r i
-- _/_.[ canonicalizeInv (canonicalizeQ (eq/ a b r i)) ] ≡ eq/ a b r i
-- _/_.[ [] , π₂ (defEquivQLifted ([] , canonicalize a) ([] , canonicalize b) r i) ] ≡ eq/ a b r i
-- _/_.[ [] , π₂ (defEquivQLifted ([] , canonicalize a) ([] , canonicalize b) r i) ] ≡ eq/ a b r i
    Iso.rightInv OneListIsoTwoList' (squash/ b b₁ p q i i₁) = {!!}
    Iso.leftInv OneListIsoTwoList' a = ++-unit-r a
-}
