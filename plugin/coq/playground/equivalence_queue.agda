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

ListRec : {A C : Set} →
  C →
  ((a : A) (l : List A) → C → C) →
  (l : List A) → C
ListRec emptyC insertC [] = emptyC
ListRec emptyC insertC (a ∷ l) = insertC a l (ListRec emptyC insertC l)

ListElim : {A : Set} (P : List A → Set) →
  P [] →
  ((a : A) (l : List A) → P l → P (a ∷ l)) →
  (l : List A) → P l
ListElim P emptyP insertP [] = emptyP
ListElim P emptyP insertP (a ∷ l) = insertP a l (ListElim P emptyP insertP l)

congMaybeRec : {T1 T2 T3 : Set} (a : T1) (b : T3 → T1) (m : Maybe T3) (f : T1 → T2) → (Cubical.Data.Maybe.rec (f a) (λ x → f (b x)) m) ≡ f (Cubical.Data.Maybe.rec a (λ x → b x) m)
congMaybeRec a b m f =
  Cubical.Data.Maybe.elim
    (λ m → (Cubical.Data.Maybe.rec (f a) (λ x → f (b x)) m) ≡ f (Cubical.Data.Maybe.rec a (λ x → b x) m))
    refl
    (λ _ → refl)
    m

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

    enqueue' : A → Q → Q
    enqueue' x x' = x ∷ x'

    dequeue' : Q → Maybe (Q × A)
    dequeue' [] = nothing
    dequeue' (x ∷ xs) with (dequeue' xs)
    ...                    | nothing = just ([] , x)
    ...                    | just (q , a) = just (x ∷ q , a)


    depConstrEmpty : Q
    depConstrEmpty = []

    depConstrInsert : A → Q → Q
    depConstrInsert a q = a ∷ q

    depElimOneList : (P : Q -> Type) -> (P depConstrEmpty) -> (∀ q a -> (P q) -> P (depConstrInsert a q)) -> ((x : Q) -> P x)
    depElimOneList P baseCase consCase [] = baseCase
    depElimOneList P baseCase consCase (x ∷ l) = consCase l x (depElimOneList P baseCase consCase l)

    ιOneListInsertEq : (P : Q → Set) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : Q) → (a : A) → (P q) → P (depConstrInsert a q)) →
      (a : A) → (q : Q) →
      depElimOneList P emptyP insertP (depConstrInsert a q)
      ≡ insertP q a (depElimOneList P emptyP insertP q)
    ιOneListInsertEq P pset emptyP insertP a = refl

    enqueue : A → Q → Q
    enqueue = depConstrInsert

    dequeue : Q → Maybe (Q × A)
    dequeue = depElimOneList (λ _ → Maybe (Q × A)) nothing recCase where
      recCase : (q : Q) (outer : A) → Maybe (Q × A) → Maybe (Q × A)
      recCase q outer m =
        Cubical.Data.Maybe.rec
          (just (depConstrEmpty , outer))
          (λ p → just (depConstrInsert outer (proj₁ p) , (proj₂ p)))
          m

    isEmpty : Q → Bool
    isEmpty = depElimOneList (λ _ → Bool) true (λ _ _ _ →  false)

    emptyTrueOk : isEmpty depConstrEmpty ≡ true
    emptyTrueOk = refl

    emptyFalseOk : (a : A) (q : Q) → isEmpty (depConstrInsert a q) ≡ false
    emptyFalseOk a = depElimOneList (λ x → isEmpty (depConstrInsert a x) ≡ false) refl (λ q₁ a₁ x i → x i)

    implTest1 : dequeue (enqueue 2 (enqueue 1 [])) ≡ just (enqueue 2 [] , 1)
    implTest1 = refl

    enqueueDequeueEmptyOk : (a : A) → dequeue (enqueue a depConstrEmpty) ≡ just (depConstrEmpty , a)
    enqueueDequeueEmptyOk a = refl

    --dequeueEnqueue formulation from "Internalizing Representation Independence with Univalence" by Angiuli et al.
    returnOrEnq : A → Maybe (Q × A) → Q × A
    returnOrEnq a m = Cubical.Data.Maybe.rec (depConstrEmpty , a) (λ p → (enqueue a (proj₁ p) , proj₂ p)) m

    dequeueEnqueue : (a : A) (q : Q) → dequeue (enqueue a q) ≡ just (returnOrEnq a (dequeue q))
    dequeueEnqueue a q =
      congMaybeRec
        (depConstrEmpty , a)
        (λ p → ((depConstrInsert a (proj₁ p)) , proj₂ p))
        (depElimOneList
          (λ _ → Maybe (Q × ℕ))
          nothing
          (λ q₁ outer m →
            Cubical.Data.Maybe.rec (just (depConstrEmpty , outer))
            (λ p → just ((depConstrInsert outer (proj₁ p)) , proj₂ p)) m)
        q)
        just

    OneList = record { A = A; Q = Q ; null = [] ; enqueue = enqueue; dequeue = dequeue}

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

    lem : (P : (Q / R) → Set) → P depConstrEmpty → ((q : Q / R) → (a : A) → P q → P (depConstrInsert a q)) → (l : List A) → P _/_.[ (l , []) ]
    lem P baseCase insertCase [] = baseCase
    lem P baseCase insertCase (a ∷ l) = insertCase _/_.[ l , [] ] a (lem P baseCase insertCase l)

    depRecQ : {C : Set} → (isSet C) → C → ((q : TLQ) (a : A) → C → C) → TLQ → C
    depRecQ {C} set empty insert = SetQuotients.rec set func wellDefined where
      help : (C : Set) → C → ((q : Q / R) → (a : A) → C → C) → (l : List A) → C
      help C baseCase insertCase [] = baseCase
      help C baseCase insertCase (a ∷ l) = insertCase _/_.[ l , [] ] a (help C baseCase insertCase l)
      func : (q : Q) → C
      func q = help C empty insert (insOrder q)
      wellDefined : (q1 q2 : Q) → R q1 q2 → func q1 ≡ func q2
      wellDefined q1 q2 r = cong (λ q → help C empty insert q) r
      
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
      SetQuotients.elimProp
        (λ x → ((pset (depConstrInsert a x)) (depElimQ P pset emptyP insertP (depConstrInsert a x)) (insertP x a (depElimQ P pset emptyP insertP x))) )
        (λ q → lem3 q) where
      lem5 : (q : Q) → PathP
                         (λ i → P (canonicalizeResp q (~ i)))      
                         (lem P emptyP insertP (insOrder q))
                         (transport
                           (λ i → P (canonicalizeResp q (~ i)))
                           (lem P emptyP insertP (insOrder q)))
      lem5 q = transport-filler (cong P (canonicalizeResp⁻ q)) (lem P emptyP insertP (insOrder q))
      lem4 : (q : Q) → PathP
                         (λ i → P (canonicalizeResp (enqueue a q) i))
                         (transport
                           (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                           (lem P emptyP insertP (insOrder (enqueue a q))))      
                         (lem P emptyP insertP (insOrder (enqueue a q)))
      lem4 q = symP (lem5 (enqueue a q))
      lem6 : (q : Q) → PathP
                         (λ i → P (depConstrInsert a (canonicalizeResp q (~ i))))
                         (insertP _/_.[ insOrder q , [] ] a (lem P emptyP insertP (insOrder q)))
                         (insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (lem P emptyP insertP (insOrder q))))
      lem6 q = congP (λ i Pq → insertP (canonicalizeResp q (~ i)) a Pq ) (lem5 q)
      lem8 : (q : Q) → _/_.[ insOrder (enqueue a q) , [] ] ≡ depConstrInsert a _/_.[ insOrder q , [] ]
      lem8 (l1 , l2) = refl
      lem7 : (q : Q) → PathP
                         (λ i → P (lem8 q i))
                         (lem P emptyP insertP (insOrder (enqueue a q)))
                         (insertP _/_.[ insOrder q , [] ] a (lem P emptyP insertP (insOrder q)))
      lem7 (l1 , l2) = refl
      lem9 : (q : Q) → PathP
                         (λ i → P (((canonicalizeResp (enqueue a q)) ∙ (lem8 q) ∙ (λ i → depConstrInsert a (canonicalizeResp q (~ i)))) i))
                         (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                           (lem P emptyP insertP
                             (insOrder (enqueue a q))))
                         (insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (lem P emptyP insertP (insOrder q))))
      lem9 q = compPathP' {B = P} (lem4 q) (compPathP' {B = P} (lem7 q) (lem6 q))
      typesSame : (q : Q) →
        PathP
          (λ i → P (((canonicalizeResp (enqueue a q)) ∙ (lem8 q) ∙ (λ i → depConstrInsert a (canonicalizeResp q (~ i)))) i))
          (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
            (lem P emptyP insertP
              (insOrder (enqueue a q))))
          (insertP _/_.[ q ] a
            (transport (λ i → P (canonicalizeResp q (~ i)))
              (lem P emptyP insertP (insOrder q))))
        ≡ PathP
            (λ i → P (refl {x = _/_.[ enqueue a q ]} i))
            (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
              (lem P emptyP insertP
                (insOrder (enqueue a q))))
            (insertP _/_.[ q ] a
              (transport (λ i → P (canonicalizeResp q (~ i)))
                (lem P emptyP insertP (insOrder q))))
      typesSame q =
        cong
         (λ x →
           PathP
            (λ i → P (x i))
            (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
              (lem P emptyP insertP
                (insOrder (enqueue a q))))
            (insertP _/_.[ q ] a
              (transport (λ i → P (canonicalizeResp q (~ i)))
                (lem P emptyP insertP (insOrder q)))))
         (squash/ _ _ _ _)
      lem3 : (q : Q) → transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                         (lem P emptyP insertP
                           (insOrder (enqueue a q)))
                       ≡ insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (lem P emptyP insertP (insOrder q)))
      lem3 q = transport (typesSame q) (lem9 q)

    ιTLQInsert : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrInsert a q)) →
      (a : A) → (q : TLQ) → (Q : P (depConstrInsert a q) → Set) →
      Q (depElimQ P pset emptyP insertP (depConstrInsert a q)) →
      Q (insertP q a (depElimQ P pset emptyP insertP q))
    ιTLQInsert P pset emptyP insertP a q Q Qp = transport (cong Q (ιTLQInsertEq P pset emptyP insertP a q)) Qp

    ιTLQInsert⁻ : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrInsert a q)) →
      (a : A) → (q : TLQ) → (Q : P (depConstrInsert a q) → Set) →
      Q (insertP q a (depElimQ P pset emptyP insertP q)) →
      Q (depElimQ P pset emptyP insertP (depConstrInsert a q))
    ιTLQInsert⁻ P pset emptyP insertP a q Q Qp = transport (cong Q (sym (ιTLQInsertEq P pset emptyP insertP a q))) Qp
      
    enqueue/R : A → TLQ → TLQ
    enqueue/R = depConstrInsert

    abstract 
      isSetDeqReturnType : isSet (Maybe (TLQ × A))
      isSetDeqReturnType = isOfHLevelMaybe 0 (isOfHLevelProd 2 squash/ isSetℕ)

    dequeue/R : TLQ → Maybe (TLQ × A)
    dequeue/R = depElimQ (λ x → Maybe (TLQ × A)) (λ _ → isSetDeqReturnType) nothing recCase where
      recCase : (q : TLQ) (outer : A) → Maybe (TLQ × A) → Maybe (TLQ × A)
      recCase q outer m =
        Cubical.Data.Maybe.rec
          (just (depConstrEmpty , outer))
          (λ p → just (depConstrInsert outer (proj₁ p) , (proj₂ p)))
          m

    isEmpty/R : TLQ → Bool
    isEmpty/R = depElimQ (λ _ → Bool) (λ _ → isSetBool) true (λ _ _ _ →  false)
    {-
    emptyTrueOk : isEmpty/R depConstrEmpty ≡ true
    emptyTrueOk = refl

    emptyFalseOk : (a : A) (q : TLQ) → isEmpty/R (depConstrInsert a q) ≡ false
    emptyFalseOk a = depElimQ (λ x → isEmpty/R (depConstrInsert a x) ≡ false) (λ _ → isProp→isSet (isSetBool _ _)) refl (λ q₁ a₁ x → {!!} ∙ x )
    
    enqueueDequeueEmptyOk : (a : A) → dequeue/R (enqueue/R a depConstrEmpty) ≡ just (depConstrEmpty , a)
    enqueueDequeueEmptyOk a = refl
    -}
    --dequeueEnqueue formulation from "Internalizing Representation Independence with Univalence" by Angiuli et al.
    returnOrEnq : A → Maybe (TLQ × A) → TLQ × A
    returnOrEnq a m = Cubical.Data.Maybe.rec (depConstrEmpty , a) (λ p → (enqueue/R a (proj₁ p) , proj₂ p)) m

    dequeueEnqueue : (a : A) (q : TLQ) → dequeue/R (enqueue/R a q) ≡ just (returnOrEnq a (dequeue/R q))
    dequeueEnqueue a q =
      ιTLQInsert⁻
        (λ _ → Maybe (TLQ × A))
        (λ _ → isSetDeqReturnType)
        nothing
        (λ q₁ outer m →
          Cubical.Data.Maybe.rec (just (_/_.[ [] , [] ] , outer))
          (λ p →
             just
             (SetQuotients.rec squash/ (λ q₂ → _/_.[ enqueue outer q₂ ])
              (enqResp outer) (proj₁ p)
              , proj₂ p))
          m)
        a
        q
        (λ m → m ≡ just (returnOrEnq a (dequeue/R q)) )
        (congMaybeRec
          (depConstrEmpty , a)
          (λ p → ((depConstrInsert a (proj₁ p)) , proj₂ p))
          (depElimQ
            (λ _ → Maybe (TLQ × A))
            (λ _ → isSetDeqReturnType)
            nothing
            (λ q1 outer m → Cubical.Data.Maybe.rec (just (depConstrEmpty , outer))
            ((λ p → just ((depConstrInsert outer (proj₁ p)) , proj₂ p))) m)
            q)
          just)

    -- safe-head and safe-tail copied from std library List.Properties, these functions are private there
    safe-head : A → List A → A
    safe-head x []      = x
    safe-head _ (x ∷ _) = x

    safe-tail : List A → List A
    safe-tail []       = []
    safe-tail (_ ∷ xs) = xs

    headTailNonempty : (a : A) (l : List A) → (safe-head a (l ++ (a ∷ []))) ∷ (safe-tail (l ++ (a ∷ []))) ≡ l ++ (a ∷ [])
    headTailNonempty a [] = refl
    headTailNonempty a (x ∷ l) = refl

    fastDequeue/R : TLQ → Maybe (TLQ × A)
    fastDequeue/R = SetQuotients.rec isSetDeqReturnType func wellDefined where
      func : Q → Maybe (TLQ × A)
      {- func (l1 , l2) =
        ListRec
          (ListRec
            nothing
            (λ a l _ → just (_/_.[ [] , safe-tail (rev (a ∷ l1)) ] , safe-head a (rev (a ∷ l1))))
            l1)
          (λ a l _ → just (_/_.[ l1 , l ] , a))
          l2-}
      func ([] , []) = nothing
      func ((a ∷ l1) , []) = just (_/_.[ [] , safe-tail (rev (a ∷ l1)) ] , safe-head a (rev (a ∷ l1)))
      func ([] , (a ∷ l2)) = just (_/_.[ [] , l2 ] , a)
      func ((b ∷ l1) , (a ∷ l2)) = just (_/_.[ (b ∷ l1) , l2 ] , a)

      wellDefinedHelp : (q : Q) → func q ≡ func ([] , (rev (insOrder q)))
      wellDefinedHelp ([] , []) = refl
      wellDefinedHelp ((x ∷ l1) , []) = (cong (λ l → func ([] , l)) (headTailNonempty x (rev l1)))
                                        ∙ (sym (cong (λ l → func ([] , (rev l) ++ (x ∷ []))) (++-unit-r l1)))
      wellDefinedHelp ([] , (x ∷ l2)) = cong (λ l → just (_/_.[ [] , l ] , x)) (sym (rev-rev l2))
                                        ∙ (cong (λ l → func ([] , l)) (sym (rev-snoc (rev l2) x)))
      wellDefinedHelp ((y ∷ l1) , (x ∷ l2)) =
        (cong
          just
          (×≡
            (eq/
              (y ∷ l1 , l2)
              ([] , rev (l1 ++ rev l2) ++ (y ∷ []))
              (cong
                (λ l → y ∷ l)
                (sym (rev-rev (l1 ++ rev l2))) ∙ sym (rev-snoc (rev (l1 ++ rev l2)) y)))
            refl)  -- (eq/ (y ∷ l1 , l2) ([] , rev (l1 ++ rev l2) ++ (y ∷ [])))
        ∙ (cong (λ l → func ([] , l ++ (y ∷ []))) (sym (rev-snoc (l1 ++ rev l2) x))))
        ∙ (cong (λ l → func ([] , (rev l) ++ (y ∷ []))) (++-assoc l1 (rev l2) (x ∷ [])))
      wellDefined : (a b : Q) (r : R a b) → func a ≡ func b
      wellDefined a b r = wellDefinedHelp a ∙ cong (λ l → func ([] , rev l)) r ∙ (sym (wellDefinedHelp b))
{-
    deqIsFastDeq : dequeue/R ≡ fastDequeue/R
    deqIsFastDeq = funExt (depElimQ (λ q → dequeue/R q ≡ fastDequeue/R q) (λ _ → isProp→isSet (isSetDeqReturnType _ _)) refl insertCase) where
      -- help : (q : TLQ) (a : A) → depConstrInsert a (proj₁ (fastDequeue/R q)) ≡ proj₁ (fastDequeue/R (depConstrInsert a q))
      -- help q a = ?
      insertCase : (q : TLQ) (a : A) → dequeue/R q ≡ fastDequeue/R q → dequeue/R (depConstrInsert a q) ≡ fastDequeue/R (depConstrInsert a q)
      insertCase q a Pq = {!!}
-}
