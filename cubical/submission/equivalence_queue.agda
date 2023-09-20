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

record Queue {ℓ} : Set (ℓ-suc ℓ) where
  field
    A : Set ℓ
    Q : Set ℓ
    null : Q
    enqueue : A → Q → Q
    dequeue : Q → Maybe (Q × A) -- similiar to the Cubical lib def but with Maybe

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
    -- We fix A here, but the proofs are generic over any set A.
    A = ℕ
    isSetA : isSet A
    isSetA = isSetℕ
    OLQ = List A

    depConstrOLQEmpty : OLQ
    depConstrOLQEmpty = []

    depConstrOLQInsert : A → OLQ → OLQ
    depConstrOLQInsert a q = a ∷ q

    depElimOLQ : (P : OLQ -> Type) -> (P depConstrOLQEmpty) -> (∀ q a -> (P q) -> P (depConstrOLQInsert a q)) -> ((x : OLQ) -> P x)
    depElimOLQ P baseCase consCase [] = baseCase
    depElimOLQ P baseCase consCase (x ∷ l) = consCase l x (depElimOLQ P baseCase consCase l)

    -- ι is trivial here, so we don't write the rewrite forms
    ιOLQInsertEq : (P : OLQ → Set) →
      (emptyP : P depConstrOLQEmpty) →
      (insertP : (q : OLQ) → (a : A) → (P q) → P (depConstrOLQInsert a q)) →
      (a : A) → (q : OLQ) →
      depElimOLQ P emptyP insertP (depConstrOLQInsert a q)
      ≡ insertP q a (depElimOLQ P emptyP insertP q)
    ιOLQInsertEq P pset emptyP insertP a = refl

    enqueue : A → OLQ → OLQ
    enqueue = depConstrOLQInsert

    dequeue : OLQ → Maybe (OLQ × A)
    dequeue = depElimOLQ (λ _ → Maybe (OLQ × A)) nothing recCase where
      recCase : (q : OLQ) (outer : A) → Maybe (OLQ × A) → Maybe (OLQ × A)
      recCase q outer m =
        Cubical.Data.Maybe.rec
          (just (depConstrOLQEmpty , outer))
          (λ p → just (depConstrOLQInsert outer (proj₁ p) , (proj₂ p)))
          m

    front : OLQ → Maybe (OLQ × A)
    front = depElimOLQ (λ x₁ → Maybe (OLQ × A)) nothing (λ q a x₁ → just (q , a))

    isEmpty : OLQ → Bool
    isEmpty = depElimOLQ (λ _ → Bool) true (λ _ _ _ →  false)

    emptyTrueOk : isEmpty depConstrOLQEmpty ≡ true
    emptyTrueOk = refl

    implTest1 : dequeue (enqueue 2 (enqueue 1 [])) ≡ just (enqueue 2 [] , 1)
    implTest1 = refl

    enqueueDequeueEmptyOk : (a : A) → dequeue (enqueue a depConstrOLQEmpty) ≡ just (depConstrOLQEmpty , a)
    enqueueDequeueEmptyOk a = refl

    dequeueEmpty : dequeue depConstrOLQEmpty ≡ nothing
    dequeueEmpty = refl

    -- dequeueEnqueue formulation from "Internalizing Representation Independence with Univalence" by Angiuli et al.
    returnOrEnq : A → Maybe (OLQ × A) → OLQ × A
    returnOrEnq a m = Cubical.Data.Maybe.rec (depConstrOLQEmpty , a) (λ p → (enqueue a (proj₁ p) , proj₂ p)) m

    dequeueEnqueue : (a : A) (q : OLQ) → dequeue (enqueue a q) ≡ just (returnOrEnq a (dequeue q))
    dequeueEnqueue a q =
      congMaybeRec
        (depConstrOLQEmpty , a)
        (λ p → ((depConstrOLQInsert a (proj₁ p)) , proj₂ p))
        (depElimOLQ
          (λ _ → Maybe (OLQ × A))
          nothing
          (λ q₁ outer m →
            Cubical.Data.Maybe.rec (just (depConstrOLQEmpty , outer))
            (λ p → just ((depConstrOLQInsert outer (proj₁ p)) , proj₂ p)) m)
        q)
        just

    OneList = record { A = A; Q = OLQ ; null = [] ; enqueue = enqueue; dequeue = dequeue}

    isSetOLQ : isSet OLQ
    isSetOLQ = isOfHLevelList 0 isSetA

module TwoList where
    -- We fix A here, but the proofs are generic over any set A.
    A = ℕ
    isSetA : isSet A
    isSetA = isSetℕ
    Q = (List A × List A)

    -- Enqueue on the unquotiented queue type. Used to define dependent constructor.
    enqueue : A → Q → Q
    enqueue x (x₁ , x₂) = (x ∷ x₁ , x₂)

    insOrder : Q → List A
    insOrder (l1 , l2) = l1 ++ (rev l2)

    canonicalize : Q → Q
    canonicalize q = (insOrder q , [])

    insOrderCanonicalizeResp : (q : Q) → insOrder q ≡ insOrder (canonicalize q)
    insOrderCanonicalizeResp q = sym (++-unit-r (insOrder q))

    isEmpty : List A → Bool
    isEmpty [] = true
    isEmpty (x ∷ x₁) = false

    R : Q → Q → Type
    R q1 q2 = insOrder q1 ≡ insOrder q2

    TLQ : Type
    TLQ = Q / R

    isSetTLQ : isSet TLQ
    isSetTLQ = squash/

    depConstrTLQEmpty : TLQ
    depConstrTLQEmpty = _/_.[ ([] , []) ]

    canonicalizeResp : (q : Q) → _/_.[_] {R = R} q ≡ _/_.[ canonicalize q ]
    canonicalizeResp (l1 , l2) = eq/ (l1 , l2) (canonicalize (l1 , l2)) (insOrderCanonicalizeResp (l1 , l2))

    canonicalizeResp⁻ : (q : Q) → _/_.[ canonicalize q ] ≡ _/_.[_] {R = R} q
    canonicalizeResp⁻ q = sym (canonicalizeResp q)

    canonicalizeIdempotent : (q : Q) →  canonicalize q ≡ canonicalize (canonicalize q)
    canonicalizeIdempotent q = ×≡ (sym (++-unit-r (insOrder q))) refl

    insOrderEnq : (a : A) → (q : Q) → a ∷ insOrder q ≡ insOrder (enqueue a q)
    insOrderEnq a (l1 , l2) = refl

    enqResp : (a : A) → (q1 q2 : Q) → R q1 q2 → _/_.[_] {R = R} (enqueue a q1) ≡ _/_.[ enqueue a q2 ]
    enqResp a (l1 , l2) (l3 , l4) r = eq/ (a ∷ l1 , l2) (a ∷ l3 , l4) (cong (λ l → a ∷ l) r)

    depConstrTLQInsert : A → TLQ → TLQ
    depConstrTLQInsert a = SetQuotients.rec squash/ (λ q → _/_.[ enqueue a q ] ) (enqResp a)

    depElimHelp : (P : TLQ → Set) → P depConstrTLQEmpty → ((q : TLQ) → (a : A) → P q → P (depConstrTLQInsert a q)) → (l : List A) → P _/_.[ (l , []) ]
    depElimHelp P baseCase insertCase [] = baseCase
    depElimHelp P baseCase insertCase (a ∷ l) = insertCase _/_.[ l , [] ] a (depElimHelp P baseCase insertCase l)
      
    depElimTLQ : (P : TLQ → Set) → (∀ x → isSet (P x)) → P depConstrTLQEmpty → ((q : TLQ) → (a : A) → P q → P (depConstrTLQInsert a q)) → ∀ q' → P q'
    depElimTLQ P set baseCase insertCase = SetQuotients.elim set func wellDefined where
      func : (q : Q) → P _/_.[ q ]
      func q = transport (cong P (canonicalizeResp⁻ q)) (depElimHelp P baseCase insertCase (insOrder q))
      lem2 : (q : Q) → PathP (λ i → P ((canonicalizeResp⁻ q) i))
        (depElimHelp P baseCase insertCase (insOrder q))
        (transport (cong P (sym (canonicalizeResp q))) (depElimHelp P baseCase insertCase (insOrder q)))
      lem2 q = transport-filler (cong P (canonicalizeResp⁻ q)) (depElimHelp P baseCase insertCase (insOrder q))
      lemResp : (q1 q2 : Q) → (r : R q1 q2) → PathP (λ i → P (cong (λ l → _/_.[ (l , []) ]) r i)) (depElimHelp P baseCase insertCase (insOrder q1)) (depElimHelp P baseCase insertCase (insOrder q2))
      lemResp q1 q2 r = congP (λ i a → depElimHelp P baseCase insertCase a) r
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
      (emptyP : P depConstrTLQEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrTLQInsert a q)) →
      depElimTLQ P pset emptyP insertP depConstrTLQEmpty ≡ emptyP
    ιTLQEmptyEq P pset emptyP insertP =
      cong
        (λ x → transport (λ i → P (x i)) emptyP)
        (squash/ {R = R}
          depConstrTLQEmpty
          depConstrTLQEmpty
          (sym (eq/ ([] , []) ([] , []) refl))
          refl)
      ∙ transportRefl emptyP

    ιTLQEmpty : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrTLQEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrTLQInsert a q)) →
      (Q : P depConstrTLQEmpty → Set) → Q (depElimTLQ P pset emptyP insertP depConstrTLQEmpty) → Q emptyP
    ιTLQEmpty P pset emptyP insertP Q Qp = transport (cong Q (ιTLQEmptyEq P pset emptyP insertP)) Qp

    ιTLQEmpty⁻ : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrTLQEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrTLQInsert a q)) →
      (Q : P depConstrTLQEmpty → Set) → Q emptyP → Q (depElimTLQ P pset emptyP insertP depConstrTLQEmpty)
    ιTLQEmpty⁻ P pset emptyP insertP Q Qp = transport (cong Q (sym (ιTLQEmptyEq P pset emptyP insertP))) Qp

    ιTLQInsertEq : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrTLQEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrTLQInsert a q)) →
      (a : A) → (q : TLQ) →
      depElimTLQ P pset emptyP insertP (depConstrTLQInsert a q)
      ≡ insertP q a (depElimTLQ P pset emptyP insertP q)
    ιTLQInsertEq P pset emptyP insertP a =
      SetQuotients.elimProp
        (λ x → ((pset (depConstrTLQInsert a x)) (depElimTLQ P pset emptyP insertP (depConstrTLQInsert a x)) (insertP x a (depElimTLQ P pset emptyP insertP x))) )
        (λ q → lem3 q) where
      -- a significant number of lemmas are used to build the right PathP
      lem5 : (q : Q) → PathP
                         (λ i → P (canonicalizeResp q (~ i)))      
                         (depElimHelp P emptyP insertP (insOrder q))
                         (transport
                           (λ i → P (canonicalizeResp q (~ i)))
                           (depElimHelp P emptyP insertP (insOrder q)))
      lem5 q = transport-filler (cong P (canonicalizeResp⁻ q)) (depElimHelp P emptyP insertP (insOrder q))
      lem4 : (q : Q) → PathP
                         (λ i → P (canonicalizeResp (enqueue a q) i))
                         (transport
                           (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                           (depElimHelp P emptyP insertP (insOrder (enqueue a q))))      
                         (depElimHelp P emptyP insertP (insOrder (enqueue a q)))
      lem4 q = symP (lem5 (enqueue a q))
      lem6 : (q : Q) → PathP
                         (λ i → P (depConstrTLQInsert a (canonicalizeResp q (~ i))))
                         (insertP _/_.[ insOrder q , [] ] a (depElimHelp P emptyP insertP (insOrder q)))
                         (insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (depElimHelp P emptyP insertP (insOrder q))))
      lem6 q = congP (λ i Pq → insertP (canonicalizeResp q (~ i)) a Pq ) (lem5 q)
      lem8 : (q : Q) → _/_.[ insOrder (enqueue a q) , [] ] ≡ depConstrTLQInsert a _/_.[ insOrder q , [] ]
      lem8 (l1 , l2) = refl
      lem7 : (q : Q) → PathP
                         (λ i → P (lem8 q i))
                         (depElimHelp P emptyP insertP (insOrder (enqueue a q)))
                         (insertP _/_.[ insOrder q , [] ] a (depElimHelp P emptyP insertP (insOrder q)))
      lem7 (l1 , l2) = refl
      lem9 : (q : Q) → PathP
                         (λ i → P (((canonicalizeResp (enqueue a q)) ∙ (lem8 q) ∙ (λ i → depConstrTLQInsert a (canonicalizeResp q (~ i)))) i))
                         (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                           (depElimHelp P emptyP insertP
                             (insOrder (enqueue a q))))
                         (insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (depElimHelp P emptyP insertP (insOrder q))))
      lem9 q = compPathP' {B = P} (lem4 q) (compPathP' {B = P} (lem7 q) (lem6 q))
      typesSame : (q : Q) →
        PathP
          (λ i → P (((canonicalizeResp (enqueue a q)) ∙ (lem8 q) ∙ (λ i → depConstrTLQInsert a (canonicalizeResp q (~ i)))) i))
          (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
            (depElimHelp P emptyP insertP
              (insOrder (enqueue a q))))
          (insertP _/_.[ q ] a
            (transport (λ i → P (canonicalizeResp q (~ i)))
              (depElimHelp P emptyP insertP (insOrder q))))
        ≡ PathP
            (λ i → P (refl {x = _/_.[ enqueue a q ]} i))
            (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
              (depElimHelp P emptyP insertP
                (insOrder (enqueue a q))))
            (insertP _/_.[ q ] a
              (transport (λ i → P (canonicalizeResp q (~ i)))
                (depElimHelp P emptyP insertP (insOrder q))))
      typesSame q =
        cong
         (λ x →
           PathP
            (λ i → P (x i))
            (transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
              (depElimHelp P emptyP insertP
                (insOrder (enqueue a q))))
            (insertP _/_.[ q ] a
              (transport (λ i → P (canonicalizeResp q (~ i)))
                (depElimHelp P emptyP insertP (insOrder q)))))
         (squash/ _ _ _ _)
      lem3 : (q : Q) → transport (λ i → P (canonicalizeResp (enqueue a q) (~ i)))
                         (depElimHelp P emptyP insertP
                           (insOrder (enqueue a q)))
                       ≡ insertP _/_.[ q ] a
                           (transport (λ i → P (canonicalizeResp q (~ i)))
                             (depElimHelp P emptyP insertP (insOrder q)))
      lem3 q = transport (typesSame q) (lem9 q)

    ιTLQInsert : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrTLQEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrTLQInsert a q)) →
      (a : A) → (q : TLQ) → (Q : P (depConstrTLQInsert a q) → Set) →
      Q (depElimTLQ P pset emptyP insertP (depConstrTLQInsert a q)) →
      Q (insertP q a (depElimTLQ P pset emptyP insertP q))
    ιTLQInsert P pset emptyP insertP a q Q Qp = transport (cong Q (ιTLQInsertEq P pset emptyP insertP a q)) Qp

    ιTLQInsert⁻ : (P : TLQ → Set) → (pset : (q : TLQ) → isSet (P q)) →
      (emptyP : P depConstrTLQEmpty) →
      (insertP : (q : TLQ) → (a : A) → (P q) → P (depConstrTLQInsert a q)) →
      (a : A) → (q : TLQ) → (Q : P (depConstrTLQInsert a q) → Set) →
      Q (insertP q a (depElimTLQ P pset emptyP insertP q)) →
      Q (depElimTLQ P pset emptyP insertP (depConstrTLQInsert a q))
    ιTLQInsert⁻ P pset emptyP insertP a q Q Qp = transport (cong Q (sym (ιTLQInsertEq P pset emptyP insertP a q))) Qp

    -- Repaired enqueue.
    enqueue/R : A → TLQ → TLQ
    enqueue/R = depConstrTLQInsert
 
    isSetDeqReturnType : isSet (Maybe (TLQ × A))
    isSetDeqReturnType = isOfHLevelMaybe 0 (isOfHLevelProd 2 squash/ isSetA)

    -- Repaired dequeue.
    dequeue/R : TLQ → Maybe (TLQ × A)
    dequeue/R = depElimTLQ (λ x → Maybe (TLQ × A)) (λ _ → isSetDeqReturnType) nothing recCase where
      recCase : (q : TLQ) (outer : A) → Maybe (TLQ × A) → Maybe (TLQ × A)
      recCase q outer m =
        Cubical.Data.Maybe.rec
          (just (depConstrTLQEmpty , outer))
          (λ p → just (depConstrTLQInsert outer (proj₁ p) , (proj₂ p)))
          m

    isEmpty/R : TLQ → Bool
    isEmpty/R = depElimTLQ (λ _ → Bool) (λ _ → isSetBool) true (λ _ _ _ →  false)

    front/R : TLQ → Maybe (TLQ × A)
    front/R = depElimTLQ (λ x → Maybe (TLQ × A)) (λ _ → isSetDeqReturnType) nothing λ q a x → just (q , a)

    emptyTrueOk : isEmpty/R depConstrTLQEmpty ≡ true
    emptyTrueOk = refl

    enqueueDequeueEmptyOk : (a : A) → dequeue/R (enqueue/R a depConstrTLQEmpty) ≡ just (depConstrTLQEmpty , a)
    enqueueDequeueEmptyOk a = refl

    -- Repaired dequeue spec.
    dequeueEmpty : dequeue/R depConstrTLQEmpty ≡ nothing
    dequeueEmpty = refl

    -- dequeueEnqueue formulation from "Internalizing Representation Independence with Univalence" by Angiuli et al.
    returnOrEnq : A → Maybe (TLQ × A) → TLQ × A
    returnOrEnq a m = Cubical.Data.Maybe.rec (depConstrTLQEmpty , a) (λ p → (enqueue/R a (proj₁ p) , proj₂ p)) m

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
          (depConstrTLQEmpty , a)
          (λ p → ((depConstrTLQInsert a (proj₁ p)) , proj₂ p))
          (depElimTLQ
            (λ _ → Maybe (TLQ × A))
            (λ _ → isSetDeqReturnType)
            nothing
            (λ q1 outer m → Cubical.Data.Maybe.rec (just (depConstrTLQEmpty , outer))
            ((λ p → just ((depConstrTLQInsert outer (proj₁ p)) , proj₂ p))) m)
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

    fastDequeueEnqueue : (a : A) (q : TLQ) → fastDequeue/R (enqueue/R a q) ≡ just (returnOrEnq a (fastDequeue/R q))
    fastDequeueEnqueue a = SetQuotients.elimProp (λ _ → isSetDeqReturnType _ _ ) func where
      safe-tailApp : (l : List A) (x a : A) → safe-tail ((l ++ (x ∷ [])) ++ (a ∷ [])) ≡ (safe-tail (l ++ (x ∷ []))) ++ (a ∷ [])
      safe-tailApp [] x a = refl
      safe-tailApp (y ∷ l) x a = refl
      safe-headApp : (l : List A) (x a : A) → safe-head a ((l ++ (x ∷ [])) ++ (a ∷ [])) ≡ (safe-head x (l ++ (x ∷ [])))
      safe-headApp [] x a = refl
      safe-headApp (y ∷ l) x a = refl
      func : (q : Q) → fastDequeue/R (enqueue/R a _/_.[ q ]) ≡ just (returnOrEnq a (fastDequeue/R _/_.[ q ]))
      func ([] , []) = refl
      func ((x ∷ l1) , []) = cong just (×≡
        (eq/ _ _ ((cong rev (safe-tailApp (rev l1) x a)) ∙ (rev-snoc (safe-tail (rev l1 ++ (x ∷ []))) a)))
        (safe-headApp (rev l1) x a))
      func ([] , (y ∷ l2)) = cong just (×≡ refl refl)
      func ((x ∷ l1) , (y ∷ l2)) = cong just (×≡ refl refl)

    deqIsFastDeq : dequeue/R ≡ fastDequeue/R
    deqIsFastDeq = funExt (depElimTLQ (λ q → dequeue/R q ≡ fastDequeue/R q) (λ _ → isProp→isSet (isSetDeqReturnType _ _)) refl insertCase) where
      insertCase : (q : TLQ) (a : A) → dequeue/R q ≡ fastDequeue/R q → dequeue/R (depConstrTLQInsert a q) ≡ fastDequeue/R (depConstrTLQInsert a q)
      insertCase q a Pq = dequeueEnqueue a q ∙ cong (λ x → just (returnOrEnq a x)) Pq ∙ (sym (fastDequeueEnqueue a q))

    TwoList = record { A = A; Q = TLQ ; null = depConstrTLQEmpty ; enqueue = enqueue/R; dequeue = fastDequeue/R}

OLQ≡TLQ : OneList.OLQ ≡ TwoList.TLQ
OLQ≡TLQ = isoToPath (iso f g sec ret) where
  f : OneList.OLQ → TwoList.TLQ
  f = OneList.depElimOLQ
        (λ _ → TwoList.TLQ)
        TwoList.depConstrTLQEmpty
        (λ olq a tlq → TwoList.depConstrTLQInsert a tlq)
  g : TwoList.TLQ → OneList.OLQ
  g = TwoList.depElimTLQ
        (λ _ → OneList.OLQ)
        (λ _ → OneList.isSetOLQ)
        OneList.depConstrOLQEmpty
        λ tlq a olq → OneList.depConstrOLQInsert a olq
  sec : section f g
  sec = TwoList.depElimTLQ
          (λ x → f (g x) ≡ x)
          (λ x → isProp→isSet (TwoList.isSetTLQ _ _))
          refl
          λ q a Pq → TwoList.ιTLQInsert⁻
            (λ _ → OneList.OLQ)
            (λ _ → OneList.isSetOLQ)
            OneList.depConstrOLQEmpty
            (λ tlq a olq → OneList.depConstrOLQInsert a olq)
            a
            q
            (λ x → f x ≡ TwoList.depConstrTLQInsert a q)
            (cong (TwoList.depConstrTLQInsert a) Pq)
  ret : retract f g
  ret = OneList.depElimOLQ
          (λ x → g (f x) ≡ x)
          refl
          λ q a Pq →
            TwoList.ιTLQInsert⁻
              (λ _ → OneList.OLQ)
              (λ _ → OneList.isSetOLQ)
              OneList.depConstrOLQEmpty
              (λ tlq a olq → OneList.depConstrOLQInsert a olq)
              a
              (f q)
              (λ x → x ≡ OneList.depConstrOLQInsert a q)
              (cong (OneList.depConstrOLQInsert a) Pq)
