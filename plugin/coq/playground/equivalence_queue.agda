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


    OneList = record { A = A; Q = Q ; null = [] ; enqueue = λ x x' → x ∷ x' ; dequeue = last }

    depConstrEmpty : Q
    depConstrEmpty = []

    depConstrInsert : A → Q → Q
    depConstrInsert x x' = x ∷ x'

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

    -- tail-recursive canonicalization func
    -- canonicalize : Q → OneList.Q
    -- canonicalize q = go q OneList.depConstrEmpty where
    --   go : Q → OneList.Q → OneList.Q
    --   go input output with dequeue input
    --   ...      | just (q , x) = go q (OneList.depConstrInsert x output)
    --   ...      | nothing = output

    canonicalizeTerm : List A → List A → OneList.Q
    canonicalizeTerm q q' = q' ++ (rev q)
    -- go q q' OneList.depConstrEmpty where -- tail recursive
    --   go : List A → List A → OneList.Q → OneList.Q -- inlined dequeue here to make term checking happy
    --   go [] [] output = output
    --   go (x ∷ xs) [] output with reverse (x ∷ xs)
    --   ...               | [] = output
    --   ...               | (y ∷ ys) = go [] ys (OneList.depConstrInsert y output)
    --   go in1 (x ∷ xs) output = go in1 xs (OneList.depConstrInsert x output)

    canonicalizeTermRight : (x : List A) → x ≡ canonicalizeTerm [] x
    canonicalizeTermRight l =  sym (++-unit-r l) ∙ refl
    -- refl
    -- canonicalizeTermRight (x ∷ xs) = cong (λ a → {!!}) (canonicalizeTermRight xs)
    -- cong help (canonicalizeTermRight xs) where
    --   help : List A → List A
    --   help [] = ?
    --   help (x ∷ x₁) = ?

    insOrder : Q → List A
    insOrder (l1 , l2) = l1 ++ (rev l2)

    canonicalize : Q → Q
    canonicalize q = (insOrder q , [])

    insOrderCanonicalizeResp : (q : Q) → insOrder q ≡ insOrder (canonicalize q)
    insOrderCanonicalizeResp q = sym (++-unit-r (insOrder q))

    canonicalizeInv : OneList.Q → Q
    canonicalizeInv x = ([] , x)

    canonicalizeSimple : Q → Q
    canonicalizeSimple (x , x₁) = ( [] , x₁ ++ (rev x) )

    -- _and_ : Type → Type → Type
    -- _and_ x x₁ = True

    defEquivN : ℕ → ℕ → Type
    defEquivN zero zero = Unit
    defEquivN zero (suc b) = ⊥
    defEquivN (suc a) zero = ⊥
    defEquivN (suc a) (suc b) = defEquivN a b

    defEquivL : List ℕ → List ℕ → Type
    defEquivL [] [] = Unit
    defEquivL [] (x ∷ x') = ⊥
    defEquivL (x ∷ x₂) [] = ⊥
    defEquivL (zero ∷ x₂) (zero ∷ x'') = defEquivL x₂ x''
    defEquivL (zero ∷ x₂) (suc x' ∷ x'') = ⊥
    defEquivL (suc x ∷ x₂) (zero ∷ x'') = ⊥
    defEquivL (suc x ∷ x₂) (suc x' ∷ x'') = defEquivL (x ∷ x₂) (x' ∷ x'')

    defEquivQ : Q → Q → Type
    defEquivQ ([] , x₂) ([] , x₃) = defEquivL x₂ x₃
    defEquivQ ([] , x₂) ((x ∷ x') , x₃) = ⊥
    defEquivQ ((x ∷ x₄) , x₂) ([] , x₃) = ⊥
    defEquivQ ((zero ∷ x₄) , x₂) ((zero ∷ x') , x₃) = defEquivQ (x₄ , x₂) (x' , x₃)
    defEquivQ ((zero ∷ x₄) , x₂) ((suc x'' ∷ x') , x₃) = ⊥
    defEquivQ ((suc x ∷ x₄) , x₂) ((zero ∷ x') , x₃) = ⊥
    defEquivQ ((suc x ∷ x₄) , x₂) ((suc x'' ∷ x') , x₃) = defEquivQ ((x ∷ x₄) , x₂) ((x'' ∷ x') , x₃)


    defEquivLLifted : (n1 n2 : List ℕ) → defEquivL n1 n2 → n1 ≡ n2
    defEquivLLifted [] [] x = refl
    defEquivLLifted (zero ∷ n1) (zero ∷ n2) x = cong (λ a →  zero ∷ a) (defEquivLLifted n1 n2 x)
    defEquivLLifted (suc x' ∷ n1) (suc x'' ∷ n2) x = cong (λ a → help a) (defEquivLLifted (x' ∷ n1) (x'' ∷ n2) x) where
      help : List ℕ → List ℕ
      help [] = []
      help (x ∷ x₁) = suc x ∷ x₁

    -- length : List Nat → Nat
    -- length [] = 0
    -- length (x ∷ x₁) = 1 + length x₁

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

-- {y..1 : Level} {A : Type y..1} {ℓ' : Level} {x y : A}
-- (B : A → Type ℓ') →
-- x ≡ y → B x → B y
    defEquivLLower : (n1 n2 : List ℕ) → n1 ≡ n2 → defEquivL n1 n2
    defEquivLLower [] [] x = tt
    defEquivLLower [] (x₁ ∷ n2) x = false≢true (sym (cong isEmpty x))
    defEquivLLower (x₁ ∷ n1) [] x = false≢true (cong isEmpty x)
    defEquivLLower (zero ∷ n1) (zero ∷ n2) proof = defEquivLLower n1 n2 (cong tail proof)
    defEquivLLower (zero ∷ n1) (suc y ∷ n2) proof = false≢true (sym (cong (λ a → isZero (head a)) proof))
    defEquivLLower (suc x ∷ n1) (zero ∷ n2) proof = false≢true (cong (λ a → isZero (head a)) proof)
    defEquivLLower (suc x ∷ n1) (suc y ∷ n2) proof = defEquivLLower (x ∷ n1) (y ∷ n2) (cong help proof) where
      help : List ℕ → List ℕ
      help [] = []
      help (zero ∷ xs) = (zero ∷ xs)
      help (suc x ∷ xs) = (x ∷ xs)
      -- lem : defEquivL n1 n1
      -- lem = defEquivLLower n1 n1 refl
      -- lem' : defEquivL n1 n2
      -- lem' = defEquivLLower n1 n2 tailHelp where
      --   headHelp : x₁ ≡ x₂
      --   headHelp = cong help x where
      --     help : List Nat → Nat
      --     help [] = 0
      --     help (x ∷ x₁) = x
      --   tailHelp : n1 ≡ n2
      --   tailHelp = cong help x where
      --     help : List Nat → List Nat
      --     help [] = []
      --     help (x ∷ xs) = xs

    defEquivQLifted : (q1 q2 : Q) → defEquivQ q1 q2 → q1 ≡ q2
    defEquivQLifted ([] , []) ([] , []) proof = refl
    defEquivQLifted ([] , (zero ∷ x')) ([] , (zero ∷ x'')) proof = cong (λ a → ([] , (zero ∷ a))) (defEquivLLifted x' x'' proof)
    defEquivQLifted ([] , (suc x ∷ xs)) ([] , (suc y ∷ ys)) proof = cong help (defEquivLLifted (x ∷ xs) (y ∷ ys) proof) where
      help : List ℕ → Q
      help [] = ([] , [])
      help (x ∷ xs) = ([] , suc x ∷ xs)
    defEquivQLifted ((zero ∷ xs) , x₁) ((zero ∷ ys) , x₃) proof = cong help (defEquivQLifted (xs , x₁) (ys , x₃) proof) where
      help : Q → Q
      help (x , y) = (zero ∷ x , y)
    defEquivQLifted ((suc x ∷ xs) , x₁) ((suc y ∷ ys) , x₃) proof = cong help (defEquivQLifted ((x ∷ xs) , x₁) ((y ∷ ys) , x₃) proof) where
      help : Q → Q
      help ([] , y) = ([] , y)
      help ((x ∷ xs) , y) = (suc x ∷ xs , y)

    defEquivQLower : (q1 q2 : Q) → q1 ≡ q2 → defEquivQ q1 q2
    defEquivQLower ([] , y) ([] , x) proof = defEquivLLower y x (cong π₂ proof)
    defEquivQLower ([] , y) ((x ∷ x') , x'') proof = false≢true (sym (cong (λ a → isEmpty (π₁ a)) proof))
    defEquivQLower ((x ∷ x₄) , x₁) ([] , x₃) proof = false≢true (cong (λ a → isEmpty (π₁ a)) proof)
    defEquivQLower ((zero ∷ xs) , x₁) ((zero ∷ ys) , x₃) proof = defEquivQLower (xs , x₁) (ys , x₃) help where
      help : (xs , x₁) ≡ (ys , x₃)
      help = cong (λ a → (tail (π₁ a) , π₂ a)) proof
    defEquivQLower ((zero ∷ xs) , x₁) ((suc y ∷ ys) , x₃) proof = false≢true (sym (cong (λ a → isZero (head (π₁ a))) proof))
    defEquivQLower ((suc x ∷ xs) , x₁) ((zero ∷ ys) , x₃) proof = false≢true (cong (λ a → isZero (head (π₁ a))) proof)
    defEquivQLower ((suc x ∷ xs) , x₁) ((suc y ∷ ys) , x₃) proof = defEquivQLower ((x ∷ xs) , x₁) ((y ∷ ys) , x₃) (cong help proof) where
      help : Q → Q
      help ([] , y) = ([] , y)
      help (zero ∷ xs , y) = (zero ∷ xs , y)
      help (suc x ∷ xs , y) = (x ∷ xs , y)

    

    R : Q → Q → Type
    R q1 q2 = insOrder q1 ≡ insOrder q2

    depConstrEmpty : Q / R
    depConstrEmpty = _/_.[ ([] , []) ]

    canonicalizeResp : (q : Q) → _/_.[_] {R = R} q ≡ _/_.[ canonicalize q ]
    canonicalizeResp (l1 , l2) = eq/ (l1 , l2) (canonicalize (l1 , l2)) (insOrderCanonicalizeResp (l1 , l2))

    enqCanonicalResp : (a : A) → (q : Q) → _/_.[_] {R = R} (enqueue a q) ≡ _/_.[ enqueue a (canonicalize q) ]
    enqCanonicalResp a (l1 , l2) = {!!}

    insOrderCons : (a : A) → (l1 l2 : List A) → a ∷ insOrder (l1 , l2) ≡ insOrder (a ∷ l1 , l2)
    insOrderCons a l1 l2 = refl

    enqResp : (a : A) → (q1 q2 : Q) → R q1 q2 → _/_.[_] {R = R} (enqueue a q1) ≡ _/_.[ enqueue a q2 ]
    enqResp a (l1 , l2) (l3 , l4) r = eq/ (a ∷ l1 , l2) (a ∷ l3 , l4) (cong (λ l → a ∷ l) r)

    depConstrInsert : A → (Q / R) → (Q / R)
    depConstrInsert a = SetQuotients.rec squash/ (λ q → _/_.[ enqueue a q ] ) (enqResp a)

{-
    depConstrInsert : A → (Q / quotient) → (Q / quotient)
    depConstrInsert x [ a ] =  _/_.[ enqueue x a ]
    depConstrInsert x (eq/ a b r i) = eq/ (enqueue x a) (enqueue x b) (defEquivQLower (genCanon (enqueue x a)) (genCanon (enqueue x b)) rLem) i where
      rTransform : genCanon a ≡ genCanon b
      rTransform = quotientGenCanonLifted a b r
      rHelp : genCanon (enqueue x (genCanon a)) ≡ genCanon (enqueue x (genCanon b))
      rHelp = cong (λ a → genCanon (enqueue x a)) rTransform
      rLem :  genCanon (enqueue x a) ≡ genCanon (enqueue x b)
      rLem = genCanonHomo a x ∙ rHelp ∙ symPath (genCanonHomo b x)
    depConstrInsert x (squash/ a b p q i j) = squash/ (depConstrInsert x a) (depConstrInsert x b) (cong (λ o → depConstrInsert x o) p) ((cong (λ o → depConstrInsert x o) q)) i j
-}

    isSetProd : ∀ {A : Type} {B : A → Type} → (∀ (a : A) → isSet (B a)) → isSet (∀ (a : A) → B a)
    isSetProd {A} {B} setB = λ (f g : ∀ (a : A) → B a) (p q : f ≡ g) → cong funExt (funExt (λ (a : A) → setB a (f a) (g a) (funExt⁻ p a) (funExt⁻ q a)))

    isSetFunc : {A B : Set} → isSet A → isSet B → isSet (A → B)
    isSetFunc {A} {B} setA setB = isSetProd {B = λ _ → B} (λ _ → setB)

    isSetFunc' : {A : Set} (B : A → Set) → ((a : A) → isSet (B a)) → isSet ((a : A) → (B a))
    isSetFunc' {A} B resultIsSet = isSetProd resultIsSet

    revSwap : (l : List ℕ ) → _/_.[_] (rev l , []) ≡ _/_.[ [] , l ]
    revSwap l = refl

    depElimQ : (P : (Q / R) → Set) → (∀ x → isSet (P x)) → P depConstrEmpty → ((q : Q / R) → (a : A) → P q → P (depConstrInsert a q)) → ∀ q' → P q'
    depElimQ P set baseCase insertCase = SetQuotients.elim set lem {!!} where
      lem' : (l : List A) → P _/_.[ (l , []) ]
      lem' [] = baseCase
      lem' (a ∷ l) = insertCase _/_.[ l , [] ] a (lem' l)
      lem : (q : Q) → P _/_.[ q ]
      lem q = transport (cong P (sym (canonicalizeResp q))) (lem' (insOrder q))
      {-
      lem' : (a : Q) → P _/_.[ a ]
      lem' ([] , []) = baseCase
      lem' ([] , (x ∷ xs)) = help xs where
        help : List ℕ → P _/_.[ ([] , (x ∷ xs)) ]
        help x = {!!}
      lem' ((x ∷ xs) , y) = insertCase _/_.[ (xs , y) ] x (lem' (xs , y))
      ++Q : (a b : Q) → Q
      ++Q (x , x₁) (x₂ , x₃) = ( [] , x₁ ++ (rev x) ++ x₃ ++ (rev x₂) )
      ++lem : (a b : Q) → P _/_.[ a ] → P _/_.[ b ] → P _/_.[ ++Q a b ] -- P _/_.[ a ++ b ]
      ++lem (x , x₁) (x₂ , x₃) b c = {!!}
      lem : (a : Q) → P _/_.[ a ]
      -- lem a = {!help q!} where
      --   q : Q
      --   q = canonicalizeSimple a
      --   help' : Q → P _/_.[ q ]
      --   help' (x , x₁) = {!!}
      --   help : (a : Q) → P _/_.[ a ]
      --   help a = {!!}
      lem ([] , x) = insertBackwards x where
         insertBackwards : (x : List ℕ) → P _/_.[ [] , x ]
         insertBackwards x = {!!} where -- substPath (λ a → {!!}) (revSwap x) startPoint where
           recInsert : (x : List ℕ) → P _/_.[ x , [] ]
           recInsert [] = baseCase
           recInsert (x ∷ xs) = insertCase _/_.[ (xs , []) ] x (recInsert xs) -- (help xs)
           startPoint : P _/_.[ rev x , [] ]
           startPoint = recInsert (rev x)
      lem ((x ∷ xs) , x₁) = insertCase _/_.[ (xs , x₁) ] x (lem (xs , x₁))
      -}
      {-
      wellDefined : (a b : Q) (r : R a b) → PathP (λ i → P (eq/ a b r i)) (lem a) (lem b)
      wellDefined a b r = {!!}
      help' : isSet ((a : Q) → P _/_.[ a ])
      help' = isSetFunc' (λ x → P _/_.[ x ]) λ x → set _/_.[ x ]
      -}


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

    canonicalizeInvEquiv : (q1 q2 : OneList.Q) → canonicalizeInv q1 ≡ canonicalizeInv q2 → q1 ≡ q2
    canonicalizeInvEquiv q1 q2 proof = cong π₂ proof

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
