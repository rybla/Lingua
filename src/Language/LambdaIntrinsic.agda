open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Product renaming (_,_ to _&_)


module Language.LambdaIntrinsic where

infix 2 _⊨_↝_ _⊨_⇓ _⊨_↝*_
infix 4 _⊢_
infix 4 _∋_
infixl 5 _,_

infixr 6 _`→_

infixr 6 `λ_
infixl 7 _`∙_
infix 8 [_]_
infix 9 `_ `#_


-- ==========================================
-- Types
-- ==========================================


-- type data
data Type : Set where
  `⊤ : Type
--  `ℕ : Type
  _`→_ : Type → Type → Type


-- type context
data Context : ℕ → Set where
  ø : Context 0
  _,_ : ∀ {n} (Γ : Context n) (α : Type) → Context (1 + n)


-- ``Γ ∋ α`` proves that type ``α`` is in context ``Γ``
data _∋_ : ∀ {n} → Context n → Type → Set where

  head : ∀ {n} {α} {Γ : Context n} →
    ------------------------------------------------
    Γ , α ∋ α

  tail : ∀ {n} {α β} {Γ : Context n} →
    Γ ∋ α →
    ------------------------------------------------
    Γ , β ∋ α


-- examples
private

  _ : ø , `⊤ ∋ `⊤
  _ = head

  _ : ø , `⊤ , `⊤ `→ `⊤ ∋ `⊤ -- ø , `⊤ `→ `⊤ , `⊤ ∋ `⊤
  _ = tail head


-- utilities

lookup : ∀ {n} (Γ : Context n) (i : Fin n) → Type
lookup (Γ , α) zero = α
lookup (Γ , α) (suc i) = lookup Γ i


-- ==========================================
-- Terms
-- ==========================================
-- intrinsically typed terms correspond to the typing judgement


-- ``Γ ⊢ α`` is a term of type ``α`` in context ``Γ``.
data _⊢_ : ∀ {n} → Context n → Type → Set where

  `⊤ : ∀ {n} {Γ : Context n} →
    ------------------------------------------------
    Γ ⊢ `⊤

  -- `zero : ∀ {n} {Γ : Context n} →
  --   ------------------------------------------------
  --   `ℕ ⊣ Γ

  -- `suc : ∀ {n} {Γ : Context n} →
  --   ------------------------------------------------
  --   `ℕ ⊣ `ℕ , Γ

  `_ : ∀ {n} {α} {Γ : Context n} →
    (x : Γ ∋ α) →
    ------------------------------------------------
    Γ ⊢ α

  `λ_ : ∀ {n} {α β} {Γ : Context n} →
    (b : Γ , α ⊢ β) →
    ------------------------------------------------
    Γ ⊢ α `→ β

  _`∙_ : ∀ {n} {α β} {Γ : Context n} →
    (b : Γ ⊢ α `→ β) →
    (a : Γ ⊢ α) →
    ------------------------------------------------
    Γ ⊢ β


-- utilities

private
  count : ∀ {n} {Γ : Context n} (i : Fin n) → Γ ∋ lookup Γ i
  count {suc n} {Γ , α} zero = head
  count {suc n} {Γ , α} (suc i) = tail (count i)

-- abbreviation for names
`#_ : ∀ {m} n {Γ : Context (1 + n + m)} → Γ ⊢ lookup Γ (Fin.inject+ m (Fin.fromℕ n))
`#_ {m} n {Γ} = ` count (Fin.inject+ m (Fin.fromℕ n))

-- examples
private 

  `id : ∀ {n} {Γ : Context n} →
    Γ ⊢ `⊤ `→ `⊤
  `id =
    `λ `# 0

  `const : ∀ {n} {Γ : Context n} →
    Γ ⊢ `⊤ `→ `⊤ `→ `⊤
  `const =
    `λ `λ `# 0

  `apply : ∀ {n} {Γ : Context n} →
    Γ ⊢ (`⊤ `→ `⊤) `→ `⊤ `→ `⊤
  `apply =
    `λ `λ `# 1 `∙ `# 0

  -- `add : ∀ {n} {Γ : Context n} →
  --   `ℕ `→ `ℕ `→ `ℕ ⊣ Γ
  -- `add =
  --   `λ `λ {!!}


-- ==========================================
-- Substitution
-- ==========================================


-- extend lookup context by with a new binder
extend-∋ : ∀ {m n} {Γ : Context m} {Γ′ : Context n} →
  (∀ {α}   → Γ     ∋ α → Γ′     ∋ α) →
  (∀ {α β} → Γ , β ∋ α → Γ′ , β ∋ α)
extend-∋ F  head      = head
extend-∋ F (tail Γ∋α) = tail (F Γ∋α)


rename : ∀ {m n} {Γ : Context m} {Γ′ : Context n} →
  (∀ {α} → Γ ∋ α → Γ′ ∋ α) →
  (∀ {α} → Γ ⊢ α → Γ′ ⊢ α)
rename F  `⊤      = `⊤
rename F (` x)    = ` F x
rename F (`λ b)   = `λ rename (extend-∋ F) b
rename F (b `∙ a) = rename F b `∙ rename F a


-- examples
private

  M₀ : ø , `⊤ `→ `⊤ ⊢ `⊤ `→ `⊤
  M₀ = `λ (`# 1 `∙ (`# 1 `∙ `# 0))

  M₁ : ø , `⊤ `→ `⊤ , `⊤ ⊢ `⊤ `→ `⊤
  M₁ = `λ (`# 2 `∙ (`# 2 `∙ `# 0))

  _ : rename tail M₀ ≡ M₁
  _ = refl


-- extension of term by a new binder
extend-⊢ : ∀ {m n} {Γ : Context m} {Γ′ : Context n} →
  (∀ {α}   → Γ     ∋ α → Γ′     ⊢ α) →
  (∀ {α β} → Γ , β ∋ α → Γ′ , β ⊢ α)
extend-⊢ F  head    = ` head
extend-⊢ F (tail a) = rename tail (F a)


-- simultaneous substitution
substitute : ∀ {m n} {Γ : Context m} {Γ′ : Context n} →
  (∀ {α} → Γ ∋ α → Γ′ ⊢ α) →
  (∀ {α} → Γ ⊢ α → Γ′ ⊢ α)
substitute F  `⊤      = `⊤
substitute F (` x)    = F x
substitute F (`λ a)   = `λ substitute (extend-⊢ F) a
substitute F (b `∙ a) = substitute F b `∙ substitute F a


-- single substitution
[_]_ : ∀ {n} {Γ : Context n} {α} {β} →
  Γ     ⊢ α →
  Γ , α ⊢ β →
  ------------------------------------------------
  Γ     ⊢ β
[ b ] a = substitute (λ { head → b ; (tail x) → ` x }) a


-- ==========================================
-- Values
-- ==========================================


data _⊨_⇓ : ∀ {n} (Γ : Context n) {α} (a : Γ ⊢ α) → Set where

  `⊤⇓ : ∀ {n} {Γ : Context n} →
    ------------------------------------------------
    Γ ⊨ `⊤ ⇓


  `λ⇓ : ∀ {n} {Γ : Context n} {α β} {b : Γ , α ⊢ β} →
    ------------------------------------------------
    Γ ⊨ `λ b ⇓



-- data IsValue : ∀ {n} {Γ : Context n} {α} (a : Γ ⊢ α) → Set where

--   `⊤-IsValue : ∀ {n} {Γ : Context n} →
--     ------------------------------------------------
--     IsValue (`⊤ {n} {Γ})


--   `λ-IsValue : ∀ {n} {Γ : Context n} {α β} {b : Γ , α ⊢ β} →
--     ------------------------------------------------
--     IsValue (`λ b)


-- IsValue-syntax : ∀ {n} (Γ : Context n) {α} (a : Γ ⊢ α) → Set
-- IsValue-syntax {n} Γ {α} a = IsValue {n} {Γ} {α} a

-- syntax IsValue-syntax Γ a = ⇓ a ⊢ Γ

-- ==========================================
-- Reduction
-- ==========================================


data _⊨_↝_ : ∀ {n} (Γ : Context n) {α} (a a′ : Γ ⊢ α) → Set where

  applicant : ∀ {n} {Γ : Context n} {α β} {b b′ : Γ ⊢ α `→ β} {a : Γ ⊢ α} →
    Γ ⊨ b ↝ b′ →
    ------------------------------------------------
    Γ ⊨ b `∙ a ↝ b′ `∙ a

  argument : ∀ {n} {Γ : Context n} {α β} {b : Γ ⊢ α `→ β} {a a′ : Γ ⊢ α} →
    Γ ⊨ b ⇓ →
    Γ ⊨ a ↝ a′ →
    ------------------------------------------------
    Γ ⊨ b `∙ a ↝ b `∙ a′

  application : ∀ {n} {Γ : Context n} {α β} {b : Γ , α ⊢ β} {a : Γ ⊢ α} →
    Γ ⊨ a ⇓ →
    ------------------------------------------------
    Γ ⊨ (`λ b) `∙ a ↝ [ a ] b
    

data _⊨_↝*_ : ∀ {n} (Γ : Context n) {α} (a a′ : Γ ⊢ α) → Set where

  refl : ∀ {n} {Γ : Context n} {α} {a : Γ ⊢ α} →
    Γ ⊨ a ↝* a

  step : ∀ {n} {Γ : Context n} {α} {a a′ : Γ ⊢ α} →
    Γ ⊨ a ↝ a′ →
    Γ ⊨ a ↝* a′

  chain : ∀ {n} {Γ : Context n} {α} {a a′ a″ : Γ ⊢ α} →
    Γ ⊨ a  ↝  a′ →
    Γ ⊨ a′ ↝* a″ →
    Γ ⊨ a  ↝* a″


-- ↝*-isPartialOrder : IsPartialOrder _≡_ _↝*_


module ↝*-Reasoning where

  infix  1 _⊨begin_
  infixr 2 _↝⟨_⟩_
  infix  3 _∎

  _⊨begin_ : ∀ {n} (Γ : Context n) {α} {a a′ : Γ ⊢ α} → Γ ⊨ a ↝* a′ → Γ ⊨ a ↝* a′
  Γ ⊨begin a↝*a′ = a↝*a′

  _↝⟨_⟩_ : ∀ {n} {Γ : Context n} {α} (a : Γ ⊢ α) {a′ a″ : Γ ⊢ α} →
    Γ ⊨ a  ↝  a′ →
    Γ ⊨ a′ ↝* a″ →
    Γ ⊨ a  ↝* a″
  a ↝⟨ a↝a′ ⟩ a′↝*a″ = chain a↝a′ a′↝*a″

  _∎ : ∀ {n} {Γ : Context n} {α} (a : Γ ⊢ α) → Γ ⊨ a ↝* a
  a ∎ = refl


-- examples
private

  _ : ∀ {n} (Γ : Context n) → Γ ⊨ `id `∙ `⊤ ↝* `⊤ 
  _ = λ Γ →
    Γ ⊨begin
      `id `∙ `⊤
    ↝⟨ application `⊤⇓ ⟩
      `⊤
    ∎
    where open ↝*-Reasoning


-- ==========================================
-- Progress
-- ==========================================


-- A closed term ``a`` is ``Progressive`` if and only if
-- it is either a value or reduces.
data Progressive {α} (a : ø ⊢ α) : Set where

  step : ∀ {a′} →
    ø ⊨ a ↝ a′ →
    ------------------------------------------------
    Progressive a

  done :
    ø ⊨ a ⇓ →
    ------------------------------------------------
    Progressive a


-- all closed terms are ``Progressive``
progress : ∀ {α} (a : ø ⊢ α) → Progressive a
progress `⊤            = done `⊤⇓
progress (`λ a)        = done `λ⇓
progress (b `∙ a)   with progress b   | progress a
progress (b `∙ a)      | step b↝b′  | _ = step (applicant b↝b′)
progress (b `∙ a)      | done b⇓      | step a↝a′ = step (argument b⇓ a↝a′)
progress ((`λ b) `∙ a) | done `λ⇓     | done a⇓ = step (application a⇓)


-- ==========================================
-- Evaluation
-- ==========================================


-- record Gas : Set where
--   constructor gas
--   field
--     amount : ℕ


-- data Finished {n} {Γ : Context n} {α} (a : Γ ⊢ α) : Set where

--   done :
--     Γ ⊨ a ⇓ →
--     ------------------------------------------------
--     Finished a

--   empty :
--     ------------------------------------------------
--     Finished a


-- data Steps {α} : ø ⊢ α → Set where

--   steps : {a a′ : ø ⊢ α} →
--     ø ⊨ a ↝* a′ →
--     Finished a′ →
--     ------------------------------------------------
--     Steps a


{-# TERMINATING #-}
evaluate : ∀ {α} → (a : ø ⊢ α) → ∃[ v ] ((ø ⊨ v ⇓) × (ø ⊨ a ↝* v))
evaluate a with progress a
evaluate a | step {a′} a↝a′ with evaluate a′
evaluate a | step {a′} a↝a′    | (a″ & a″⇓ & a′↝*a″) = a″ & a″⇓ & chain a↝a′ a′↝*a″
evaluate a | done a⇓ = a & a⇓ & refl


-- examples
private

  _ : evaluate `⊤ ≡ (`⊤ & _)
  _ = refl

  _ : evaluate ((`λ `# 0) `∙ `⊤) ≡ (`⊤ & _)
  _ = refl
