open import Function using (_∘_)
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

infixr 6 `λ_ `μ_
infixr 7 `ε_[_∣_]
infixl 8 _`∙_
infix  9 [_]_
infixl 10 `suc_
infix  11 `_ `#_


-- ===================================================================
-- Types
-- ===================================================================


-- type data
data Type : Set where
  `⊤ : Type
  `ℕ : Type
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

  _ : ø , `⊤ , `⊤ `→ `⊤ ∋ `⊤
  _ = tail head


-- utilities

lookup : ∀ {n} (Γ : Context n) (i : Fin n) → Type
lookup (Γ , α) zero = α
lookup (Γ , α) (suc i) = lookup Γ i


-- ===================================================================
-- Terms
-- ===================================================================
-- intrinsically typed terms correspond to the typing judgement


-- ``Γ ⊢ α`` is a term of type ``α`` in context ``Γ``.
data _⊢_ : ∀ {n} → Context n → Type → Set where

  -- unit value
  `⊤ : ∀ {n} {Γ : Context n} →
    ------------------------------------------------
    Γ ⊢ `⊤

  -- natural zero
  `zero : ∀ {n} {Γ : Context n} →
    ------------------------------------------------
    Γ ⊢ `ℕ

  -- natural successor
  `suc_ : ∀ {n} {Γ : Context n} →
    Γ ⊢ `ℕ →
    ------------------------------------------------
    Γ ⊢ `ℕ

  -- natural elimination (i.e. pattern matching)
  `ε_[_∣_] : ∀ {n} {α} {Γ : Context n} →
    Γ      ⊢ `ℕ →
    Γ      ⊢ α  →
    Γ , `ℕ ⊢ α  →
    ------------------------------------------------
    Γ ⊢ α

  -- name
  `_ : ∀ {n} {α} {Γ : Context n} →
    (x : Γ ∋ α) →
    ------------------------------------------------
    Γ ⊢ α

  -- function
  `λ_ : ∀ {n} {α β} {Γ : Context n} →
    (b : Γ , α ⊢ β) →
    ------------------------------------------------
    Γ ⊢ α `→ β

  -- fixpoint
  `μ_ : ∀ {n} {α} {Γ : Context n} →
    (a : Γ , α ⊢ α) →
    ------------------------------------------------
    Γ ⊢ α

  -- function application
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

  `id : ∀ {n} {Γ : Context n} → Γ ⊢ `⊤ `→ `⊤
  `id = `λ `# 0

  `const : ∀ {n} {Γ : Context n} → Γ ⊢ `⊤ `→ `⊤ `→ `⊤
  `const = `λ `λ `# 0

  `apply : ∀ {n} {Γ : Context n} → Γ ⊢ (`⊤ `→ `⊤) `→ `⊤ `→ `⊤
  `apply = `λ `λ `# 1 `∙ `# 0

  `0 : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
  `0 = `zero

  `1 : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
  `1 = `suc `0

  `add : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ `→ `ℕ `→ `ℕ
  `add = `μ `λ `λ `ε `# 1 [ `# 0 ∣ `suc (`# 3 `∙ `# 0 `∙ `# 1) ]

  `2 : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
  `2 = `add `∙ `1 `∙ `1

  `3 : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
  `3 = `add `∙ `1 `∙ `2

  `4 : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
  `4 = `add `∙ `1 `∙ `3


-- ===================================================================
-- Substitution
-- ===================================================================


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
rename F `zero    = `zero
rename F (`suc n) = `suc (rename F n)
rename F (` x)    = ` F x
rename F (`λ b)   = `λ rename (extend-∋ F) b
rename F (`μ a)   = `μ rename (extend-∋ F) a
rename F (b `∙ a) = rename F b `∙ rename F a
rename F (`ε n [ a₁ ∣ a₂ ]) = `ε rename F n [ rename F a₁ ∣ rename (extend-∋ F) a₂ ]


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
substitute F `zero = `zero
substitute F (`suc n) = `suc substitute F n
substitute F (` x)    = F x
substitute F (`λ b)   = `λ substitute (extend-⊢ F) b
substitute F (`μ a) = `μ substitute (extend-⊢ F) a
substitute F (b `∙ a) = substitute F b `∙ substitute F a
substitute F (`ε n [ a₁ ∣ a₂ ]) = `ε substitute F n [ substitute F a₁ ∣ substitute (extend-⊢ F) a₂ ]



-- single substitution
[_]_ : ∀ {n} {Γ : Context n} {α} {β} →
  Γ     ⊢ α →
  Γ , α ⊢ β →
  ------------------------------------------------
  Γ     ⊢ β
[ b ] a = substitute (λ { head → b ; (tail x) → ` x }) a


-- ===================================================================
-- Values
-- ===================================================================


data _⊨_⇓ : ∀ {n} (Γ : Context n) {α} (a : Γ ⊢ α) → Set where

  ⊤⇓ : ∀ {n} {Γ : Context n} →
    ------------------------------------------------
    Γ ⊨ `⊤ ⇓

  zero⇓ : ∀ {n} {Γ : Context n} →
    ------------------------------------------------
    Γ ⊨ `zero ⇓

  suc⇓ : ∀ {n} {Γ : Context n} {n : Γ ⊢ `ℕ} →
    ------------------------------------------------
    Γ ⊨ n ⇓ →
    Γ ⊨ `suc n ⇓


  `λ⇓ : ∀ {n} {Γ : Context n} {α β} {b : Γ , α ⊢ β} →
    ------------------------------------------------
    Γ ⊨ `λ b ⇓


-- ===================================================================
-- Reduction
-- ===================================================================


data _⊨_↝_ : ∀ {n} (Γ : Context n) {α} (a a′ : Γ ⊢ α) → Set where

  suc-argument : ∀ {n} {Γ : Context n} {n n′ : Γ ⊢ `ℕ} →
    Γ ⊨ n ↝ n′ →
    ------------------------------------------------
    Γ ⊨ `suc n ↝ `suc n′

  λ-applicant : ∀ {n} {Γ : Context n} {α β} {b b′ : Γ ⊢ α `→ β} {a : Γ ⊢ α} →
    Γ ⊨ b ↝ b′ →
    ------------------------------------------------
    Γ ⊨ b `∙ a ↝ b′ `∙ a

  λ-argument : ∀ {n} {Γ : Context n} {α β} {b : Γ ⊢ α `→ β} {a a′ : Γ ⊢ α} →
    Γ ⊨ b ⇓ →
    Γ ⊨ a ↝ a′ →
    ------------------------------------------------
    Γ ⊨ b `∙ a ↝ b `∙ a′

  λ-application : ∀ {n} {Γ : Context n} {α β} {b : Γ , α ⊢ β} {a : Γ ⊢ α} →
    Γ ⊨ a ⇓ →
    ------------------------------------------------
    Γ ⊨ (`λ b) `∙ a ↝ [ a ] b

  application-μ : ∀ {n} {Γ : Context n} {α} {a : Γ , α ⊢ α} →
    Γ ⊨ `μ a ↝ [ `μ a ] a

  ε-discriminant : ∀ {n} {Γ : Context n} {α} {n n′ : Γ ⊢ `ℕ} {a₁ : Γ ⊢ α} {a₂ : Γ , `ℕ ⊢ α} →
    Γ ⊨ n ↝ n′ →
    Γ ⊨ `ε n [ a₁ ∣ a₂ ] ↝ `ε n′ [ a₁ ∣ a₂ ]

  ε-zero : ∀ {n} {Γ : Context n} {α} {a₁ : Γ ⊢ α} {a₂ : Γ , `ℕ ⊢ α} →
    Γ ⊨ `ε `zero [ a₁ ∣ a₂ ] ↝ a₁

  ε-suc : ∀ {n} {Γ : Context n} {α} {n : Γ ⊢ `ℕ} {a₁ : Γ ⊢ α} {a₂ : Γ , `ℕ ⊢ α} →
    Γ ⊨ `ε `suc n [ a₁ ∣ a₂ ] ↝ [ n ] a₂
    

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

  _ : ø ⊨ `id `∙ `⊤ ↝* `⊤ 
  _ = 
    ø ⊨begin
      `id `∙ `⊤
    ↝⟨ λ-application ⊤⇓ ⟩
      `⊤
    ∎
    where open ↝*-Reasoning


-- ===================================================================
-- Progress
-- ===================================================================


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
progress `⊤                         = done ⊤⇓
progress `zero                      = done zero⇓
progress (`suc n)                with progress n
progress (`suc n)                   | step n↝n′ = step (suc-argument n↝n′)
progress (`suc n)                   | done n⇓   = done (suc⇓ n⇓)
progress (`λ b)                     = done `λ⇓
progress (`μ a)                     = step application-μ
progress (b `∙ a)                with progress b | progress a
progress (b `∙ a)                   | step b↝b′  | _         = step (λ-applicant       b↝b′)
progress (b `∙ a)                   | done b⇓    | step a↝a′ = step (λ-argument     b⇓ a↝a′)
progress ((`λ b) `∙ a)              | done `λ⇓   | done a⇓   = step (λ-application a⇓)
progress (`ε n      [ a₁ ∣ a₂ ]) with progress n
progress (`ε n      [ a₁ ∣ a₂ ])    | step n↝n′ = step (ε-discriminant n↝n′)
progress (`ε `zero  [ a₁ ∣ a₂ ])    | done _    = step ε-zero
progress (`ε `suc n [ a₁ ∣ a₂ ])    | done _    = step ε-suc


-- ===================================================================
-- Evaluation
-- ===================================================================


Gas : Set
Gas = ℕ

data EvaluationStatus {n} {Γ : Context n} {α} (a : Γ ⊢ α) : Set where

  evaluated :
    Γ ⊨ a ⇓ →
    ------------------------------------------------
    EvaluationStatus a

  truncated :
    ------------------------------------------------
    EvaluationStatus a


record Result {α} (a : ø ⊢ α) : Set where
  constructor result
  field
    value     : ø ⊢ α
    reduction : ø ⊨ a ↝* value
    status    : EvaluationStatus value

open Result


module _ where
  open ↝*-Reasoning

  evaluate :
    Gas →
    ∀ {α} → (a : ø ⊢ α) →
    Result a
  evaluate zero      a    = result a refl truncated
  evaluate (suc gas) a with progress a
  evaluate (suc gas) a    | done a⇓ = result a refl (evaluated a⇓)
  evaluate (suc gas) a    | step {a′} a↝a′ with evaluate gas a′
  evaluate (suc gas) a    | step {a′} a↝a′    | result a″ a′↝a″ status = result a″ (a ↝⟨ a↝a′ ⟩ a′↝a″) status


-- examples
private

  _ : value (evaluate 1 `⊤) ≡ `⊤
  _ = refl

  _ : value (evaluate 1 ((`λ `# 0) `∙ `⊤)) ≡ `⊤
  _ = refl

  -- infinite loop
  _ : status (evaluate 10 (`μ `suc `# 0)) ≡ truncated
  _ = refl

  _ : (value ∘ evaluate 30) (`add `∙ `2 `∙ `2)
    ≡ (value ∘ evaluate 24)  `4
  _ = refl
