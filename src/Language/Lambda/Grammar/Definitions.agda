open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality

open import Data.Nat as Nat using (ℕ; zero; _+_) renaming (suc to 1+)
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin) renaming (zero to #0; suc to #1+)


module Language.Lambda.Grammar.Definitions where


-- ================================================================
-- Definitions
-- ================================================================


infixr 15 _`→_

infixr 15 `_
infixr 14 `↑_ `↑+_
infixr 13 _`∙_
infixr 12 `λ_`⦂_`⇒_


-- ----------------------------------------------------------------
-- Type
-- ----------------------------------------------------------------


data Type : Set where
  `𝟘   : Type
  `𝟙   : Type
  _`→_ : ∀ (α β : Type) → Type


-- examples

`𝟙→𝟙 : Type
`𝟙→𝟙 = `𝟙 `→ `𝟙


-- ================================================================
-- Term
-- ================================================================

-- ``t : Term n`` is a term with ``n`` free names
data Term : ℕ → Set where
  `1 : Term 0
  `_ : ∀ n  → Term (1+ n)
  _`∙_ : ∀ {n} (a b : Term n) → Term n
  `λ_`⦂_`⇒_ : ∀ n (α : Type) (b : Term (1+ n)) → Term n
  `↑_ : ∀ {n} (a : Term n) → Term (1+ n)


-- utilities


-- if m ≡ n, then an m-Term is also an n-Term
cast : ∀ {m} {n} → m ≡ n → Term m → Term n
cast m≡n t rewrite m≡n = t

`↑+_ : ∀ {m} {n} → Term n → Term (m + n)
`↑+_ {zero} {n} t = t
`↑+_ {1+ m} {n} t = `↑ (`↑+ t)


-- examples

`id : Term 0
`id = `λ 0 `⦂ `𝟙 `⇒ ` 0 -- `λ 0 `⦂ `𝟙 `⇒ ` 0

`const : Term 0
`const = `λ 0 `⦂ `𝟙 `⇒ `λ 1 `⦂ `𝟙 `⇒ ` 1

`apply : Term 0
`apply = `λ 0 `⦂ `𝟙→𝟙 `⇒ `λ 1 `⦂ `𝟙 `⇒ (`↑ ` 0) `∙ ` 1

