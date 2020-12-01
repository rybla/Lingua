open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Data.Nat as Nat renaming (suc to 1+)
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin) renaming (zero to #0; suc to #1+)

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.DecidableEquality


module Language.Lambda.Grammar.Properties where


-- infix 11 _⊴_
-- data _⊴_ : ∀ {n} → Term (1+ n) → ℕ → Set where

--   name : ∀ {n} {i : Fin (1+ n)} →
--     n ≢ Fin.toℕ i →
--     ` i ⊴ 1+ n

--   application : ∀ {n} {s t : Term (1+ n)} →
--     s ⊴ 1+ n →
--     t ⊴ 1+ n →
--     s `⋆ t ⊴ 1+ n

--   -- you cannot lower functions,
--   -- since they automatically rename

-- lower₁ : ∀ {n} (t : Term (1+ n)) → t ⊴ (1+ n) → Term n
-- lower₁ {n} (` i) (name n≢to-i) = ` (Fin.lower₁ i n≢to-i)
-- lower₁ {n} (s `⋆ t) (application s⊴ t⊴) = (lower₁ s s⊴) `⋆ lower₁ t t⊴
-- lower₁ {n} (`λ .(1+ n) `⦂ τ `⇒ t) ()

