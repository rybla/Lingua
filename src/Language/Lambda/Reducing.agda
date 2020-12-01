import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
  renaming ([_] to ≡[_])
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat as Nat using (ℕ; zero) renaming (suc to 1+)
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin) renaming (zero to #0; suc to #1+)
import Data.Fin.Properties as FinProperties
open import Data.Product
  using (∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to _&_)
-- open import Data.List using (List; []; _∷_; [_]; _++_)

open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe.Categorical as MaybeCategorical
import Category.Monad as Monad
open Monad.RawMonadPlus (MaybeCategorical.monadPlus {Level.zero})

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.DecidableEquality
open import Language.Lambda.Grammar.Properties
open import Language.Lambda.Typing


module Language.Lambda.Reducing where


-- ================================================================
-- Reducing
-- ================================================================

infixr 17 _↦_,_
infixr 18 _↦_
infixr 16 [_]_


-- ----------------------------------------------------------------
-- Substitution
-- ----------------------------------------------------------------


-- substitution
data Substitution : Set where
  ø : Substitution
  _↦_,_ : ∀ n → Term n → Substitution → Substitution

_↦_ : ∀ n → Term n → Substitution
x ↦ t = x ↦ t , ø


-- -- without
-- _⊝_ : Substitution → Name → Substitution
-- ∙-substitution ⊝ x = ∙-substitution
-- (x ↦ t , subs) ⊝ y with x Name.≟ y
-- ... | yes _ = subs ⊝ y
-- ... | no  _ = x ↦ t , subs ⊝ y

-- substitute
[_]_ : ∀ {n} → Substitution → Term n → Term n
[ ø ] t = t
[ n ↦ t′ , subs ] (` m) with n Nat.≟ 1+ m
[ n ↦ t′ , subs ] (` m)    | yes refl = t′
[ n ↦ t′ , subs ] (` m)    | no  n≢m  = [ subs ] (` m)
[ subs ] (s `⋆ t) = [ subs ] s `⋆ [ subs ] t
[ subs ] (`λ _ `⦂ x₁ `⇒ t) = {!!}
[ subs ] (`↑ t) = {!!}
-- [ ∙-substitution ]# t = t
-- [ x ↦ s , subs ]# (` y) with x Name.≟ y
-- ... | yes _ = s
-- ... | no  _ = ` y
-- [ x ↦ s , subs ]# (t `⋆ u) = [ x ↦ s , subs ]# t `⋆ [ x ↦ s , subs ]# u
-- [ subs@(_ ↦ _ , _) ]# (`λ y `⦂ τ `⇒ t) = `λ y `⦂ τ `⇒ [ subs ⊝ y ]# t


-- -- small-step reductions
-- infix 10 _⟶_
-- data _⟶_ : Term → Term → Set where
--   reduce-argument : ∀ s t t′ →
--     t ⟶ t′ →
--     s `⋆ t ⟶ s `⋆ t′
--   reduce-application : ∀ x τ s t →
--     (`λ x `⦂ τ `⇒ s) `⋆ t ⟶ [ x ↦ t ]# s


-- -- value predicate
-- IsValue : Term → Set
-- IsValue t = ¬ (∃[ t′ ] (t ⟶ t′))


-- -- big-step reductions
-- infix 10 _⟶*_
-- data _⟶*_ : Term → Term → Set where
--   reduce*-id : ∀ t → t ⟶* t
--   reduct*-lift : ∀ t t′ →
--     t ⟶ t′ →
--     t ⟶* t′
--   reduce*-argument : ∀ s t t′ →
--     t ⟶* t′ →
--     s `⋆ t ⟶* s `⋆ t′
--   reduce*-applicant : ∀ s s′ t →
--     IsValue t →
--     s ⟶* s′ →
--     s `⋆ t ⟶* s′ `⋆ t
    

-- -- evaluation
-- _⇓_ : Term → Term → Set
-- t ⇓ v = t ⟶* v × IsValue v


-- -- strongly normalziing
