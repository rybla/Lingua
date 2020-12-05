open import Level using (0ℓ)
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Nat as Nat
  using (ℕ; zero)
  renaming (suc to 1+)
import Data.Nat.Properties as NatProperties
open import Data.Product
  using (∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to _&_)
open import Data.Sum as Sum
  using (_⊎_; [_,_]; inj₁; inj₂)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_)
  
  
-- open import Data.Maybe using (Maybe; just; nothing; maybe)
-- import Data.Maybe.Categorical as MaybeCategorical
-- import Category.Monad as Monad
-- open Monad.RawMonadPlus (MaybeCategorical.monadPlus {Level.zero})

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.DecidableEquality
open import Language.Lambda.Grammar.Properties
open import Language.Lambda.Typing


module Language.Lambda.Reducing where


-- ================================================================
-- Reducing
-- ================================================================


-- infixr 17 [_]_
-- infix 10 _⟿_ _⟿*_ -- _⇓_

-- ----------------------------------------------------------------
-- Substitution
-- ----------------------------------------------------------------


-- downshift : ∀ {n} (Γ : Context (1+ n)) → Context n
-- downshift 


-- substitute : ∀ {n} {a : Term (1+ n)} {x : Term 0} {Γ : Context n} {α ξ} →
--   n ⦂ ξ , Γ ⊢ a ⦂ α →
--   ø ⊢ x ⦂ ξ →
--   ∃[ a′ ] (Γ ⊢ a′ ⦂ α)
-- -- substitute {n} {a} {x} {Γ} {α} {ξ} J₁ J₂ = {!!}
-- substitute {.0} {` 0} {x} {ø} {α} {.α} name ø⊢x⦂ξ = x & ø⊢x⦂ξ
-- substitute {.(1+ n)} {` 1+ n} {x} {.n ⦂ β , Γ} {α} {.α} name ø⊢x⦂ξ = {!!}
-- -- (` n) & {!!}
-- substitute {n} {a `∙ a₁} {x} {Γ} {α} {ξ} J₁ J₂ = {!!}
-- substitute {n} {`λ .(1+ n) `⦂ α₁ `⇒ a} {x} {Γ} {α} {ξ} J₁ J₂ = {!!}
-- substitute {n} {`↑ a} {x} {Γ} {α} {ξ} J₁ J₂ = {!!}


-- substitute {.0} {` zero} {x} {ø} {α} {.α} name ø⊢x⦂ξ = x & ø⊢x⦂ξ
-- substitute {.(1+ n)} {` 1+ n} {x} {ø} {α} {.α} name ø⊢x⦂ξ = ` n & {!!}
-- substitute {.(1+ n)} {` 1+ n} {x} {.n ⦂ x₁ , Γ} {α} {ξ} n⦂ξ,Γ⊢a⦂α ø⊢x⦂ξ = {!!}
-- substitute {n} {a `∙ a₁} {x} {Γ} {α} {ξ} n⦂ξ,Γ⊢a⦂α ø⊢x⦂ξ = {!!}
-- substitute {n} {`λ .(1+ n) `⦂ α₁ `⇒ a} {x} {Γ} {α} {ξ} n⦂ξ,Γ⊢a⦂α ø⊢x⦂ξ = {!!}
-- substitute {n} {`↑ a} {x} {Γ} {α} {ξ} n⦂ξ,Γ⊢a⦂α ø⊢x⦂ξ = {!!}
  
  


-- [_]_ : ∀ {n} → Term 0 → Term (1+ n) → Term n
-- [ x ] (` 0) = x
-- [ x ] (` 1+ n) = ` n
-- [ x ] (a `∙ b) = [ x ] a `∙ [ x ] b
-- [ x ] (`λ 1+ n `⦂ α `⇒ b) = `λ n `⦂ α `⇒ [ x ] b
-- [ x ] (`↑ a) = a


-- -- ----------------------------------------------------------------
-- -- Small-Step Reduction
-- -- ----------------------------------------------------------------

-- -- ``Γ ⊢ a ⟿ b`` is the type of proofs that ``a`` small-step-reduces to ``b``
-- data _⟿_ : ∀ {n} → Rel (Term n) 0ℓ

-- -- ``is-value a`` is the type of proofs that ``a : Term n`` is a value
-- data is-value : ∀ {n} (a : Term n) → Set


-- data _⟿_ where
--   argument : ∀ {n} {a b b′ : Term n} →
--     b ⟿ b′ →
--     ------------------------------------------------------
--     a `∙ b ⟿ a `∙ b′

--   applicant : ∀ {n} {a a′ b : Term n} → 
--     is-value b →
--     a ⟿ a′ →
--     ------------------------------------------------------
--     a `∙ b ⟿ a′ `∙ b 

--   application : ∀ {a : Term 0} {b : Term 1} {α} →
--     ------------------------------------------------------
--     (`λ 0 `⦂ α `⇒ b) `∙ a ⟿ [ a ] b


-- data is-value where
--   `1 :
--     ------------------------------------------------------
--     is-value `1

--   function : ∀ {n} {b : Term (1+ n)} {α} →
--     ------------------------------------------------------
--     is-value (`λ n `⦂ α `⇒ b)


-- -- ----------------------------------------------------------------
-- -- Large-Step Reduction
-- -- ----------------------------------------------------------------


-- data _⟿*_ : ∀ {n} → Rel (Term n) 0ℓ where

--   refl : ∀ {n} {a : Term n} →
--     a ⟿* a

--   step : ∀ {n} {a a′ : Term n} →
--     a ⟿ a′ →
--     a ⟿* a′

--   chain : ∀ {n} {a a′ a″ : Term n} →
--     a ⟿ a′ →
--     a′ ⟿* a″ →
--     a ⟿* a″


-- ⟿*-isPartialOrder : ∀ {n} → IsPartialOrder _≡_ (_⟿*_ {n})
-- ⟿*-isPartialOrder {n} = record { isPreorder =
--                                                   record { isEquivalence = PE.isEquivalence
--                                                                 ; reflexive = reflexive
--                                                                 ; trans = trans }
--                                                                 ; antisym = antisym }
--   where
--     trans  : ∀ {n} → Transitive (_⟿*_ {n})
--     trans {n} {a} {.a} {a″} refl a′⟿*a″ = a′⟿*a″
--     trans {n} {a} {a′} {a″} (step a⟿a′) a′⟿*a″ = chain a⟿a′ a′⟿*a″
--     trans {n} {a} {a′} {a″} (chain a⟿b b⟿*a′) a′⟿*a″ = chain a⟿b (trans b⟿*a′ a′⟿*a″)

--     reflexive : ∀ {n} → _≡_ ⇒ (_⟿*_ {n})
--     reflexive {n} {a} {b} PE.refl = refl

--     postulate
--       antisym : ∀ {n} → Antisymmetric _≡_ (_⟿*_ {n})
--       -- antisym {n} {a} {a′} a⟿*a′ a′⟿*a = {!!}



-- ----------------------------------------------------------------
-- Progress
-- ----------------------------------------------------------------



-- ----------------------------------------------------------------
-- Preservation
-- ----------------------------------------------------------------

-- substitution-preservation :
--   Γ ⊢ a ⦂ α →
--   Γ ⊢ b ⦂ β →
--   Γ ⊢ [ a ] b ⦂ β


-- preservation : ∀ {n} {Γ} {a a′ : Term n} {α} →
--   Γ ⊢ a ⦂ α →
--   a ⟿* a′ →
--   ------------------------------------------------------
--   Γ ⊢ a′ ⦂ α
-- preservation {.0} {Γ} {`1} {.`1} {α} Γ⊢a⦂α refl = Γ⊢a⦂α

-- preservation {.(1+ n)} {Γ} {` n} {.(` n)} {α} Γ⊢a⦂α refl = Γ⊢a⦂α

-- preservation {n} {Γ} {c `∙ d} {.c `∙ .d} {α} Γ⊢a⦂α refl = Γ⊢a⦂α
-- preservation {n} {Γ} {c `∙ d} {.c `∙ d′} {α} (application Γ⊢c⦂β→α Γ⊢d⦂β) (step (argument d⟿d′)) = application Γ⊢c⦂β→α (preservation Γ⊢d⦂β (step d⟿d′))
-- preservation {n} {Γ} {c `∙ d} {.(_ `∙ d)} {α} (application J1 J2) (step (applicant is-value-d c⟿a′)) = application (preservation J1 (step c⟿a′)) J2
-- preservation {.0} {Γ} {(`λ 0 `⦂ β `⇒ b) `∙ c} {.([ c ] b)} {α} (application J₁ J₂) (step application) = {!!}
-- preservation {n} {Γ} {a `∙ b} {a′} {α} Γ⊢a⦂α (chain x a⟿*a′) = {!!}

-- preservation {n} {Γ} {`λ .n `⦂ α₁ `⇒ a} {a′} {α} Γ⊢a⦂α a⟿*a′ = {!!}

-- preservation {.(1+ _)} {Γ} {`↑ a} {a′} {α} Γ⊢a⦂α a⟿*a′ = {!!}

-- -- ----------------------------------------------------------------
-- -- Evaluation
-- -- ----------------------------------------------------------------


-- _⇓_ : ∀ {n} → Rel (Term n) 0ℓ
-- a ⇓ v = a ⟿* v × is-value v


-- evaluate : ∀ (a : Term 0) → ∃[ v ] (a ⇓ v)
-- evaluate `1 = `1 , refl , `1
-- evaluate (`1 `∙ b) = {!!}
-- evaluate ((a `∙ a₁) `∙ b) = {!!}
-- evaluate ((`λ .0 `⦂ α `⇒ a) `∙ b) = {!!}
-- evaluate (`λ .0 `⦂ α `⇒ a) = {!!}



-- evaluate : ∀ {n} (a : Term n) → Dec  (∃[ v ] (a ⇓ v))
