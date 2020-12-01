import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality -- hiding ([_])
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
open import Data.List using (List; []; _∷_; [_]; _++_)

open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe.Categorical as MaybeCategorical
import Category.Monad as Monad
open Monad.RawMonadPlus (MaybeCategorical.monadPlus {Level.zero})

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.DecidableEquality
open import Language.Lambda.Grammar.Properties


module Language.Lambda.Typing where


-- ================================================================
-- Typing
-- ================================================================


-- ----------------------------------------------------------------
-- Typing Context
-- ----------------------------------------------------------------

infixr 18 _⦂_
infixr 17 _⦂_,_
infix  10 _⊢_⦂_

-- context
data Context : ℕ → Set where
  ø     : ∀ {n} → Context n
  _⦂_,_ : ∀ n → Type → Context n → Context (1+ n)

_⦂_ : ∀ n → Type → Context (1+ n)
x ⦂ τ = x ⦂ τ , ø


-- ----------------------------------------------------------------
-- Type Judgment
-- ----------------------------------------------------------------

data _⊢_⦂_ : ∀ {n} → Context n → Term n → Type → Set where

  name : ∀ {n} {Γ : Context n} {τ} →
    ------------------------------------------------------
    n ⦂ τ , Γ ⊢ ` n ⦂ τ

  function : ∀ {n} {Γ : Context n} {t : Term (1+ n)} {σ τ} →
    n ⦂ σ , Γ ⊢ t ⦂ τ →
    ---------------------------------------------
    Γ ⊢ `λ n `⦂ σ `⇒ t ⦂ σ `→ τ

  application : ∀ {n} {Γ : Context n} {s t : Term n} {σ τ} →
    Γ ⊢ s ⦂ σ `→ τ →
    Γ ⊢ t ⦂ σ →
    ---------------------------------------------
    Γ ⊢ s `⋆ t ⦂ τ

  injection : ∀ {n} {Γ : Context n} {t : Term n} {σ τ} →
    Γ ⊢ t ⦂ τ →
    ------------------------------------------------------
    n ⦂ σ , Γ ⊢ `↑ t ⦂ τ


-- lemmas

⊢-injective : ∀ {n} {Γ : Context n} {t : Term n} {τ τ′} →
  Γ ⊢ t ⦂ τ →
  Γ ⊢ t ⦂ τ′ →
  ------------------------------
  τ ≡ τ′
-- name
⊢-injective {.(1+ n)} {.(n ⦂ τ , _)} {` n} {τ} {τ′} name name = refl
-- application
⊢-injective {n} {Γ} {s `⋆ t} {τ} {τ′}
  (application {.n} {.Γ} {.s} {.t} {σ } {.τ } Γ⊢s⦂σ→τ   Γ⊢t⦂τ)
  (application {.n} {.Γ} {.s} {.t} {σ′} {.τ′} Γ⊢s⦂σ′→τ′ Γ⊢t⦂τ′)
  with ⊢-injective Γ⊢s⦂σ→τ Γ⊢s⦂σ′→τ′ | ⊢-injective Γ⊢t⦂τ Γ⊢t⦂τ′
... | refl | refl = refl
-- function
⊢-injective {n} {Γ} {`λ .n `⦂ σ `⇒ t} {.σ `→ τ} {.σ `→ τ′}
  (function {.n} {.Γ} {.t} {.σ} {τ } n⦂σ,Γ⊢t⦂τ)
  (function {.n} {.Γ} {.t} {.σ} {τ′} n⦂σ,Γ⊢t⦂τ′)
  with ⊢-injective n⦂σ,Γ⊢t⦂τ n⦂σ,Γ⊢t⦂τ′
... | refl = refl
-- injection
⊢-injective {1+ n} {.n ⦂ σ , Γ} {`↑ t} {τ} {τ′}
  (injection {.n} {.Γ} {.t} {.σ} {.τ } Γ⊢t⦂τ)
  (injection {.n} {.Γ} {.t} {.σ} {.τ′} Γ⊢t⦂τ′)
  with ⊢-injective Γ⊢t⦂τ Γ⊢t⦂τ′
... | refl = refl

-- examples

_ : 1 ⦂ `⊤ `→ `⊤ , 0 ⦂ `⊤ ⊢ ` 1 `⋆ `↑ ` 0 ⦂ `⊤
_ = application name (injection name)

_ : ø ⊢ `id ⦂ `⊤ `→ `⊤
_ = function name

_ : ø ⊢ `const ⦂ `⊤ `→ (`⊤ `→ `⊤)
_ = function (function name)

_ : ø ⊢ `apply ⦂ (`⊤ `→ `⊤) `→ `⊤ `→ `⊤
_ = function (function (application (injection name) name))


-- ----------------------------------------------------------------
-- Type Inference and Checking
-- ----------------------------------------------------------------


-- type unification
unify : ∀ (σ τ : Type) → Dec (∃[ ρ ] ((σ ≡ ρ) × (τ ≡ ρ)))
unify σ τ with σ Type.≟ τ
...          | yes σ≡τ = yes (τ & σ≡τ & refl)
...          | no  σ≢τ = no λ { (ρ & σ≡ρ & τ≡ρ) → ⊥-elim (σ≢τ (trans σ≡ρ (sym τ≡ρ))) }

unify-application : ∀ (σ τ : Type) → Dec (∃[ ρ ] (σ ≡ τ `→ ρ))
unify-application `⊤ τ = no λ ()
unify-application (τ `→ ρ)  τ′ with τ Type.≟ τ′
unify-application (τ `→ ρ) .τ     | yes refl = yes (ρ & refl)
unify-application (τ `→ ρ)  τ′    | no  τ≢τ′ = no λ { (ρ & refl) → τ≢τ′ refl }


-- type inference
infer : ∀ {n} (Γ : Context n) (t : Term n) → Dec (∃[ τ ] (Γ ⊢ t ⦂ τ))
-- name
infer {1+ n}           ø  (` .n) = no λ ()
infer {1+ n} (.n ⦂ τ , Γ) (` .n) = yes (τ & name)
-- application
infer {n} Γ (s `⋆ t) with infer Γ s               | infer Γ t
infer {n} Γ (s `⋆ t)    | yes (σ & Γ⊢s⦂σ)         | yes (τ & Γ⊢t⦂τ) with unify-application σ τ
infer {n} Γ (s `⋆ t)    | yes (.(τ `→ ρ) & Γ⊢s⦂σ) | yes (τ & Γ⊢t⦂τ)    | yes (ρ & refl) = yes (ρ & (application Γ⊢s⦂σ Γ⊢t⦂τ))
infer {n} Γ (s `⋆ t)    | yes (σ & Γ⊢s⦂σ)         | yes (τ & Γ⊢t⦂τ)    | no ∄[ρ]σ≡τ→ρ   = no λ { (ρ & application {.n} {.Γ} {.s} {.t} {ν} {.ρ} Γ⊢s⦂ν→ρ Γ⊢t⦂ν) →
                                                                                                 ∄[ρ]σ≡τ→ρ (ρ & helper Γ⊢s⦂σ Γ⊢t⦂τ Γ⊢s⦂ν→ρ Γ⊢t⦂ν ∄[ρ]σ≡τ→ρ) } where
                                                                                          helper : ∀ {n} {Γ : Context n} {s t : Term n} {σ τ ν ρ} →
                                                                                            Γ ⊢ s ⦂ σ      → Γ ⊢ t ⦂ τ →
                                                                                            Γ ⊢ s ⦂ ν `→ ρ → Γ ⊢ t ⦂ ν →
                                                                                            ¬ ∃[ ρ′ ] (σ ≡ τ `→ ρ′) →
                                                                                            σ ≡ τ `→ ρ
                                                                                          helper Γ⊢s⦂σ Γ⊢t⦂τ Γ⊢s⦂ν→ρ Γ⊢t⦂ν ∄[ρ]σ≡τ→ρ
                                                                                            with ⊢-injective Γ⊢s⦂σ Γ⊢s⦂ν→ρ | ⊢-injective Γ⊢t⦂τ Γ⊢t⦂ν
                                                                                          ...  | refl | refl = refl
infer {n} Γ (s `⋆ t)    | yes (σ & Γ⊢s⦂σ)         | no ∄[τ]Γ⊢t⦂τ = no λ { (τ & application {.n} {.Γ} {.s} {.t} {ρ} {.τ} Γ⊢s⦂ρ→τ Γ⊢t⦂ρ) → ∄[τ]Γ⊢t⦂τ (ρ & Γ⊢t⦂ρ) }
infer {n} Γ (s `⋆ t)    | no ∄[σ]Γ⊢s⦂σ            | _            = no λ { (τ & application {.n} {.Γ} {.s} {.t} {ρ} {.τ} Γ⊢s⦂ρ→τ Γ⊢t⦂σ) → ∄[σ]Γ⊢s⦂σ (ρ `→ τ & Γ⊢s⦂ρ→τ) }
-- function 
infer {n} Γ (`λ .n `⦂ σ `⇒ t) with infer (n ⦂ σ , Γ) t
infer {n} Γ (`λ .n `⦂ σ `⇒ t)    | yes (τ & n⦂σ,Γ⊢t⦂τ) = yes (σ `→ τ & function n⦂σ,Γ⊢t⦂τ)
infer {n} Γ (`λ .n `⦂ σ `⇒ t)    | no ∄[τ]n⦂σ,Γ⊢t⦂τ    = no λ { (.σ `→ τ & function n⦂σ,Γ⊢t⦂τ) → ∄[τ]n⦂σ,Γ⊢t⦂τ (τ & n⦂σ,Γ⊢t⦂τ) }
-- injection
infer {1+ n}           ø  (`↑ t) = no λ { (τ & ()) }
infer {1+ n} (.n ⦂ σ , Γ) (`↑ t) with infer Γ t
infer {1+ n} (.n ⦂ σ , Γ) (`↑ t)    | yes (τ & Γ⊢t⦂τ) = yes (τ & (injection Γ⊢t⦂τ))
infer {1+ n} (.n ⦂ σ , Γ) (`↑ t)    | no  ∄[τ]Γ⊢t⦂τ  = no (λ { (τ & injection Γ⊢t⦂τ) → ∄[τ]Γ⊢t⦂τ (τ & Γ⊢t⦂τ) })


check : ∀ {n} (Γ : Context n) (t : Term n) (τ : Type) → Dec (Γ ⊢ t ⦂ τ)
check {n} Γ t τ with infer Γ t
check {n} Γ t τ    | yes (τ′ & Γ⊢t⦂τ′) with unify τ τ′
check {n} Γ t τ    | yes (τ′ & Γ⊢t⦂τ′)    | yes (.τ & refl & refl) = yes Γ⊢t⦂τ′
check {n} Γ t τ    | yes (τ′ & Γ⊢t⦂τ′)    | no  ∄[τ″]τ≡τ″×τ′≡τ″ = no λ { Γ⊢t⦂τ → ∄[τ″]τ≡τ″×τ′≡τ″ (τ & refl & ⊢-injective Γ⊢t⦂τ′ Γ⊢t⦂τ) }
check {n} Γ t τ    | no ∄[τ′]Γ⊢t⦂τ′    = no (λ { Γ⊢t⦂τ → ∄[τ′]Γ⊢t⦂τ′ (τ & Γ⊢t⦂τ) })
