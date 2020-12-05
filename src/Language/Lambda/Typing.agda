import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Nat as Nat
  using (ℕ; zero)
  renaming (suc to 1+)
open import Data.Product
  using (∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to _&_)

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.DecidableEquality
open import Language.Lambda.Grammar.Properties


module Language.Lambda.Typing where


-- ================================================================
-- Typing
-- ================================================================

infixr 17 _⦂_,_
infix  10 _⊢_⦂_


-- ----------------------------------------------------------------
-- Typing Context
-- ----------------------------------------------------------------

-- ``Γ : Context n`` is a context of typing information of
-- ``Term n``s.
data Context : ℕ → Set where
  ø     : Context 0
  _⦂_,_ : ∀ n → Type → Context n → Context (1+ n)


_ : Context 2
_ = 1 ⦂ `𝟙 , 0 ⦂ `𝟙 , ø

-- ----------------------------------------------------------------
-- Type Judgment
-- ----------------------------------------------------------------


-- ``Γ ⊢ a ⦂ α`` is the type of derivations that,
-- in context ``Γ``, the term ``a`` has type ``α``.
data _⊢_⦂_ : ∀ {n} → Context n → Term n → Type → Set where

  ø⊢1⦂𝟙 :
    ------------------------------------------------------
    ø ⊢ `1 ⦂ `𝟙

  name : ∀ {n} {Γ : Context n} {α} →
    ------------------------------------------------------
    n ⦂ α , Γ ⊢ ` n ⦂ α

  function : ∀ {n} {Γ : Context n} {t : Term (1+ n)} {β α} →
    n ⦂ β , Γ ⊢ t ⦂ α →
    ---------------------------------------------
    Γ ⊢ `λ n `⦂ β `⇒ t ⦂ β `→ α

  application : ∀ {n} {Γ : Context n} {s t : Term n} {β α} →
    Γ ⊢ s ⦂ β `→ α →
    Γ ⊢ t ⦂ β →
    ---------------------------------------------
    Γ ⊢ s `∙ t ⦂ α

  injection : ∀ {n} {Γ : Context n} {t : Term n} {β α} →
    Γ ⊢ t ⦂ α →
    ------------------------------------------------------
    n ⦂ β , Γ ⊢ `↑ t ⦂ α

  substitution : ∀ {n} {x} {a} {Γ} {ξ α} →
    ø ⊢ x ⦂ ξ →
    ? ⊢ a ⦂ α →
    Γ ⊢ [ x ] a ⦂ α


-- lemmas

⊢-injective : ∀ {n} {Γ : Context n} {t : Term n} {α α′} →
  Γ ⊢ t ⦂ α →
  Γ ⊢ t ⦂ α′ →
  ------------------------------
  α ≡ α′
-- name
⊢-injective {0} {ø} {`1} {.`𝟙} {.`𝟙} ø⊢1⦂𝟙 ø⊢1⦂𝟙 = refl
⊢-injective {.(1+ n)} {.(n ⦂ α , _)} {` n} {α} {α′} name name = refl
-- application
⊢-injective {n} {Γ} {s `∙ t} {α} {α′}
  (application {.n} {.Γ} {.s} {.t} {β } {.α } Γ⊢s⦂β→α   Γ⊢t⦂α)
  (application {.n} {.Γ} {.s} {.t} {β′} {.α′} Γ⊢s⦂β′→α′ Γ⊢t⦂α′)
  with ⊢-injective Γ⊢s⦂β→α Γ⊢s⦂β′→α′ | ⊢-injective Γ⊢t⦂α Γ⊢t⦂α′
... | refl | refl = refl
-- function
⊢-injective {n} {Γ} {`λ .n `⦂ β `⇒ t} {.β `→ α} {.β `→ α′}
  (function {.n} {.Γ} {.t} {.β} {α } n⦂β,Γ⊢t⦂α)
  (function {.n} {.Γ} {.t} {.β} {α′} n⦂β,Γ⊢t⦂α′)
  with ⊢-injective n⦂β,Γ⊢t⦂α n⦂β,Γ⊢t⦂α′
... | refl = refl
-- injection
⊢-injective {1+ n} {.n ⦂ β , Γ} {`↑ t} {α} {α′}
  (injection {.n} {.Γ} {.t} {.β} {.α } Γ⊢t⦂α)
  (injection {.n} {.Γ} {.t} {.β} {.α′} Γ⊢t⦂α′)
  with ⊢-injective Γ⊢t⦂α Γ⊢t⦂α′
... | refl = refl

-- examples

_ : 1 ⦂ `𝟙 `→ `𝟙 , 0 ⦂ `𝟙 , ø ⊢ ` 1 `∙ `↑ ` 0 ⦂ `𝟙
_ = application name (injection name)

_ : ø ⊢ `id ⦂ `𝟙 `→ `𝟙
_ = function name

_ : ø ⊢ `const ⦂ `𝟙 `→ (`𝟙 `→ `𝟙)
_ = function (function name)

_ : ø ⊢ `apply ⦂ (`𝟙 `→ `𝟙) `→ `𝟙 `→ `𝟙
_ = function (function (application (injection name) name))


-- ----------------------------------------------------------------
-- Type Inference and Checking
-- ----------------------------------------------------------------


-- type unification
unify : ∀ (β α : Type) → Dec (∃[ γ ] ((β ≡ γ) × (α ≡ γ)))
unify β α with β Type.≟ α
...          | yes β≡α = yes (α & β≡α & refl)
...          | no  β≢α = no λ { (γ & β≡γ & α≡γ) → ⊥-elim (β≢α (trans β≡γ (sym α≡γ))) }

unify-application : ∀ (β α : Type) → Dec (∃[ γ ] (β ≡ α `→ γ))
unify-application `𝟘 α = no λ ()
unify-application `𝟙 α = no λ ()
unify-application (α `→ γ)  α′ with α Type.≟ α′
unify-application (α `→ γ) .α     | yes refl = yes (γ & refl)
unify-application (α `→ γ)  α′    | no  α≢α′ = no λ { (γ & refl) → α≢α′ refl }


-- type inference
infer : ∀ {n} (Γ : Context n) (t : Term n) → Dec (∃[ α ] (Γ ⊢ t ⦂ α))
-- primitive
infer {0} ø `1 = yes (`𝟙 & ø⊢1⦂𝟙)
-- name
infer {1+ n} (.n ⦂ α , Γ) (` .n) = yes (α & name)
-- application
infer {n} Γ (s `∙ t) with infer Γ s               | infer Γ t
infer {n} Γ (s `∙ t)    | yes (β & Γ⊢s⦂β)         | yes (α & Γ⊢t⦂α) with unify-application β α
infer {n} Γ (s `∙ t)    | yes (.(α `→ γ) & Γ⊢s⦂β) | yes (α & Γ⊢t⦂α)    | yes (γ & refl) = yes (γ & (application Γ⊢s⦂β Γ⊢t⦂α))
infer {n} Γ (s `∙ t)    | yes (β & Γ⊢s⦂β)         | yes (α & Γ⊢t⦂α)    | no ∄[γ]β≡α→γ   = no λ { (γ & application {.n} {.Γ} {.s} {.t} {ν} {.γ} Γ⊢s⦂ν→γ Γ⊢t⦂ν) →
                                                                                                 ∄[γ]β≡α→γ (γ & helper Γ⊢s⦂β Γ⊢t⦂α Γ⊢s⦂ν→γ Γ⊢t⦂ν ∄[γ]β≡α→γ) } where
                                                                                          helper : ∀ {n} {Γ : Context n} {s t : Term n} {β α ν γ} →
                                                                                            Γ ⊢ s ⦂ β      → Γ ⊢ t ⦂ α →
                                                                                            Γ ⊢ s ⦂ ν `→ γ → Γ ⊢ t ⦂ ν →
                                                                                            ¬ ∃[ γ′ ] (β ≡ α `→ γ′) →
                                                                                            β ≡ α `→ γ
                                                                                          helper Γ⊢s⦂β Γ⊢t⦂α Γ⊢s⦂ν→γ Γ⊢t⦂ν ∄[γ]β≡α→γ
                                                                                            with ⊢-injective Γ⊢s⦂β Γ⊢s⦂ν→γ | ⊢-injective Γ⊢t⦂α Γ⊢t⦂ν
                                                                                          ...  | refl | refl = refl
infer {n} Γ (s `∙ t)    | yes (β & Γ⊢s⦂β)         | no ∄[α]Γ⊢t⦂α = no λ { (α & application {.n} {.Γ} {.s} {.t} {γ} {.α} Γ⊢s⦂γ→α Γ⊢t⦂γ) → ∄[α]Γ⊢t⦂α (γ & Γ⊢t⦂γ) }
infer {n} Γ (s `∙ t)    | no ∄[β]Γ⊢s⦂β            | _            = no λ { (α & application {.n} {.Γ} {.s} {.t} {γ} {.α} Γ⊢s⦂γ→α Γ⊢t⦂β) → ∄[β]Γ⊢s⦂β (γ `→ α & Γ⊢s⦂γ→α) }
-- function 
infer {n} Γ (`λ .n `⦂ β `⇒ t) with infer (n ⦂ β , Γ) t
infer {n} Γ (`λ .n `⦂ β `⇒ t)    | yes (α & n⦂β,Γ⊢t⦂α) = yes (β `→ α & function n⦂β,Γ⊢t⦂α)
infer {n} Γ (`λ .n `⦂ β `⇒ t)    | no ∄[α]n⦂β,Γ⊢t⦂α    = no λ { (.β `→ α & function n⦂β,Γ⊢t⦂α) → ∄[α]n⦂β,Γ⊢t⦂α (α & n⦂β,Γ⊢t⦂α) }
-- injection
infer {1+ n} (.n ⦂ β , Γ) (`↑ t) with infer Γ t
infer {1+ n} (.n ⦂ β , Γ) (`↑ t)    | yes (α & Γ⊢t⦂α) = yes (α & (injection Γ⊢t⦂α))
infer {1+ n} (.n ⦂ β , Γ) (`↑ t)    | no  ∄[α]Γ⊢t⦂α  = no (λ { (α & injection Γ⊢t⦂α) → ∄[α]Γ⊢t⦂α (α & Γ⊢t⦂α) })


check : ∀ {n} (Γ : Context n) (t : Term n) (α : Type) → Dec (Γ ⊢ t ⦂ α)
check {n} Γ t α with infer Γ t
check {n} Γ t α    | yes (α′ & Γ⊢t⦂α′) with unify α α′
check {n} Γ t α    | yes (α′ & Γ⊢t⦂α′)    | yes (.α & refl & refl) = yes Γ⊢t⦂α′
check {n} Γ t α    | yes (α′ & Γ⊢t⦂α′)    | no  ∄[α″]α≡α″×α′≡α″ = no λ { Γ⊢t⦂α → ∄[α″]α≡α″×α′≡α″ (α & refl & ⊢-injective Γ⊢t⦂α′ Γ⊢t⦂α) }
check {n} Γ t α    | no ∄[α′]Γ⊢t⦂α′    = no (λ { Γ⊢t⦂α → ∄[α′]Γ⊢t⦂α′ (α & Γ⊢t⦂α) })
