import Level
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary using (Rel)
open import Relation.Nullary.Decidable
open import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Product renaming (_,_ to _&_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)


module Language.Lambda2.Kinding where


infix 3 _∋→⊨_ _≅ₜ_ _≅ₛ_ _≅ₑ_ _⊢⇓_ _⊢↓_ _⊨_ _∋→⊢⇓_ _⊢≅⊨_ _⊢≅⊨ₑ_
infix 4 _∋_ _⊢_ _∙_
infix 5 _∋→∋_ _∋→⊢_
infixl 6 _,_

infixl 8 _`∙_
infixr 9 `λ_ `μ_ `Π_
infixr 10 _`→_
infixr 11 ↓_ `_ `$_ S_
infix  12 _[_] _[_]⇓




-- ===================================================================
-- Kinds
-- ===================================================================


data Kind : Set where

  -- unit
  `⋆ : Kind

  -- arrow
  _`→_ : Kind → Kind → Kind



-- ===================================================================
-- Kinding Context
-- ===================================================================


-- Kinding Context
data Context : Set where
  ø : Context
  _,_ : Context → Kind → Context


-- Type Name in Kinding Context
-- ``Φ ∋ A`` encodes that a Type Name of Kind ``A`` is in Context ``Φ``
data _∋_ : Context → Kind → Set where

  head : ∀ {Φ A} →
    ------------------------------------------------
    Φ , A ∋ A

  tail : ∀ {Φ A B} →
    Φ ∋ B →
    ------------------------------------------------
    Φ , A ∋ B


-- abbreviations

Z : ∀ {Φ A} → Φ , A ∋ A
Z = head

S_ : ∀ {Φ A B} → Φ ∋ B → Φ , A ∋ B
S_ = tail


-- ===================================================================
-- Types
-- ===================================================================


-- Type
-- ``Φ ⊢ K`` encodes a Type of Kind ``K`` in Context ``Φ``
data _⊢_ Φ : Kind → Set where

  -- unit
  `⊤ :
    ------------------------------------------------
    Φ ⊢ `⋆

  -- name
  `_ : ∀ {K} →
    Φ ∋ K →
    ------------------------------------------------
    Φ ⊢ K

  -- arrow
  _`→_ :
    Φ ⊢ `⋆ →
    Φ ⊢ `⋆ →
    ------------------------------------------------
    Φ ⊢ `⋆

  -- product
  `Π_ : ∀ {K} →
    Φ , K ⊢ `⋆ →
    ------------------------------------------------
    Φ     ⊢ `⋆

  -- function
  `λ_ : ∀ {J K} →
    Φ , J ⊢ K →
    ------------------------------------------------
    Φ     ⊢ J `→ K

  -- application
  _`∙_ : ∀ {J K} →
    Φ ⊢ J `→ K →
    Φ ⊢ J →
    ------------------------------------------------
    Φ ⊢ K

  -- fixpoint
  `μ_ :
    Φ , `⋆ ⊢ `⋆ →
    ------------------------------------------------
    Φ      ⊢ `⋆


length : Context → ℕ
length ø = 0
length (Φ , _) = 1 + length Φ


lookup : ∀ (Φ : Context) (i : ℕ) → i < length Φ → Kind
lookup (Φ , ξ)  zero    _       = ξ
lookup (Φ , _) (suc i) (s≤s i<) = lookup Φ i i<


count : ∀ {Φ} i (i< : i < length Φ) → Φ ∋ lookup Φ i i<
count {_ , _}  zero    _       = head
count {_ , _} (suc i) (s≤s i<) = tail (count i i<)


-- abbreviation for DeBruijn indexed names
`$_ : ∀ {Φ}
  (n : ℕ) → {ξ : True (suc n ≤? length Φ)} →
  Φ ⊢ lookup Φ n (toWitness ξ)
`$_ x {ξ} = ` (count x (toWitness ξ))


-- examples
private

  _ : ∀ {Φ A} → Φ , A ⊢ A
  _ = `$ 0

  _ : ∀ {Φ A B} → Φ , A , B ⊢ A
  _ = `$ 1



-- -------------------------------------------------------------------
-- substitution
-- -------------------------------------------------------------------


-- Renaming (Type Names to Type Names)
_∋→∋_ : Context → Context → Set
Φ ∋→∋ Ψ = ∀ {K} →
  Φ ∋ K →
  Ψ ∋ K


-- weaken a Renaming to a larger Context
weaken-∋→∋ : ∀ {Φ Ψ} →
  Φ ∋→∋ Ψ →
  ∀ {K} → Φ , K ∋→∋ Ψ , K
weaken-∋→∋ ℜ  head       = head
weaken-∋→∋ ℜ (tail x) = tail (ℜ x)


-- apply Renaming
rename : ∀ {Φ Ψ} →
  Φ ∋→∋ Ψ →
  ∀ {K} →
    Φ ⊢ K →
    Ψ ⊢ K

rename ℜ  `⊤      = `⊤
rename ℜ (` ξ)    = ` (ℜ ξ)
rename ℜ (`λ β)   = `λ (rename (weaken-∋→∋ ℜ) β)
rename ℜ (β `∙ α) = rename ℜ β `∙ rename ℜ α
rename ℜ (α `→ β) = rename ℜ α `→ rename ℜ β
rename ℜ (`Π β)   = `Π rename (weaken-∋→∋ ℜ) β
rename ℜ (`μ β)   = `μ rename (weaken-∋→∋ ℜ) β


-- weaken a Type to a larger context
weaken-⊢ : ∀ {Φ J K} →
  Φ     ⊢ K →
  Φ , J ⊢ K

weaken-⊢ = rename tail


-- Substitution (Type Names to Types)
_∋→⊢_ : Context → Context → Set
Φ ∋→⊢ Ψ = ∀ {K} →
  Φ ∋ K →
  Ψ ⊢ K


-- weaken a Substitution to a larger context
weaken-∋→⊢ : ∀ {Φ Ψ} →
          Φ     ∋→⊢ Ψ →
  ∀ {K} → Φ , K ∋→⊢ Ψ , K
weaken-∋→⊢ 𝔖  head    = ` head
weaken-∋→⊢ 𝔖 (tail x) = rename tail (𝔖 x)


-- apply Substitution
substitute : ∀ {Φ Ψ} →
  Φ ∋→⊢ Ψ →
  ∀ {K} → Φ ⊢ K →
          Ψ ⊢ K
substitute 𝔖  `⊤      = `⊤
substitute 𝔖 (` x)    = 𝔖 x
substitute 𝔖 (`λ β)   = `λ substitute (weaken-∋→⊢ 𝔖) β
substitute 𝔖 (β `∙ α) = substitute 𝔖 β `∙ substitute 𝔖 α
substitute 𝔖 (α `→ β) = substitute 𝔖 α `→ substitute 𝔖 β
substitute 𝔖 (`Π β)   = `Π substitute (weaken-∋→⊢ 𝔖) β
substitute 𝔖 (`μ β)   = `μ substitute (weaken-∋→⊢ 𝔖) β


-- extend Substitution
extend-∋→⊢ : ∀ {Φ Ψ} →
                      Φ     ∋→⊢ Ψ →
  ∀ {K} (α : Ψ ⊢ K) → Φ , K ∋→⊢ Ψ

extend-∋→⊢ 𝔖 α  head    = α
extend-∋→⊢ 𝔖 _ (tail x) = 𝔖 x


-- apply single Substitution
_[_] : ∀ {Φ J K} →
  Φ , J ⊢ K → -- β
  Φ     ⊢ J → -- α
  ------------------------------------------------
  Φ     ⊢ K   -- β [ α ]

β [ α ] = substitute (extend-∋→⊢ `_ α) β



-- -------------------------------------------------------------------
-- properties
-- -------------------------------------------------------------------


weaken-∋→∋-identity : ∀ {Φ J K} (α : Φ , J ∋ K) →
  weaken-∋→∋ id α ≡ α

weaken-∋→∋-identity  head    = ≡.refl
weaken-∋→∋-identity (tail x) = ≡.refl


weaken-∋→∋-compose : ∀ {Φ Ψ Θ} {ℜ₁ : Φ ∋→∋ Ψ} {ℜ₂ : Ψ ∋→∋ Θ} {A B} (α : Φ , A ∋ B) →
  weaken-∋→∋ (ℜ₂ ∘ ℜ₁) α ≡ weaken-∋→∋ ℜ₂ (weaken-∋→∋ ℜ₁ α)

weaken-∋→∋-compose  head    = ≡.refl
weaken-∋→∋-compose (tail x) = ≡.refl


postulate
  rename-identity : ∀ {Φ A} (α : Φ ⊢ A) →
    rename id α ≡ α


postulate
  rename-compose : ∀ {Φ Ψ Θ} {ℜ₁ : Φ ∋→∋ Ψ} {ℜ₂ : Ψ ∋→∋ Θ} {A} (α : Φ ⊢ A) →
    rename (ℜ₂ ∘ ℜ₁) α ≡ rename ℜ₂ (rename ℜ₁ α)



postulate
  weaken-∋→⊢-identity : ∀ {Φ X Y} (ξ : Φ , Y ∋ X) →
    weaken-∋→⊢ `_ ξ ≡ ` ξ


postulate
  weaken-∋→⊢-compose : ∀ {Φ Ψ Θ} {𝔖₁ : Φ ∋→⊢ Ψ} {𝔖₂ : Ψ ∋→⊢ Θ} {X Y} (ξ : Φ , Y ∋ X) →
    weaken-∋→⊢ (substitute 𝔖₂ ∘ 𝔖₁) ξ ≡ substitute (weaken-∋→⊢ 𝔖₂) (weaken-∋→⊢ 𝔖₁ ξ)


postulate
  weaken-∋→⊢-cong : ∀ {Φ Ψ} {𝔖 𝔖′ : Φ ∋→⊢ Ψ} →
    (∀ {A}  (α : Φ ∋ A) → 𝔖 α ≡ 𝔖′ α) →
    ∀ {A B} (α : Φ , A ∋ B) →
    weaken-∋→⊢ 𝔖 α ≡ weaken-∋→⊢ 𝔖′ α


postulate
  weaken-∋→⊢-weaken-∋→∋ : ∀ {Φ Ψ Θ} {ℜ : Φ ∋→∋ Ψ} {𝔖 : Ψ ∋→⊢ Θ} {A B} (α : Φ , A ∋ B) →
    weaken-∋→⊢ (𝔖 ∘ ℜ) α ≡ weaken-∋→⊢ 𝔖 (weaken-∋→∋ ℜ α)


postulate
  substitute-rename : ∀ {Φ Ψ Θ} {ℜ : Φ ∋→∋ Ψ} {𝔖 : Ψ ∋→⊢ Θ} {A} (α : Φ ⊢ A) →
    substitute (𝔖 ∘ ℜ) α ≡ substitute 𝔖 (rename ℜ α)


postulate
  rename-weaken-∋→∋-weaken-∋→⊢ : ∀ {Φ Ψ Θ} {𝔖 : Φ ∋→⊢ Ψ} {ℜ : Ψ ∋→∋ Θ} {A B} (α : Φ , A ∋ B) →
    weaken-∋→⊢ (rename ℜ ∘ 𝔖) α ≡ rename (weaken-∋→∋ ℜ) (weaken-∋→⊢ 𝔖 α)


postulate
  rename-substitute : ∀ {Φ Ψ Θ} {𝔖 : Φ ∋→⊢ Ψ} {ℜ : Ψ ∋→∋ Θ} {A} (α : Φ ⊢ A) →
    substitute (rename ℜ ∘ 𝔖) α ≡ rename ℜ (substitute 𝔖 α)


postulate
  substitute-identity : ∀ {Φ A} (α : Φ ⊢ A) →
    substitute `_ α ≡ α


postulate
  substitute-name : ∀ {Φ Ψ} {𝔖 : Φ ∋→⊢ Ψ} {X} (ξ : Φ ∋ X) →
    substitute 𝔖 (` ξ) ≡ 𝔖 ξ


postulate
  substitute-compose : ∀ {Φ Ψ Θ} {𝔖₁ : Φ ∋→⊢ Ψ} {𝔖₂ : Ψ ∋→⊢ Θ} {A} (α : Φ ⊢ A) →
    substitute (substitute 𝔖₂ ∘ 𝔖₁) α ≡ substitute 𝔖₂ (substitute 𝔖₁ α)


postulate
  substitute-cong : ∀ {Φ Ψ} {𝔖 𝔖′ : Φ ∋→⊢ Ψ} →
    (∀ {A} (α : Φ ∋ A) → 𝔖 α ≡ 𝔖′ α) →
    ∀ {A} (α : Φ ⊢ A) →
    substitute 𝔖 α ≡ substitute 𝔖′ α


-- Lemma. push renaming into extended substitution
postulate
  rename-extend-∋→⊢ : ∀ {Φ Ψ} {A B} (ℜ : Φ ∋→∋ Ψ) (α : Φ ⊢ A) (β : Φ , A ∋ B) →
    extend-∋→⊢ `_ (rename ℜ α) (weaken-∋→∋ ℜ β) ≡ rename ℜ (extend-∋→⊢ `_ α β)


-- Lemma. push substitution into extended substitution
postulate
  substitute-extend-∋→⊢ : ∀ {Φ Ψ} {A B} (𝔖 : Φ ∋→⊢ Ψ) (α : Φ ⊢ A) (β : Φ , A ∋ B) →
    substitute (extend-∋→⊢ `_ (substitute 𝔖 α)) (weaken-∋→⊢ 𝔖 β) ≡ substitute 𝔖 (extend-∋→⊢ `_ α β)



-- -------------------------------------------------------------------
-- Type Equality
-- -------------------------------------------------------------------


-- Relation. Type equality
data _≅ₜ_ {Φ} : ∀ {A} → Rel (Φ ⊢ A) Level.zero where

  refl : ∀ {A} {α : Φ ⊢ A} →
    ------------------------------------------------
    α ≅ₜ α

  sym : ∀ {A} {α α′ : Φ ⊢ A} →
    α ≅ₜ α′ →
    ------------------------------------------------
    α′ ≅ₜ α

  trans : ∀ {A} {α α′ α″ : Φ ⊢ A} →
    α  ≅ₜ α′ →
    α′ ≅ₜ α″ →
    ------------------------------------------------
    α  ≅ₜ α″

  -- congruence rules

  subst : ∀ {A B} (β : Φ , A ⊢ B) (α : Φ ⊢ A) →
    ------------------------------------------------
    (`λ β) `∙ α ≅ₜ β [ α ]

  _`→_ : ∀ {α α′ β β′ : Φ ⊢ `⋆} →
    α ≅ₜ α′ →
    β ≅ₜ β′ →
    ------------------------------------------------
    α `→ β ≅ₜ α′ `→ β′

  `Π_ : ∀ {K} {β β′ : Φ , K ⊢ `⋆} →
    β ≅ₜ β′ →
    ------------------------------------------------
    `Π β ≅ₜ `Π β′

  `μ_ : ∀ {β β′ : Φ , `⋆ ⊢ `⋆} →
    β ≅ₜ β′ →
    ------------------------------------------------
    `μ β ≅ₜ `μ β

  `λ_ : ∀ {β β′ : Φ , `⋆ ⊢ `⋆} →
    β ≅ₜ β′ →
    ------------------------------------------------
    `λ β ≅ₜ `λ β

  _`∙_ : ∀ {J K} {β β′ : Φ ⊢ J `→ K} {α α′ : Φ ⊢ J} →
    β ≅ₜ β′ →
    α ≅ₜ α′ →
    ------------------------------------------------
    β `∙ α ≅ₜ β′ `∙ α′


-- Lemma. renaming preserves type equality
rename-≅ₜ : ∀ {Φ Ψ} {K} {α α′ : Φ ⊢ K} (ℜ : Φ ∋→∋ Ψ) →
  α ≅ₜ α′ →
  rename ℜ α ≅ₜ rename ℜ α′

rename-≅ₜ ℜ (subst β α)        = ≡.subst (rename ℜ ((`λ β) `∙ α) ≅ₜ_)
                                          (≡.trans (≡.sym (substitute-rename β))
                                                   (≡.trans (substitute-cong (rename-extend-∋→⊢ ℜ α) β)
                                                            (rename-substitute β)))
                                          (subst _ _)
rename-≅ₜ ℜ  refl              = refl
rename-≅ₜ ℜ (sym a≅a′)         = sym (rename-≅ₜ ℜ a≅a′)
rename-≅ₜ ℜ (trans a≅a′ a′≅a″) = trans (rename-≅ₜ ℜ a≅a′) (rename-≅ₜ ℜ a′≅a″)
rename-≅ₜ ℜ (β≅β′ `→ α≅α′)     = rename-≅ₜ ℜ β≅β′ `→ rename-≅ₜ ℜ α≅α′
rename-≅ₜ ℜ (`Π β≅β′)          = `Π rename-≅ₜ (weaken-∋→∋ ℜ) β≅β′
rename-≅ₜ ℜ (`μ β≅β′)          = `μ rename-≅ₜ (weaken-∋→∋ ℜ) β≅β′
rename-≅ₜ ℜ (`λ β≅β′)          = `λ rename-≅ₜ (weaken-∋→∋ ℜ) β≅β′
rename-≅ₜ ℜ (β≅β′ `∙ α≅α′)     = rename-≅ₜ ℜ β≅β′ `∙ rename-≅ₜ ℜ α≅α′


-- Lemma. substitution preserves type equality
substitute-≅ₜ : ∀ {Φ Ψ} {K} {α α′ : Φ ⊢ K} (𝔖 : Φ ∋→⊢ Ψ) →
  α ≅ₜ α′ →
  substitute 𝔖 α ≅ₜ substitute 𝔖 α′

substitute-≅ₜ 𝔖 (subst β α)        = ≡.subst (substitute 𝔖 ((`λ β) `∙ α) ≅ₜ_)
                                              (≡.trans (≡.trans (≡.sym (substitute-compose β))
                                                                (substitute-cong (substitute-extend-∋→⊢ 𝔖 α) β))
                                                       (substitute-compose β))
                                              (subst _ _)
substitute-≅ₜ 𝔖  refl              = refl
substitute-≅ₜ 𝔖 (sym α≅α′)         = sym (substitute-≅ₜ 𝔖 α≅α′)
substitute-≅ₜ 𝔖 (trans α≅α′ α′≅α″) = trans (substitute-≅ₜ 𝔖 α≅α′) (substitute-≅ₜ 𝔖 α′≅α″)
substitute-≅ₜ 𝔖 (α≅α′ `→ β≅β′)     = substitute-≅ₜ 𝔖 α≅α′ `→ substitute-≅ₜ 𝔖 β≅β′
substitute-≅ₜ 𝔖 (`Π β≅β′)          = `Π substitute-≅ₜ (weaken-∋→⊢ 𝔖) β≅β′
substitute-≅ₜ 𝔖 (`μ β≅β′)          = `μ substitute-≅ₜ (weaken-∋→⊢ 𝔖) β≅β′
substitute-≅ₜ 𝔖 (`λ β≅β′)          = `λ substitute-≅ₜ (weaken-∋→⊢ 𝔖) β≅β′
substitute-≅ₜ 𝔖 (β≅β′ `∙ α≅α′)     = substitute-≅ₜ 𝔖 β≅β′ `∙ substitute-≅ₜ 𝔖 α≅α′



-- ===================================================================
-- Type Normalization
-- ===================================================================
-- A type in normal form should not reduce.


data _⊢⇓_ Φ : Kind → Set  -- Normal Type
data _⊢↓_ Φ : Kind → Set  -- Neutral Type


-- Normal Type
data _⊢⇓_ Φ where

  -- function
  `λ_ : ∀ {A B} →
    Φ , A ⊢⇓ B →
    ------------------------------------------------
    Φ     ⊢⇓ A `→ B

  -- arrow
  _`→_ :
    Φ ⊢⇓ `⋆ →
    Φ ⊢⇓ `⋆ →
    ------------------------------------------------
    Φ ⊢⇓ `⋆

  -- product
  `Π_ : ∀ {A} →
    Φ , A ⊢⇓ `⋆ →
    ------------------------------------------------
    Φ     ⊢⇓ `⋆

  -- fixpoint
  `μ_ :
    Φ , `⋆ ⊢⇓ `⋆ →
    ------------------------------------------------
    Φ      ⊢⇓ `⋆

  -- neutral ⇒ normal
  ↓_ : ∀ {A} →
    Φ ⊢↓ A →
    ------------------------------------------------
    Φ ⊢⇓ A


-- Neutral Type
data _⊢↓_ Φ where

  -- unit
  `⊤ :
    ------------------------------------------------
    Φ ⊢↓ `⋆

  -- name
  `_ : ∀ {A} →
    Φ ∋ A →
    ------------------------------------------------
    Φ ⊢↓ A

  -- application
  _`∙_ : ∀ {A B} →
    Φ ⊢↓ A `→ B →
    Φ ⊢⇓ A →
    ------------------------------------------------
    Φ ⊢↓ B



-- Lemma. renaming preserves normal forms
rename-⊢⇓ : ∀ {Φ Ψ} →
  Φ ∋→∋ Ψ →
  ∀ {A} → Φ ⊢⇓ A →
          Ψ ⊢⇓ A

rename-⊢↓ : ∀ {Φ Ψ} →
  Φ ∋→∋ Ψ →
  ∀ {A} →
    Φ ⊢↓ A →
    Ψ ⊢↓ A

-- normal
rename-⊢⇓ ℜ (`λ B⇓)    = `λ rename-⊢⇓ (weaken-∋→∋ ℜ) B⇓
rename-⊢⇓ ℜ (A⇓ `→ B⇓) = rename-⊢⇓ ℜ A⇓ `→ rename-⊢⇓ ℜ B⇓
rename-⊢⇓ ℜ (`Π B⇓)    = `Π rename-⊢⇓ (weaken-∋→∋ ℜ) B⇓
rename-⊢⇓ ℜ (`μ B⇓)    = `μ rename-⊢⇓ (weaken-∋→∋ ℜ) B⇓
rename-⊢⇓ ℜ (↓ A↓ )    = ↓ rename-⊢↓ ℜ A↓
-- neutral
rename-⊢↓ ℜ `⊤         = `⊤
rename-⊢↓ ℜ (` X)      = ` ℜ X
rename-⊢↓ ℜ (B↓ `∙ A↓) = rename-⊢↓ ℜ B↓ `∙ rename-⊢⇓ ℜ A↓


-- Lemma. weakening preserves normal form
weaken-⊢⇓ : ∀ {Φ A B} →
  Φ     ⊢⇓ B →
  Φ , A ⊢⇓ B
weaken-⊢⇓ = rename-⊢⇓ tail


-- Lemma. congruence over renaming
postulate
  rename-⊢⇓-cong : ∀ {Φ Ψ} →
    {ℜ ℜ′ : Φ ∋→∋ Ψ} →
    (∀ {A} (α : Φ ∋ A) → ℜ α ≡ ℜ′ α) →
    ∀ {A} (α : Φ ⊢⇓ A) →
    rename-⊢⇓ ℜ α ≡ rename-⊢⇓ ℜ′ α


-- Lemma. renaming normal forms is functorial
rename-⊢⇓-identity : ∀ {Φ A} → (α : Φ ⊢⇓ A) →
  rename-⊢⇓ id α ≡ α
rename-⊢↓-identity : ∀ {Φ A} → (α : Φ ⊢↓ A) →
  rename-⊢↓ id α ≡ α

-- normal
rename-⊢⇓-identity (`λ B⇓)    = ≡.cong  `λ_     (≡.trans (rename-⊢⇓-cong weaken-∋→∋-identity B⇓) (rename-⊢⇓-identity B⇓))
rename-⊢⇓-identity (A⇓ `→ B⇓) = ≡.cong₂ _`→_   (rename-⊢⇓-identity A⇓) (rename-⊢⇓-identity B⇓)
rename-⊢⇓-identity (`Π B⇓)    = ≡.cong  `Π_     (≡.trans (rename-⊢⇓-cong weaken-∋→∋-identity B⇓) (rename-⊢⇓-identity B⇓))
rename-⊢⇓-identity (`μ B⇓)    = ≡.cong  `μ_     (≡.trans (rename-⊢⇓-cong weaken-∋→∋-identity B⇓) (rename-⊢⇓-identity B⇓))
rename-⊢⇓-identity (↓ A↓ )    = ≡.cong ↓_ (rename-⊢↓-identity A↓)
-- neutral
rename-⊢↓-identity  `⊤        = ≡.refl
rename-⊢↓-identity (` X)      = ≡.refl
rename-⊢↓-identity (B↓ `∙ A⇓) = ≡.cong₂ _`∙_ (rename-⊢↓-identity B↓) (rename-⊢⇓-identity A⇓)


postulate
  rename-⊢⇓-compose : ∀ {Φ Ψ Θ} {ℜ : Φ ∋→∋ Ψ} {ℜ′ : Ψ ∋→∋ Θ} {A} (α : Φ ⊢⇓ A) →
    rename-⊢⇓ (ℜ′ ∘ ℜ) α ≡ rename-⊢⇓ ℜ′ (rename-⊢⇓ ℜ α)


postulate
  rename-⊢↓-compose : ∀ {Φ Ψ Θ} {ℜ : Φ ∋→∋ Ψ} {ℜ′ : Ψ ∋→∋ Θ} {A} (α : Φ ⊢↓ A) →
    rename-⊢↓ (ℜ′ ∘ ℜ) α ≡ rename-⊢↓ ℜ′ (rename-⊢↓ ℜ α)

-- semantic kinding
_⊨_ : Context → Kind → Set
Φ ⊨  `⋆      = (Φ ⊢⇓ `⋆)
Φ ⊨ (A `→ B) = (Φ ⊢↓ A `→ B) ⊎ (∀ {Ψ} → Φ ∋→∋ Ψ → Ψ ⊨ A → Ψ ⊨ B)


-- embeds a neutral type into a semantic type
reflect : ∀ {Φ A} →
  Φ ⊢↓ A →
  ------------------------------------------------
  Φ ⊨ A

reflect {A = `⋆}     α↓ = ↓ α↓
reflect {A = _ `→ _} α↓ = inj₁ α↓


-- convert semantic type to syntactic type
reify : ∀ {Φ A} →
  Φ ⊨ A →
  ------------------------------------------------
  Φ ⊢⇓ A

reify {A = `⋆}      α        = α
reify {A = _ `→ _} (inj₁ α) = ↓ α
reify {A = _ `→ _} (inj₂ αF)  = `λ reify (αF tail (reflect (` head)))


rename-⊨ : ∀ {Φ Ψ A} →
  Φ ∋→∋ Ψ →
  Φ ⊨ A →
  ------------------------------------------------
  Ψ ⊨ A

rename-⊨ {_} {_} {`⋆}     ℜ α         = rename-⊢⇓ ℜ α
rename-⊨ {_} {_} {_ `→ _} ℜ (inj₁ α↓) = inj₁ (rename-⊢↓ ℜ α↓)
rename-⊨ {_} {_} {_ `→ _} ℜ (inj₂ αF) = inj₂ λ ℜ′ → αF (ℜ′ ∘ ℜ)


weaken-⊨ : ∀ {Φ A B} →
  Φ     ⊨ B →
  ------------------------------------------------
  Φ , A ⊨ B

weaken-⊨ = rename-⊨ tail


-- an environment maps names to semantic types
_∋→⊨_ : Rel Context Level.zero
Φ ∋→⊨ Ψ = ∀ {A} → Φ ∋ A → Ψ ⊨ A


-- extend environment with larger source context
extendₑ : ∀ {Φ Ψ} →
                      Φ     ∋→⊨ Ψ →
  ∀ {Z} (ζ : Ψ ⊨ Z) → Φ , Z ∋→⊨ Ψ

extendₑ 𝔈 ζ  head    = ζ
extendₑ 𝔈 ζ (tail ξ) = 𝔈 ξ


weakenₑ : ∀ {Φ Ψ} →
  Φ ∋→⊨ Ψ →
  ∀ {A} → Φ , A ∋→⊨ Ψ , A
weakenₑ 𝔈 = extendₑ (weaken-⊨ ∘ 𝔈) (reflect (` head))


-- semantic application
_∙_ : ∀ {Φ A B} →
  Φ ⊨ (A `→ B) →
  Φ ⊨ A →
  Φ ⊨ B
inj₁ α ∙ A = reflect (α `∙ reify A)
inj₂ φ ∙ A = φ id A


evaluate : ∀ {Φ Ψ A} →
  Φ ⊢ A →
  Φ ∋→⊨ Ψ →
  ------------------------------------------------
  Ψ ⊨ A
evaluate  `⊤      𝔈 = ↓ `⊤
evaluate (` ξ)    𝔈 = 𝔈 ξ
evaluate (α `→ β) 𝔈 = reify (evaluate α 𝔈) `→ reify (evaluate β 𝔈)
evaluate (`Π β)   𝔈 = `Π reify (evaluate β (weakenₑ 𝔈))
evaluate (`λ β)   𝔈 = inj₂ λ ℜ ζ → evaluate β (extendₑ (rename-⊨ ℜ ∘ 𝔈) ζ)
evaluate (`μ β)   𝔈 = `μ reify (evaluate β (weakenₑ 𝔈))
evaluate (α `∙ β) 𝔈 = evaluate α 𝔈 ∙ evaluate β 𝔈


εₑ : ∀ {Φ} → Φ ∋→⊨ Φ
εₑ {Φ} = reflect ∘ `_


-- nf
normalize : ∀ {Φ A} →
  Φ ⊢ A →
  ------------------------------------------------
  Φ ⊢⇓ A
normalize α = reify (evaluate α εₑ)



-- ===================================================================
-- Completeness of Type Normalization
-- ===================================================================
-- Normalization is injective up to type equality



-- -------------------------------------------------------------------
-- Semantic Equality
-- -------------------------------------------------------------------

-- Relation. symantic equality
_≅ₛ_ : ∀ {Φ} {A} → Φ ⊨ A → Φ ⊨ A → Set
_≅ₛ_ {Φ} {`⋆} α α′ = α ≡ α′
_≅ₛ_ {Φ} {A `→ B} (inj₁ α) (inj₁ α′) = α ≡ α′
_≅ₛ_ {Φ} {A `→ B} (inj₁ α) (inj₂ φ′) = ⊥
_≅ₛ_ {Φ} {A `→ B} (inj₂ φ) (inj₁ α′) = ⊥
_≅ₛ_ {Φ} {A `→ B} (inj₂ φ) (inj₂ φ′) = (Uniform φ) × (Uniform φ′) × (∀ {Ψ} (ℜ : _ ∋→∋ Ψ) (α α′ : Ψ ⊨ A) → α ≅ₛ α′ → φ ℜ α ≅ₛ φ′ ℜ α′)
  where
    Uniform : ∀ {Φ A B} → (∀ {Ψ} → Φ ∋→∋ Ψ → Ψ ⊨ A → Ψ ⊨ B) → Set
    Uniform {Φ} {A} {B} φ = ∀ {Ψ Ψ′}
      (ℜ : Φ ∋→∋ Ψ) (ℜ′ : Ψ ∋→∋ Ψ′)
      (α α′ : Ψ ⊨ A) →
      α ≅ₛ α′ →
      rename-⊨ ℜ′ (φ ℜ α) ≅ₛ φ (ℜ′ ∘ ℜ) (rename-⊨ ℜ′ α′)


-- Lemma. reflexivity of semantic equality (only on semantic types that are semantically equal to another semantic type)
postulate
  refl-≅ₛ : ∀ {Φ A} {α α′ : Φ ⊨ A} →
    α ≅ₛ α′ →
    α ≅ₛ α


-- Lemma. symmetry of semantic equality
postulate
  sym-≅ₛ : ∀ {Φ A} {α α′ : Φ ⊨ A} →
    α  ≅ₛ α′ →
    α′ ≅ₛ α


-- Lemma. transitivity of semantic equality
postulate
  trans-≅ₛ : ∀ {Φ A} {α α′ α″ : Φ ⊨ A} →
    α  ≅ₛ α′ →
    α′ ≅ₛ α″ →
    α  ≅ₛ α″


-- Lemma. semantically renaming by ``id`` preserves semantic equality
postulate
  rename-⊨-identity : ∀ {Φ A} {α α′ : Φ ⊨ A} →
    α             ≅ₛ α′ →
    rename-⊨ id α ≅ₛ α′


-- Lemma. sequencing of composed semantic renamings
postulate
  rename-⊨-comp : ∀ {Φ Ψ Θ A} (ℜ : Φ ∋→∋ Ψ) (ℜ′ : Ψ ∋→∋ Θ) {α α′ : Φ ⊨ A} →
    α ≅ₛ α′ →
    rename-⊨ (ℜ′ ∘ ℜ) α ≅ₛ rename-⊨ ℜ′ (rename-⊨ ℜ α)


-- Lemma. reflecting preserves semantic renaming
postulate
  reflect-≅ₛ : ∀ {Φ A} {α α′ : Φ ⊢↓ A} →
    α ≡ α′ →
    (reflect α) ≅ₛ reflect α′


-- Lemma. reifying preserves semantic renaming
postulate
  reify-≅ₛ : ∀ {Φ A} {α α′ : Φ ⊨ A} →
    α ≅ₛ α′ →
    reify α ≡ reify α′



-- -------------------------------------------------------------------
-- Environmental Equality
-- -------------------------------------------------------------------


-- Relation. environmental equality
_≅ₑ_ : ∀ {Φ Ψ} → (𝔈 𝔈′ : Φ ∋→⊨ Ψ) → Set
𝔈 ≅ₑ 𝔈′ = ∀ {A} (α : _ ∋ A) → 𝔈 α ≅ₛ 𝔈′ α


-- Lemma. evaluation preserves environmental equality as semantic equality
postulate
  extend-evaluate-id-≅ₛ : ∀ {Φ Ψ A} {𝔈 𝔈′ : Φ ∋→⊨ Ψ} →
    𝔈 ≅ₑ 𝔈′ →
    ∀ (α : Φ ⊢ A) →
      evaluate α 𝔈 ≅ₛ evaluate α 𝔈′


-- Lemma. commuting semantic renaming and evaluation
postulate
  rename-⊨-evaluate-≅ₛ : ∀ {Φ Ψ Θ A} (α : Φ ⊢ A) {𝔈 𝔈′ : Φ ∋→⊨ Ψ} →
    𝔈 ≅ₑ 𝔈′ →
    ∀ (ℜ : Ψ ∋→∋ Θ) →
      rename-⊨ ℜ (evaluate α 𝔈) ≅ₛ evaluate α (rename-⊨ ℜ ∘ 𝔈′)


-- Lemma. commuting renaming and evalution
postulate
  rename-evaluate-≅ₛ : ∀ {Φ Ψ Θ A} (α : Φ ⊢ A) {𝔈 𝔈′ : Ψ ∋→⊨ Θ} →
    𝔈 ≅ₑ 𝔈′ →
    ∀ (ℜ : Φ ∋→∋ Ψ) →
      evaluate (rename ℜ α) 𝔈 ≅ₛ evaluate α (𝔈′ ∘ ℜ)


-- Lemma. formulate substitution in terms of evaluation
postulate
  substitute-evaluate-≅ₛ : ∀ {Φ Ψ Θ A} (α : Φ ⊢ A) {𝔈 𝔈′ : Ψ ∋→⊨ Θ} →
    𝔈 ≅ₑ 𝔈′ →
    ∀ (𝔖 : Φ ∋→⊢ Ψ) →
      evaluate (substitute 𝔖 α) 𝔈 ≅ₛ evaluate α (λ ξ → evaluate (𝔖 ξ) 𝔈)


-- Lemma. evaluation preserves type equality as semantic equality
postulate
  evaluate-≅ₛ : ∀ {Φ Ψ A} {𝔈 𝔈′ : Φ ∋→⊨ Ψ} {α α′ : Φ ⊢ A} →
    𝔈 ≅ₑ 𝔈′ →
    α ≅ₜ α′ →
    evaluate α 𝔈 ≅ₛ evaluate α′ 𝔈′


-- Lemma. commuting semantic renameing and reflection
postulate
  rename-⊨-reflect : ∀ {Φ Ψ A} (ℜ : Φ ∋→∋ Ψ) α →
    _≅ₛ_ {A = A} (rename-⊨ ℜ (reflect α)) (reflect (rename-⊢↓ ℜ α))


-- Lemma. commuting normal renaming and reifying
postulate
  rename-reify : ∀ {Φ Ψ A} (ℜ : Φ ∋→∋ Ψ) {α α′} →
    _≅ₛ_ {A = A} α α′ →
    rename-⊢⇓ ℜ (reify α) ≡ reify (rename-⊨ ℜ α′)


-- Lemma. distribution of renaming over semantic application
postulate
  rename-⊨-∙ : ∀ {Φ Ψ A B} (ℜ : Φ ∋→∋ Ψ) {β β′} {α α′} →
    _≅ₛ_ {A = A `→ B} β β′ →
    _≅ₛ_ {A = A} α α′ →
    _≅ₛ_ {A = B} (rename-⊨ ℜ (β ∙ α)) (rename-⊨ ℜ β′ ∙ rename-⊨ ℜ α′)


-- Lemma. the identity environment is environmentally equal to itself
id-≅ₑ : ∀ {Φ} → εₑ {Φ} ≅ₑ εₑ {Φ}
id-≅ₑ ξ = reflect-≅ₛ ≡.refl


-- Lemma. commuting semantic renaming and evaluation
postulate
  rename-⊨-evaluate : ∀ {Φ Ψ Θ A} (α : Φ ⊢ A) {𝔈 𝔈′ : Φ ∋→⊨ Ψ} (𝔈≅𝔈′ : 𝔈 ≅ₑ 𝔈′) (ℜ : Ψ ∋→∋ Θ) →
    _≅ₛ_ {A = A} (rename-⊨ ℜ (evaluate α 𝔈)) (evaluate α (rename-⊨ ℜ ∘ 𝔈′))



-- completeness: normal form of equal types are equivalent
postulate
  completeness : ∀ {Φ A} {α α′ : Φ ⊢ A} →
    α ≅ₜ α′ →
    normalize α ≡ normalize α′



-- ===================================================================
-- Soundness of Type Normalization
-- ===================================================================


-- normal type embedding: embed normal type to unnormalized type
embed-⊢⇓ : ∀ {Φ A} → Φ ⊢⇓ A → Φ ⊢  A
embed-⊢↓ : ∀ {Φ A} → Φ ⊢↓ A → Φ ⊢  A

embed-⊢⇓ (`λ α)   = `λ embed-⊢⇓ α
embed-⊢⇓ (α `→ β) = embed-⊢⇓ α `→ embed-⊢⇓ β
embed-⊢⇓ (`Π β)   = `Π embed-⊢⇓ β
embed-⊢⇓ (`μ β)   = `μ embed-⊢⇓ β
embed-⊢⇓ (↓ α)    = embed-⊢↓ α
embed-⊢↓  `⊤      = `⊤
embed-⊢↓ (` x)    = ` x
embed-⊢↓ (β `∙ α) = embed-⊢↓ β `∙ embed-⊢⇓ α


-- Lemma. commuting renaming and normal embedding
rename-embed-⊢⇓ : ∀ {Φ Ψ} (ℜ : Φ ∋→∋ Ψ) {A} (α : Φ ⊢⇓ A) →
  embed-⊢⇓ (rename-⊢⇓ ℜ α) ≡ rename ℜ (embed-⊢⇓ α)
rename-embed-⊢↓ : ∀ {Φ Ψ} (ℜ : Φ ∋→∋ Ψ) {A} (α : Φ ⊢↓ A) →
  embed-⊢↓ (rename-⊢↓ ℜ α) ≡ rename ℜ (embed-⊢↓ α)

rename-embed-⊢⇓ ℜ (`λ β)   = ≡.cong `λ_ (rename-embed-⊢⇓ (weaken-∋→∋ ℜ) β)
rename-embed-⊢⇓ ℜ (α `→ β) = ≡.cong₂ _`→_ (rename-embed-⊢⇓ ℜ α) (rename-embed-⊢⇓ ℜ β)
rename-embed-⊢⇓ ℜ (`Π β)   = ≡.cong `Π_ (rename-embed-⊢⇓ (weaken-∋→∋ ℜ) β)
rename-embed-⊢⇓ ℜ (`μ β)   = ≡.cong `μ_ (rename-embed-⊢⇓ (weaken-∋→∋ ℜ) β)
rename-embed-⊢⇓ ℜ (↓ α)    = rename-embed-⊢↓ ℜ α
rename-embed-⊢↓ ℜ `⊤       = ≡.refl
rename-embed-⊢↓ ℜ (` ξ)    = ≡.refl
rename-embed-⊢↓ ℜ (β `∙ α) = ≡.cong₂ _`∙_ (rename-embed-⊢↓ ℜ β) (rename-embed-⊢⇓ ℜ α)


-- -------------------------------------------------------------------
-- Semantic Forms
-- -------------------------------------------------------------------


-- Relation. semantic form: ``α ≅ α̃`` encodes that ``α`` has semantic form ``α̃``
_⊢≅⊨_ : ∀ {Φ} {A} → Φ ⊢ A → Φ ⊨ A → Set
_⊢≅⊨_ {A = `⋆}     α  α̃       = α ≅ₜ embed-⊢⇓ α̃
_⊢≅⊨_ {A = _ `→ _} α (inj₁ α̃) = α ≅ₜ embed-⊢↓ α̃
_⊢≅⊨_ {A = A `→ B} α (inj₂ f) = Σ (_ , A ⊢ B) λ β →
                                  (α ≅ₜ `λ β) × (∀ {Ψ} (ℜ : _ ∋→∋ Ψ) {γ δ} →
                                                   γ                    ⊢≅⊨ δ →
                                                   rename ℜ (`λ β) `∙ γ ⊢≅⊨ rename-⊨ ℜ (inj₂ f) ∙ δ)


-- Lemma. semantic form from neutral embedding
postulate
  reflect-⊢≅⊨ : ∀ {Φ A} {α : Φ ⊢ A} {α′ : Φ ⊢↓ A} →
    α ≅ₜ  embed-⊢↓ α′ →
    α ⊢≅⊨ reflect α′

-- Lemma. semantic form to reified normal embedding
postulate
  reify-⊢≅⊨ : ∀ {Φ A} {α : Φ ⊢ A} {α′ : Φ ⊨ A} →
    α ⊢≅⊨ α′ →
    α ≅ₜ  embed-⊢⇓ (reify α′)


-- Relation. environmental semantic form: ``𝔖 ⊢≅⊨ₑ 𝔈`` encodes that ``𝔖`` has environmental semantic form ``𝔈``
_⊢≅⊨ₑ_ : ∀ {Φ Ψ} → Φ ∋→⊢ Ψ → Φ ∋→⊨ Ψ → Set
_⊢≅⊨ₑ_ {Φ} 𝔖 𝔈 = ∀ {X} (ξ : Φ ∋ X) → 𝔖 ξ ⊢≅⊨ 𝔈 ξ


-- Lemma. semantic form from environmental semantic form
postulate
  substitute-⊢≅⊨-evaluate : ∀ {Φ Ψ A} (α : Φ ⊢ A) {𝔖 : Φ ∋→⊢ Ψ} {𝔈 : Φ ∋→⊨ Ψ} →
    𝔖 ⊢≅⊨ₑ 𝔈 →
    substitute 𝔖 α ⊢≅⊨ evaluate α 𝔈


-- Lemma. the quoting renaming has envrionmental semantic form ``εₑ``
`-⊢≅⊨-εₑ : ∀ {Φ} → `_ ⊢≅⊨ₑ (εₑ {Φ})
`-⊢≅⊨-εₑ = reflect-⊢≅⊨ ∘ (λ α → refl {α = α}) ∘ `_


-- soundness: normalization preserves normal forms
soundness : ∀ {Φ A} (α : Φ ⊢ A) →
  α ≅ₜ embed-⊢⇓ (normalize α)

soundness α = ≡.subst (_≅ₜ embed-⊢⇓ (normalize α))
                      (substitute-identity α)
                      (reify-⊢≅⊨ (substitute-⊢≅⊨-evaluate α `-⊢≅⊨-εₑ))



-- ===================================================================
-- Stability of Type Normalization
-- ===================================================================


postulate
  stability    : ∀{A ϕ} (α : ϕ ⊢⇓ A) → normalize (embed-⊢⇓ α)          ≡ α
  stability-⊢↓ : ∀{A ϕ} (α : ϕ ⊢↓ A) → evaluate  (embed-⊢↓ α) (εₑ {ϕ}) ≡ reflect α



-- ===================================================================
-- Type Substitution Preserves Normality
-- ===================================================================


-- Relation. Normal Substitution
_∋→⊢⇓_ : Context → Context → Set
Φ ∋→⊢⇓ Ψ = ∀ {A} → Φ ∋ A → Ψ ⊢⇓ A


-- weaken Normal Substitution to a larger Context
weaken-∋→⊢⇓ : ∀ {Φ Ψ} →
          Φ     ∋→⊢⇓ Ψ →
  ∀ {A} → Φ , A ∋→⊢⇓ Ψ , A
weaken-∋→⊢⇓ 𝔖  head    = ↓ ` head
weaken-∋→⊢⇓ 𝔖 (tail α) = weaken-⊢⇓ (𝔖 α)


-- extend Normal Substitution to larger source Context
extend-∋→⊢⇓ : ∀ {Φ Ψ} →
                       Φ     ∋→⊢⇓ Ψ →
  ∀ {A} (α : Ψ ⊢⇓ A) → Φ , A ∋→⊢⇓ Ψ
extend-∋→⊢⇓ 𝔖 A  head    = A
extend-∋→⊢⇓ 𝔖 A (tail α) = 𝔖 α


-- apply Normal Substitution
substitute-⊢⇓ : ∀ {Φ Ψ} →
  Φ ∋→⊢⇓ Ψ →
  ∀ {A} → Φ ⊢⇓ A → Ψ ⊢⇓ A
substitute-⊢⇓ ℜ α = normalize (substitute (embed-⊢⇓ ∘ ℜ) (embed-⊢⇓ α))


-- apply single Normal Substitution
_[_]⇓ : ∀ {Φ A B} →
  Φ , A ⊢⇓ B →
  Φ     ⊢⇓ A →
  Φ     ⊢⇓ B
β [ α ]⇓ = substitute-⊢⇓ (extend-∋→⊢⇓ (↓_ ∘ `_) α) β


-- the identity Normal Substitution
ε-∋→⊢⇓ : ∀ {Φ} → Φ ∋→⊢⇓ Φ
ε-∋→⊢⇓ = ↓_ ∘ `_

-- Lemma. ``ε-∋→⊢⇓`` is the identity Normal Substitution
postulate
  substitute-⊢⇓-identity : ∀ {Φ A} (α : Φ ⊢⇓ A) →
    substitute-⊢⇓ ε-∋→⊢⇓ α ≡ α


-- Lemma. expand normal renaming of normal single substitution
postulate
  rename-[]⇓ : ∀ {Φ Ψ A B} (ℜ : Φ ∋→∋ Ψ) (β : Φ , A ⊢⇓ B) (α : Φ ⊢⇓ A) →
    rename-⊢⇓ ℜ (β [ α ]⇓) ≡
    rename-⊢⇓ (weaken-∋→∋ ℜ) β [ rename-⊢⇓ ℜ α ]⇓


-- Lemma. commute normal weakening nad normal substitution
postulate
  weaken-⊢⇓-substitute-⊢⇓ : ∀ {Φ Ψ} (𝔖 : Φ ∋→⊢⇓ Ψ) {A} (α : Φ ⊢⇓ `⋆) →
    weaken-⊢⇓ {A = A} (substitute-⊢⇓ 𝔖 α) ≡
    substitute-⊢⇓ (weaken-∋→⊢⇓ 𝔖) (weaken-⊢⇓ α)


-- Lemma. expand normal substitution by weakened Normal Substitution
postulate
  substitute-⊢⇓-weaken-∋→⊢⇓ : ∀ {Φ Ψ} (𝔖 : Φ ∋→⊢⇓ Ψ) {A} (β : Φ , A ⊢⇓ `⋆) →
    substitute-⊢⇓ (weaken-∋→⊢⇓ 𝔖) β ≡
    evaluate (substitute (weaken-∋→⊢ (embed-⊢⇓ ∘ 𝔖)) (embed-⊢⇓ β)) (weakenₑ εₑ)


-- Lemma. expand normal substitution on single normal substitution
postulate
  substitute-⊢⇓-[]⇓ : ∀ {Φ Ψ A} (𝔖 : Φ ∋→⊢⇓ Ψ) (α : Φ ⊢⇓ A) (β : Φ , A ⊢⇓ `⋆) →
    substitute-⊢⇓ 𝔖 (β [ α ]⇓) ≡
    evaluate (substitute (weaken-∋→⊢ (embed-⊢⇓ ∘ 𝔖)) (embed-⊢⇓ β)) (weakenₑ εₑ) [ substitute-⊢⇓ 𝔖 α ]⇓


-- Lemma. normal single-substituting of weakened Type cancels out
postulate
  weaken-⊢⇓-[] : ∀ {Φ A} (α : Φ ⊢⇓ A) (β : Φ ⊢⇓ `⋆)  →
    β ≡ weaken-⊢⇓ β [ α ]⇓
