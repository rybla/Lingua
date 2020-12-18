import Level
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary using (Rel)
open import Relation.Nullary.Decidable
open import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Product renaming (_,_ to _&_)

open import Language.Lambda2.Kinding as ♯
  using
    ( `⋆ ; _`→_
    ; ø ; _,_
    ; head ; tail
    ; `⊤ ; `_ ; `Π_ ; `λ_ ; _`∙_ ; `μ_
    ; refl ; trans ; subst
    ; ↓_ )

module Language.Lambda2.Typing where


infix 4 _∋_ _⊢_
infixl 6 _,_ _,♯_

infixl 8 _`∙_
infixr 9 `λ_
infixr 11 `_



-- ===================================================================
-- Type Context
-- ===================================================================


-- Type Context
data Context : ♯.Context → Set where

  -- empty Context
  ø : Context ø

  -- Type in Context
  _,_ : ∀ {Φ} → Context Φ → Φ ♯.⊢ `⋆ → Context Φ

  -- Kind in Context
  _,♯_ : ∀ {Φ} → Context Φ → ∀ X → Context (Φ , X)


-- Term Name
data _∋_ : ∀ {Φ : ♯.Context} (Γ : Context Φ) → Φ ♯.⊢ `⋆ → Set where

  head : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} →
    ------------------------------------------------
    Γ , α ∋ α

  tail : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} {β : Φ ♯.⊢ `⋆} →
    Γ     ∋ α →
    ------------------------------------------------
    Γ , β ∋ α

  tail♯ : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} {B} →
    Γ      ∋ α →
    ------------------------------------------------
    Γ ,♯ B ∋ ♯.weaken-⊢ α



-- ===================================================================
-- Terms
-- ===================================================================


-- Term with unnormalized Type
data _⊢_ {Φ} Γ : Φ ♯.⊢ `⋆ → Set where

  -- unit
  `● :
    ------------------------------------------------
    Γ ⊢ `⊤

  -- name
  `_ : ∀ {α} →
    Γ ∋ α →
    ------------------------------------------------
    Γ ⊢ α

  -- function
  `λ_ : ∀ {α β} →
    Γ , α ⊢ β →
    ------------------------------------------------
    Γ ⊢ α `→ β

  -- application
  _`∙_ : ∀ {α β} →
    Γ ⊢ α `→ β →
    Γ ⊢ α →
    ------------------------------------------------
    Γ ⊢ β

  -- polymorphism function
  `Λ_ : ∀ {A B} →
    Γ ,♯ A ⊢ B →
    ------------------------------------------------
    Γ      ⊢ `Π B

  -- polymorphism application
  _`∙♯_ : ∀ {A β} →
    (b : Γ   ⊢ `Π β) →
    (α : Φ ♯.⊢ A   ) →
    ------------------------------------------------
    Γ ⊢ β ♯.[ α ]

  -- fold fixpoint
  `fold :
    ∀ α →
    Γ ⊢ α ♯.[ `μ α ] →
    ------------------------------------------------
    Γ ⊢ `μ α

  -- unfold fixpoint
  `unfold : ∀ {α} →
    Γ ⊢ `μ α →
    ------------------------------------------------
    Γ ⊢ α ♯.[ `μ α ]

  -- cast between equal types
  `cast : ∀ {α α′} →
    α ♯.≅ₜ α′ →
    Γ ⊢ α →
    ------------------------------------------------
    Γ ⊢ α′


length : ∀ {Φ} → Context Φ → ℕ
length ø        = 0
length (Γ ,  _) = 1 + length Γ
length (Γ ,♯ _) = length Γ


cast-∋ : ∀ {Φ Γ} {α α′ : Φ ♯.⊢ `⋆} →
  α ≡ α′ →
  Γ ∋ α →
  Γ ∋ α′
cast-∋ refl a = a
