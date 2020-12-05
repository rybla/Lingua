open import Level using (0ℓ)
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PE
  using (_≡_; refl)
open import Relation.Nullary
open import Data.Empty
open import Data.Nat as Nat using (ℕ; zero; _⊔_) renaming (suc to 1+)
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin) renaming (zero to #0; suc to #1+)
import Data.Fin.Properties as FinProperties
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Product

open import Language.Lambda.Grammar.Definitions as Definitions
  hiding (Type; Term)


module Language.Lambda.Grammar.DecidableEquality where


module Type where

  -- postulate
  --   _≟_ : Decidable {A = Definitions.Type} _≡_

  _≟_ : Decidable {A = Definitions.Type} _≡_

  `𝟘 ≟ `𝟘 = yes refl
  `𝟘 ≟ `𝟙 = no λ ()
  `𝟘 ≟ (_ `→ _) = no λ ()
  
  `𝟙 ≟ `𝟙 = yes refl
  `𝟙 ≟ `𝟘 = no λ ()
  `𝟙 ≟ (_ `→ _) = no λ ()

  (β `→ α) ≟ (γ `→ δ) with β ≟ γ | α ≟ δ
  ... | yes refl | yes refl = yes refl
  ... | yes β≡α  | no γ≢δ   = no λ { refl → γ≢δ refl }
  ... | no  β≢α  | _        = no λ { refl → β≢α refl }
  (β `→ α) ≟ `𝟘 = no λ ()
  (β `→ α) ≟ `𝟙 = no λ ()


  ≡-isDecEquivalence : IsDecEquivalence (_≡_ {A = Definitions.Type})
  ≡-isDecEquivalence = record
    { isEquivalence = PE.isEquivalence
    ; _≟_ = _≟_ }

  decSetoid : DecSetoid 0ℓ 0ℓ
  decSetoid = record { isDecEquivalence = ≡-isDecEquivalence }

  open DecSetoid decSetoid public
    hiding (_≟_)
  

module Term where

  _≟_ : ∀ {n} → Decidable {A = Definitions.Term n} _≡_

  `1 ≟ `1 = yes refl
  `1 ≟ (_ `∙ _) = no λ ()
  `1 ≟ (`λ _ `⦂ _ `⇒ _) = no λ ()
  
  (` n) ≟ (` .n) = yes refl
  (` n) ≟ (b `∙ b₁) = no λ ()
  (` n) ≟ (`λ .(1+ n) `⦂ α `⇒ b) = no λ ()
  (` n) ≟ (`↑ b) = no λ ()

  (a `∙ b) ≟ (c `∙ d) with a ≟ c | b ≟ d
  ...                    | yes refl | yes refl = yes refl
  ...                    | yes a≡c  | no  b≢d  = no λ { refl → b≢d refl }
  ...                    | no  a≢c  | _        = no λ { refl → a≢c refl }
  (a `∙ b) ≟ `1 = no λ ()
  (a `∙ b) ≟ (` n) = no λ ()
  (a `∙ b) ≟ (`λ _ `⦂ α `⇒ c) = no λ ()
  (a `∙ b) ≟ (`↑ c) = no λ ()

  (`λ n `⦂ α `⇒ b) ≟ (`λ .n `⦂ β `⇒ d) with α Type.≟ β | b ≟ d
  ...                                     | yes refl   | yes refl = yes refl
  ...                                     | yes α≡β    | no  b≢d  = no λ { refl → b≢d refl }
  ...                                     | no  α≢β    | _        = no λ { refl → α≢β refl }
  (`λ .0 `⦂ α `⇒ a) ≟ `1 = no λ ()
  (`λ .(1+ n) `⦂ α `⇒ a) ≟ (` n) = no λ ()
  (`λ n `⦂ α `⇒ a) ≟ (b `∙ b₁) = no λ ()
  (`λ .(1+ _) `⦂ α `⇒ a) ≟ (`↑ b) = no λ ()

  (`↑ a) ≟ (`↑ b) with a ≟ b
  ...                | yes refl = yes refl
  ...                | no  a≢b  = no λ { refl → a≢b refl }
  (`↑ a) ≟ (` _) = no λ ()
  (`↑ a) ≟ (b `∙ b₁) = no λ ()
  (`↑ a) ≟ (`λ .(1+ _) `⦂ α `⇒ b) = no λ ()
  

  ≡-isDecEquivalence : ∀ {n} → IsDecEquivalence (_≡_ {A = Definitions.Term n})
  ≡-isDecEquivalence = record
    { isEquivalence = PE.isEquivalence
    ; _≟_ = _≟_ }

  decSetoid : ∀ {n} → DecSetoid 0ℓ 0ℓ
  decSetoid {n} = record { isDecEquivalence = ≡-isDecEquivalence {n} }

  module _ {n} where
    open DecSetoid (decSetoid {n}) public
      hiding (_≟_)
