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

  `⊤ ≟ `⊤ = yes refl
  `⊤ ≟ (_ `→ _) = no λ ()

  (σ `→ τ) ≟ (υ `→ φ) with σ ≟ υ | τ ≟ φ
  ... | yes refl | yes refl = yes refl
  ... | yes σ≡τ  | no υ≢φ   = no λ { refl → υ≢φ refl }
  ... | no  σ≢τ  | _        = no λ { refl → σ≢τ refl }
  (σ `→ τ) ≟ `⊤ = no λ ()


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
  (` n) ≟ (` .n) = yes refl
  (` n) ≟ (_ `⋆ _)         = no λ ()
  (` n) ≟ (`λ _ `⦂ _ `⇒ _) = no λ ()
  (` n) ≟ (`↑ _)           = no λ ()

  (s `⋆ t) ≟ (q `⋆ r) with s ≟ q    | t ≟ r
  ...                    | yes refl | yes refl = yes refl
  ...                    | yes s≡q  | no  t≢r  = no λ { refl → t≢r refl }
  ...                    | no  s≢q  | _        = no λ { refl → s≢q refl }
  (s `⋆ t) ≟ (` _)            = no λ ()
  (s `⋆ t) ≟ (`λ _ `⦂ _ `⇒ _) = no λ () 
  (s `⋆ t) ≟ (`↑ _)           = no λ ()

  (`λ n `⦂ τ `⇒ s) ≟ (`λ .n `⦂ σ `⇒ t) with τ Type.≟ σ | s ≟ t
  ...                                     | yes refl   | yes refl = yes refl
  ...                                     | yes τ≡σ    | no  s≢t  = no λ { refl → s≢t refl }
  ...                                     | no  τ≢σ    | _        = no λ { refl → τ≢σ refl }
  (`λ n `⦂ τ `⇒ s) ≟ (` _)    = no λ ()
  (`λ n `⦂ τ `⇒ s) ≟ (_ `⋆ _) = no λ ()
  (`λ n `⦂ τ `⇒ s) ≟ (`↑ _)   = no λ ()

  (`↑ s) ≟ (`↑ t) with s ≟ t
  ...                | yes refl = yes refl
  ...                | no  s≢t  = no λ { refl → s≢t refl }
  (`↑ s) ≟ (` _)            = no λ ()
  (`↑ s) ≟ (_ `⋆ _)         = no λ ()
  (`↑ s) ≟ (`λ _ `⦂ _ `⇒ _) = no λ ()


  ≡-isDecEquivalence : ∀ {n} → IsDecEquivalence (_≡_ {A = Definitions.Term n})
  ≡-isDecEquivalence = record
    { isEquivalence = PE.isEquivalence
    ; _≟_ = _≟_ }

  decSetoid : ∀ {n} → DecSetoid 0ℓ 0ℓ
  decSetoid {n} = record { isDecEquivalence = ≡-isDecEquivalence {n} }

  module _ {n} where
    open DecSetoid (decSetoid {n}) public
      hiding (_≟_)
