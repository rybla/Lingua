open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _×_)

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.Properties
open import Language.Lambda.Typing


module Language.Lambda.Reduction where


-- substitution
infixr 17 _↦_,_
infixr 18 _↦_
data Substitution : Set where
  ∙-substitution : Substitution
  _↦_,_ : Name → Term → Substitution → Substitution

_↦_ : Name → Term → Substitution
x ↦ t = x ↦ t , ∙-substitution


-- without
_⊝_ : Substitution → Name → Substitution
∙-substitution ⊝ x = ∙-substitution
(x ↦ t , subs) ⊝ y with x Name.≟ y
... | yes _ = subs ⊝ y
... | no  _ = x ↦ t , subs ⊝ y

-- substitute
infixr 16 [_]#_
[_]#_ : Substitution → Term → Term
[ ∙-substitution ]# t = t
[ x ↦ s , subs ]# (` y) with x Name.≟ y
... | yes _ = s
... | no  _ = ` y
[ x ↦ s , subs ]# (t `⋆ u) = [ x ↦ s , subs ]# t `⋆ [ x ↦ s , subs ]# u
[ subs@(_ ↦ _ , _) ]# (`λ y `⦂ τ `⇒ t) = `λ y `⦂ τ `⇒ [ subs ⊝ y ]# t


-- small-step reductions
infix 10 _⟶_
data _⟶_ : Term → Term → Set where
  reduce-argument : ∀ s t t′ →
    t ⟶ t′ →
    s `⋆ t ⟶ s `⋆ t′
  reduce-application : ∀ x τ s t →
    (`λ x `⦂ τ `⇒ s) `⋆ t ⟶ [ x ↦ t ]# s


-- value predicate
IsValue : Term → Set
IsValue t = ¬ (∃[ t′ ] (t ⟶ t′))


-- big-step reductions
infix 10 _⟶*_
data _⟶*_ : Term → Term → Set where
  reduce*-id : ∀ t → t ⟶* t
  reduct*-lift : ∀ t t′ →
    t ⟶ t′ →
    t ⟶* t′
  reduce*-argument : ∀ s t t′ →
    t ⟶* t′ →
    s `⋆ t ⟶* s `⋆ t′
  reduce*-applicant : ∀ s s′ t →
    IsValue t →
    s ⟶* s′ →
    s `⋆ t ⟶* s′ `⋆ t
    

-- evaluation
_⇓_ : Term → Term → Set
t ⇓ v = t ⟶* v × IsValue v


-- strongly normalziing
