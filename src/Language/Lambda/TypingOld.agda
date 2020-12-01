import Level
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality -- hiding ([_])
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _×_)
open import Data.List using (List; []; _∷_; [_]; _++_)

open import Data.Maybe using (Maybe; just; nothing; maybe)
import Data.Maybe.Categorical as MaybeCategorical
import Category.Monad as Monad
open Monad.RawMonadPlus (MaybeCategorical.monadPlus {Level.zero})

open import Language.Lambda.Grammar.Definitions
open import Language.Lambda.Grammar.Properties


module Language.Lambda.Typing where


-- context
infixr 17 _⦂_,_
infixr 18 _⦂_
data Context : Set where
  ∙-context : Context
  _⦂_,_ : Name → Type → Context → Context

_⦂_ : Name → Type → Context
x ⦂ τ = x ⦂ τ , ∙-context


-- bound-names : Term → List Name
-- bound-names (` x) = []
-- bound-names (s `⋆ t) = bound-names s ++ bound-names t
-- bound-names (`λ x `⦂ τ `⇒ t) = x ∷ bound-names t


-- free variables
infix 11 _∈FV_
data _∈FV_ : Name → Term → Set where

  name : ∀ x y →
    x ≢ y →
    ---------------------------------------------
    x ∈FV ` y 

  application : ∀ x s t →
    x ∈FV s  →
    x ∈FV t  →
    ---------------------------------------------
    x ∈FV s `⋆ t

  function : ∀ x y τ t →
    x ≢ y →
    x ∈FV t →
    ---------------------------------------------
    x ∈FV `λ y `⦂ τ `⇒ t

_∉FV_ : Name → Term → Set
x ∉FV t = ¬ x ∈FV t


-- typing judgement
infix 10 _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where

  head : ∀ {Γ x τ} →
    ---------------------------------------------
    x ⦂ τ , Γ ⊢ ` x ⦂ τ

  tail : ∀ {Γ t x σ τ} →
    Γ ⊢ t ⦂ σ →
    x ∈FV t →
    ---------------------------------------------
    x ⦂ τ , Γ ⊢ t ⦂ σ

  function : ∀ {Γ x t σ τ} →
    x ⦂ σ , Γ ⊢ t ⦂ τ →
    ---------------------------------------------
    Γ ⊢ (`λ x `⦂ σ `⇒ t) ⦂ σ `→ τ

  application : ∀ {Γ f s t σ τ} →
    Γ ⊢ f ⦂ σ `→ τ →
    Γ ⊢ s ⦂ σ →
    ---------------------------------------------
    Γ ⊢ f `⋆ t ⦂ τ



-- examples

_ : ∀ σ τ f x → f ≢ x →
  f ⦂ σ `→ τ , x ⦂ σ ⊢ ` f `⋆ ` x ⦂ τ
_ = λ σ τ f x f≢x →
  application
    head
    (tail head (name f x f≢x))

infer-name : Context → Name → Maybe Type
infer-name ∙-context x = nothing
infer-name (y ⦂ τ , Γ) x with x Name.≟ y
...                         | yes _ = just τ
...                         | no  _ = nothing


-- type unification
unify : Type → Type → Maybe Type
unify σ τ with σ Type.≟ τ
...          | yes _ = just σ
...          | no  _ = nothing


infer : Context → Term → Maybe Type
check : Context → Term → Type → Maybe ⊤

-- type inference
infer Γ (` x) = infer-name Γ x
infer Γ (s `⋆ t) with infer Γ s
...                 | just `⊤ = nothing
...                 | just (σ `→ τ) = do check Γ t τ ; return τ
...                 | nothing = nothing
infer Γ (`λ x `⦂ σ `⇒ t) = do τ ← infer (x ⦂ σ , Γ) t ; return (σ `→ τ)

-- type checking
check Γ (` x)            τ = do τ′ ← infer-name Γ x ; unify τ τ′ ; return tt
check Γ (s `⋆ t)         τ with infer Γ s | infer Γ t
...                           | just `⊤         | just σ  = nothing
...                           | just (σ′ `→ τ′) | just σ  = do unify σ σ′ ; unify τ τ′ ; return tt
...                           | just  _         | nothing = nothing
...                           | nothing         | just _  = nothing
...                           | nothing         | nothing = nothing
check Γ (`λ x `⦂ σ `⇒ t) τ = do ρ ← infer (x ⦂ σ , Γ) t ; unify (σ `→ ρ) τ ; return tt


--
-- type checking is correct
--

check→judgment : ∀ Γ t τ → check Γ t τ ≡ just tt → Γ ⊢ t ⦂ τ
check→judgment Γ t τ H = {!!}


x≟x≡yes : ∀ (t : Term) → t Term.≟ t ≡ yes refl
x≟x≡yes t with t Term.≟ t
... | yes refl = refl
... | no ¬t≡t = ⊥-elim (¬t≡t refl)

lem1 : ∀ (Γ : Context) (x : Name) (t : Term) (τ τ′ : Type) →
  x ∈FV t →
  check Γ t τ′ ≡ just tt →
  check (x ⦂ τ , Γ) t τ′ ≡ just tt
lem1 Γ x (`  y) τ τ′  x∈FVt           checked with x Name.≟ y
lem1 Γ x (` .x) τ τ′ (name .x .x x≢y) checked    | yes refl = ⊥-elim (x≢y refl)
lem1 Γ x (`  y) τ τ′  x∈FVt           checked    | no ¬x≡y = {!!}

lem1 Γ x (t `⋆ t₁) τ τ′ x∈FVt checked = {!!}
lem1 Γ x (`λ x₁ `⦂ x₂ `⇒ t) τ τ′ x∈FVt checked = {!!}

judgment→check : ∀ Γ t τ → Γ ⊢ t ⦂ τ → check Γ t τ ≡ just tt
-- judgment→check Γ t τ Γ⊢t⦂τ = ?
judgment→check (x ⦂ τ , Γ) .(` x) .τ   head with x Name.≟ x
judgment→check (x ⦂ τ , Γ) .(` x) .τ   head | yes x≡x with τ Type.≟ τ
judgment→check (x ⦂ τ , Γ) .(` x) .τ   head | yes x≡x | yes τ≡τ = refl
judgment→check (x ⦂ τ , Γ) .(` x) .τ   head | yes x≡x | no ¬τ≡τ = ⊥-elim (¬τ≡τ refl)
judgment→check (x ⦂ τ , Γ) .(` x) .τ   head | no ¬x≡x = ⊥-elim (¬x≡x refl)
judgment→check (x ⦂ τ , Γ)  t      τ′ (tail Γ⊢t⦂τ x∈FVt) = {!judgment→check Γ t τ′ Γ⊢t⦂τ !}
judgment→check Γ .(`λ _ `⦂ _ `⇒ _) .(_ `→ _) (function Γ⊢t⦂τ) = {!!}
judgment→check Γ .(_ `⋆ _) τ (application Γ⊢t⦂τ Γ⊢t⦂τ₁) = {!!}

-- judgment→check Γ (` x) τ Γ⊢t⦂τ           with infer-name Γ x | inspect (infer-name Γ) x
-- judgment→check .(x ⦂ τ  , _) (` x)  τ  head | just τ′        | [ eq₁  ]                 with unify τ τ′ | inspect (unify τ) τ′ 
-- judgment→check .(x ⦂ τ  , _) (` x)  τ  head | just τ′        | [ eq₁  ]                    | just σ     | [ eq₂ ]              = refl
-- judgment→check .(x ⦂ τ  , _) (` x)  τ  head | just τ′        | [ eq₁  ]                    | nothing    | [ eq₂ ]              with τ Type.≟ τ′ | x Name.≟ x
-- judgment→check .(x ⦂ τ  , _) (` x)  τ  head | just τ′        | [ eq₁  ]                    | nothing    | [ ()  ]                 | yes τ≡τ′    | yes x≡x
-- judgment→check .(x ⦂ τ  , _) (` x)  τ  head | just τ′        | [ eq₁  ]                    | nothing    | [ ()  ]                 | yes τ≡τ′    | no ¬x≡x
-- judgment→check .(x ⦂ τ′ , _) (` x) .τ′ head | just τ′        | [ refl ]                    | nothing    | [ eq₂ ]                 | no ¬τ≡τ′    | yes x≡x     = ⊥-elim (¬τ≡τ′ refl)
-- judgment→check .(x ⦂ τ  , _) (` x)  τ  head | just τ′        | [ eq₁  ]                    | nothing    | [ eq₂ ]                 | no ¬τ≡τ′    | no ¬x≡x     = ⊥-elim (¬x≡x refl)

-- judgment→check .(_ ⦂ _ , _) (` x) τ (tail Γ⊢t⦂τ x₁) | just τ′ | [ eq₁ ] with unify τ τ′ | inspect (unify τ) τ′
-- judgment→check .(_ ⦂ _ , _) (` x) τ (tail Γ⊢t⦂τ x₁) | just τ′ | [ eq₁ ]    | just σ | [ eq₂ ] = refl
-- judgment→check .(_ ⦂ _ , _) (` x) τ (tail Γ⊢t⦂τ x₁) | just τ′ | [ eq₁ ]    | nothing | [ eq₂ ] = {!!}

-- judgment→check Γ (` x) τ Γ⊢t⦂τ    | nothing | [ _ ] = {! !}

-- judgment→check Γ (t `⋆ t₁) τ Γ⊢t⦂τ = {!!}

-- judgment→check Γ (`λ x `⦂ x₁ `⇒ t) τ Γ⊢t⦂τ = {!!}


-- judgment→check : ∀ Γ t τ → Γ ⊢ t ⦂ τ → check Γ t τ ≡ just tt
-- judgment→check (x ⦂ τ , Γ) .(` x) τ head
--   with x Name.≟ x | τ Type.≟ τ | inspect (unify τ) τ
-- ...  | yes x≡x    | yes τ≡τ    | [ uni ] rewrite uni = refl
-- ...  | yes x≡x    | no ¬τ≡τ    | _ = ⊥-elim (¬τ≡τ refl)
-- ...  | no ¬x≡x    | yes τ≡τ    | _ = ⊥-elim (¬x≡x refl)
-- ...  | no ¬x≡x    | no ¬τ≡τ    | _ = ⊥-elim (¬x≡x refl)
-- judgment→check (x ⦂ τ , Γ) (` x₁) τ′ (tail Γ⊢t⦂τ x∈FVt) = {!!}
-- judgment→check (x ⦂ τ , Γ) (t `⋆ t₁) τ′ (tail Γ⊢t⦂τ x∈FVt) = {!!}
-- judgment→check (x ⦂ τ , Γ) (`λ x₁ `⦂ x₂ `⇒ t) τ′ (tail Γ⊢t⦂τ x∈FVt) = {!!}
-- judgment→check Γ .(`λ _ `⦂ _ `⇒ _) .(_ `→ _) (function Γ⊢t⦂τ) = {!!}
-- judgment→check Γ .(_ `⋆ _) τ (application Γ⊢t⦂τ Γ⊢t⦂τ₁) = {!!}
  
-- check↔judgment : ∀ Γ t τ → check Γ t τ ≡ just tt ⇔ Γ ⊢ t ⦂ τ
-- check↔judgment Γ t τ = ?
  
