import Level
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)
open import Relation.Binary using (Rel)
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Product as Product using (_×_; ∃-syntax; Σ-syntax) renaming (_,_ to _&_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; map)


open import Language.Lambda2.Kinding as ♯
  using
    ( `⋆ ; _`→_
    ; ø ; _,_
    ; head ; tail
    ; `⊤ ; `_ ; `Π_ ; `λ_ ; _`∙_ ; `μ_
    ; refl ; trans ; subst
    ; ↓_ )

open import Language.Lambda2.Typing as ⅋
  using
    ( `● ; `_ ; `λ_ ; `Λ_ ; _`∙_ ; _`∙♯_ ; `fold ; `unfold ; `cast )

open import Language.Lambda2.TypingNormal as ¡
  using
    ( Context ; ø ; _,♯_ ; _,_
    ; _∋_ ; head ; tail ; tail♯
    ; _⊢_ ; `● ; `_ ; `λ_ ; `Λ_ ; _`∙_ ; _`∙♯_ ; `fold ; `unfold )
  


module Language.Lambda2.TypeErasure where


infix 4 _⊣ _⇓ _⟶_ _⟶*_
infix 5 _#→#_ _#→⊣_
infix 11 _[_]



-- ===================================================================
-- Type-Erased Terms
-- ===================================================================
-- Terms encoded without their Types

data _⊣ : ℕ → Set where
  `●   : ∀ {n} → n ⊣
  `_   : ∀ {n} (x   : Fin n)   → n ⊣
  `λ_  : ∀ {n} (b   : suc n ⊣) → n ⊣
  _`∙_ : ∀ {n} (b a : n ⊣)     → n ⊣



-- ===================================================================
-- Type Erasure (Unnormalized)
-- ===================================================================
-- Erase Types of Terms with unnormalized Types.

module ⅋-Erasure where


  erase-Name : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} →
    Γ ⅋.∋ α →
    Fin (⅋.length Γ)
  erase-Name  ⅋.head     = zero
  erase-Name (⅋.tail x)  = suc (erase-Name x)
  erase-Name (⅋.tail♯ x) = erase-Name x


  erase : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} →
    Γ ⅋.⊢ α →
    ⅋.length Γ ⊣
  erase  `●         = `●
  erase (` x)       = ` erase-Name x
  erase (`λ a)      = `λ erase a
  erase (b `∙ a)    = erase a `∙ erase b
  erase (`Λ a)      = erase a
  erase (a `∙♯ α)   = erase a
  erase (`fold α a) = erase a
  erase (`unfold a) = erase a
  erase (`cast _ a) = erase a



-- ===================================================================
-- Type Erasure (Normalized)
-- ===================================================================
-- Erase Types of Terms with Normal Types.
-- Type-normalization should preserve type-erasure form.


-- erase Normal Type of Term Name
erase-Name : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} → Γ ∋ α → Fin (¡.length Γ)
erase-Name  head     = zero
erase-Name (tail  x) = suc (erase-Name x)
erase-Name (tail♯ x) = erase-Name x


-- erase Normal Type of Term
erase : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} → Γ ⊢ α → ¡.length Γ ⊣
erase  `●         = `●
erase (` x)       = ` erase-Name x
erase (`λ a)      = `λ erase a
erase (b `∙ a)    = erase b `∙ erase a
erase (`Λ a)      = erase a
erase (a `∙♯ α)   = erase a
erase (`fold α a) = erase a
erase (`unfold a) = erase a


-- Lemma. Context-normalization preserves Context length
length-normalize-Context : ∀ {Φ} (Γ : ⅋.Context Φ) →
  ¡.length (¡.normalize-Context Γ) ≡ ⅋.length Γ
length-normalize-Context  ⅋.ø       = ≡.refl
length-normalize-Context (Γ ⅋.,  ξ) = ≡.cong suc (length-normalize-Context Γ)
length-normalize-Context (Γ ⅋.,♯ X) = length-normalize-Context Γ
  

-- Lemma. normalizing a Term's Type preserves the erased form
postulate
  erase-normalize-Type-≡ : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} (a : Γ ⅋.⊢ α) →
    ⅋-Erasure.erase a ≡
    ≡.subst _⊣ (length-normalize-Context Γ) (erase (¡.normalize-Type a))



-- -------------------------------------------------------------------
-- Renaming
-- -------------------------------------------------------------------


-- Type-erased Renaming
_#→#_ : Rel ℕ Level.zero
m #→# n = Fin m → Fin n


-- weaken Type-erased Renaming to larger Context
weaken-#→# : ∀ {m n} → m #→# n → suc m #→# suc n
weaken-#→# 𝔯  zero   = zero
weaken-#→# 𝔯 (suc x) = suc (𝔯 x)


-- Lemma. congruence over weakened Type-erased Renaming
weaken-#→#-cong : ∀ {m n} {𝔯 𝔯′ : m #→# n} →
  (∀ a → 𝔯 a ≡ 𝔯′ a) →
  (x : Fin (suc m)) →
    weaken-#→# 𝔯 x ≡ weaken-#→# 𝔯′ x

weaken-#→#-cong eq  zero   = ≡.refl
weaken-#→#-cong eq (suc x) = ≡.cong suc (eq x)


-- Lemma. Type-erased weakening preserves identity
weaken-#→#-identity : ∀ {n} (x : Fin (suc n)) →
  id x ≡ weaken-#→# id x

weaken-#→#-identity  zero   = ≡.refl
weaken-#→#-identity (suc x) = ≡.refl


-- apply Type-erased Renaming
rename : ∀ {m n} → m #→# n → m ⊣ → n ⊣
rename 𝔯  `● = `●
rename 𝔯 (` x) = ` 𝔯 x
rename 𝔯 (`λ b) = `λ rename (weaken-#→# 𝔯) b 
rename 𝔯 (b `∙ a) = rename 𝔯 b `∙ rename 𝔯 a


-- Lemma. congruence over Type-erased renaming
rename-cong : ∀ {m n} {𝔯 𝔯′ : m #→# n} →
  (∀ x → 𝔯 x ≡ 𝔯′ x) →
  (a : m ⊣) →
  rename 𝔯 a ≡ rename 𝔯′ a
  
rename-cong eq  `●      = ≡.refl
rename-cong eq (` x)    = ≡.cong `_ (eq x)
rename-cong eq (`λ b)   = ≡.cong `λ_ (rename-cong (weaken-#→#-cong eq) b)
rename-cong eq (b `∙ a) = ≡.cong₂ _`∙_ (rename-cong eq b) (rename-cong eq a)


-- Lemma. Type-erased Renaming by ``id`` is ``id``
rename-identity : ∀ {n} (a : n ⊣) →
  a ≡ rename id a

rename-identity  `●      = ≡.refl
rename-identity (` x)    = ≡.refl
rename-identity (`λ b)   = ≡.cong `λ_ (≡.trans (rename-identity b) (rename-cong weaken-#→#-identity b))
rename-identity (b `∙ a) = ≡.cong₂ _`∙_ (rename-identity b) (rename-identity a)



-- -------------------------------------------------------------------
-- Substitution
-- -------------------------------------------------------------------


-- Type-erased Substitution
_#→⊣_ : Rel ℕ Level.zero
m #→⊣ n = Fin m → n ⊣


-- weaken Type-erased Substitution to larger Context
weaken-#→⊣ : ∀ {m n} → m #→⊣ n → suc m #→⊣ suc n
weaken-#→⊣ 𝔰  zero   = ` zero
weaken-#→⊣ 𝔰 (suc x) = rename suc (𝔰 x)


-- apply Type-erased Substitution
substitute : ∀ {m n} → m #→⊣ n → m ⊣ → n ⊣
substitute 𝔰  `●      = `●
substitute 𝔰 (` x)    = 𝔰 x
substitute 𝔰 (`λ b)   = `λ substitute (weaken-#→⊣ 𝔰) b
substitute 𝔰 (b `∙ a) = substitute 𝔰 b `∙ substitute 𝔰 a


-- extend Type-erased Substitution to larger source Context
extend-#→⊣ : ∀ {m n} → m #→⊣ n → n ⊣ → suc m #→⊣ n
extend-#→⊣ 𝔰 a  zero   = a
extend-#→⊣ 𝔰 a (suc x) = 𝔰 x


-- Lemma. congruence over weakened Type-erased Substitution
weaken-#→⊣-cong : ∀ {m n} {𝔰 𝔰′ : m #→⊣ n} →
  (∀ x → 𝔰 x ≡ 𝔰′ x) →
  (x : Fin (suc m)) →
  weaken-#→⊣ 𝔰 x ≡ weaken-#→⊣ 𝔰′ x

weaken-#→⊣-cong eq  zero   = ≡.refl
weaken-#→⊣-cong eq (suc x) = ≡.cong (rename suc) (eq x)


-- Lemma. congruence over Type-erased Substitution
substitute-cong : ∀ {m n} {𝔰 𝔰′ : m #→⊣ n} →
  (∀ x → 𝔰 x ≡ 𝔰′ x) →
  (a : m ⊣) →
  substitute 𝔰 a ≡ substitute 𝔰′ a

substitute-cong eq  `●      = ≡.refl
substitute-cong eq (` x)    = eq x
substitute-cong eq (`λ a)   = ≡.cong `λ_ (substitute-cong (weaken-#→⊣-cong eq) a)
substitute-cong eq (b `∙ a) = ≡.cong₂ _`∙_ (substitute-cong eq b) (substitute-cong eq a)


-- Lemma. Type-erased substitution weakening preserves quoting
weaken-#→⊣-identity : ∀ {n} → (x : Fin (suc n)) → ` x ≡ weaken-#→⊣ `_ x
weaken-#→⊣-identity  zero   = ≡.refl
weaken-#→⊣-identity (suc x) = ≡.refl


-- apply single Type-erased Substitution
_[_] : ∀ {n} → suc n ⊣ → n ⊣ → n ⊣
b [ a ] = substitute (extend-#→⊣ `_ a) b


-- Lemma. Term-substitution of Type-erased Term
postulate
  erase-[] : ∀ {Φ} {Γ : Context Φ} {α β} (b : Γ , α ⊢ β) (a : Γ ⊢ α) →
    erase b [ erase a ] ≡
    erase (b ¡.[ a ])


-- Lemma. Type-erasure cancels out Type-substitution
postulate
  erase-[]♯ : ∀ {Φ} {Γ : Context Φ} {A β} (b : Γ ,♯ A ⊢ β) (α : Φ ♯.⊢⇓ A) →
    erase b ≡
    erase (b ¡.[ α ]♯)



-- -------------------------------------------------------------------
-- Value
-- -------------------------------------------------------------------


-- Type-erased Value
data _⇓ {n} : n ⊣ → Set where
  ●⇓ : `● ⇓
  λ⇓ : (b : suc n ⊣) → `λ b ⇓



-- -------------------------------------------------------------------
-- Reduction
-- -------------------------------------------------------------------


-- Type-erased reduction
data _⟶_ {n} : Rel (n ⊣) Level.zero where

  applicant : {b b′ a : n ⊣} →
    b ⟶ b′ →
    b `∙ a ⟶ b′ `∙ a

  argument : {b a a′ : n ⊣} →
    b ⇓ →
    a ⟶ a′ →
    b `∙ a ⟶ b `∙ a′

  apply : {b : suc n ⊣} {a : n ⊣} →
    a ⇓ →
    `λ b `∙ a ⟶ b [ a ]


-- Type-erase Value
erase-⇓ : ∀ {Φ α} {Γ : Context Φ} {a : Γ ⊢ α} → a ¡.⇓ → erase a ⇓
erase-⇓  ¡.●⇓        = ●⇓
erase-⇓ (¡.λ⇓    b)  = (λ⇓ ∘ erase) b
erase-⇓ (¡.Λ⇓    a⇓) = erase-⇓ a⇓
erase-⇓ (¡.fold⇓ a⇓) = erase-⇓ a⇓


-- Theorem. Type-erasure preserves reduction
erase-⟶ : ∀ {Φ α} {Γ : Context Φ} {a a′ : Γ ⊢ α} →
  a ¡.⟶ a′ →
  erase a ⟶ erase a′ ⊎ erase a ≡ erase a′

erase-⟶ (¡.applicant       {a = a} b⟶b′)         = map applicant
                                                           (≡.cong (_`∙ erase a )) (erase-⟶ b⟶b′)
erase-⟶ (¡.argument        {b = b} a⟶a′ b⇓)      = map (argument (erase-⇓ b⇓))
                                                           (≡.cong (erase b `∙_))  (erase-⟶ a⟶a′)
erase-⟶ (¡.function♯                       a⟶a′) = erase-⟶ a⟶a′
erase-⟶ (¡.applicant♯                      a⟶a′) = erase-⟶ a⟶a′
erase-⟶ (¡.unfold-argument                 a⟶a′) = erase-⟶ a⟶a′
erase-⟶ (¡.fold-argument                   a⟶a′) = erase-⟶ a⟶a′
erase-⟶ (¡.apply           {b = b} {a = a} a⇓)     = inj₁ (≡.subst (`λ erase b `∙ erase a ⟶_)
                                                                     (erase-[] b a)
                                                                     (apply (erase-⇓ a⇓)))
erase-⟶ (¡.apply♯          {b = b} {α = α})        = inj₂ (erase-[]♯ b α)
erase-⟶ ¡.unfold-fold                              = inj₂ ≡.refl


-- Theorem. Type-erased progress
progress-ø : ∀ {α : ø ♯.⊢⇓ `⋆} (a : ø ⊢ α) →
  erase a ⇓ ⊎
  ∃[ a′ ]
      ((a ¡.⟶ a′) ×
      ((erase a ⟶ erase a′) ⊎ (erase a ≡ erase a′)))
progress-ø a = map erase-⇓ (λ { (a′ & a⟶a′) → a′ & a⟶a′ & erase-⟶ a⟶a′ }) (¡.progress-ø a)



-- ===================================================================
-- Evaluation
-- ===================================================================
-- Evaluation via iterative applications of `progress`.


-- Type-erased multi-step reduction
data _⟶*_ {n} : Rel (n ⊣) Level.zero where

  refl : ∀ {a : n ⊣} →
    a ⟶* a

  chain : ∀ {a a′ a″ : n ⊣} →
    a  ⟶  a′ →
    a′ ⟶* a″ →
    a  ⟶* a″


-- Type-erasure preserves evaluation
erase-⟶* : ∀ {Φ} {α : Φ ♯.⊢⇓ `⋆} {Γ : Context Φ} {a a′ : Γ ⊢ α} →
  a ¡.⟶* a′ →
  erase a ⟶* erase a′
erase-⟶*  ¡.refl = refl
erase-⟶* (¡.chain {a = a} {a′ = a′} {a″ = a″} a⟶a′ a′⟶*a″) =
  Sum.[ (λ ea⟶ea′ → chain ea⟶ea′ (erase-⟶* a′⟶*a″))
      , (λ ea≡ea′ → ≡.subst (_⟶* erase a″) (≡.sym ea≡ea′) (erase-⟶* a′⟶*a″))
  ] (erase-⟶ a⟶a′)

