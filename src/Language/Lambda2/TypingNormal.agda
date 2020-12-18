import Level
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as ≡
  using (_≡_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat as Nat
import Data.Nat.Properties as NatProperties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Product as Product using (_×_; ∃-syntax; Σ-syntax; proj₁; proj₂) renaming (_,_ to _&_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe as Maybe using (Maybe; just; nothing)


open import Language.Lambda2.Kinding as ♯
  using
    ( `⋆ ; _`→_
    ; ø ; _,_
    ; head ; tail
    ; `⊤ ; `_ ; `Π_ ; `λ_ ; _`∙_ ; `μ_
    ; refl ; trans ; subst
    ; ↓_ )
    
open import Language.Lambda2.Typing as ⅋
  using ( `● ; `_ ; `λ_ ; _`∙_ )


module Language.Lambda2.TypingNormal where


infix 3 _≅[_]_
infix 4 _∋_ _⊢_ _⇓ _⟶_ _⟶*_
infix 5 _∋→∋⟨_⟩_ _∋→⊢⟨_⟩_
infixl 6 _,_

infixl 8 _`∙_ _`∙♯_
infixr 9 `λ_ `Λ_
infixr 11 `_ S_ S♯_
infix  12 _[_] _[_]♯



-- ===================================================================
-- Type Context
-- ===================================================================


-- Type Context
data Context : ♯.Context → Set where
  ø    : Context ø                                        -- empty Context   
  _,_  : ∀ {Φ} → Context Φ → Φ ♯.⊢⇓ `⋆ → Context  Φ       -- Normal Type in Context
  _,♯_ : ∀ {Φ} → Context Φ → ∀ A       → Context (Φ , A)  -- Kind in Context


length : ∀ {Φ} → Context Φ → ℕ
length  ø       = 0
length (Γ ,  _) = 1 + length Γ
length (Γ ,♯ _) = length Γ


-- Term Name
data _∋_ : ∀ {Φ} → Context Φ → Φ ♯.⊢⇓ `⋆ → Set where
  head  : ∀ {Φ Γ} {α   : Φ ♯.⊢⇓ `⋆}     →         Γ ,  α ∋ α
  tail  : ∀ {Φ Γ} {α β : Φ ♯.⊢⇓ `⋆}     → Γ ∋ β → Γ ,  α ∋ β
  tail♯ : ∀ {Φ Γ} {α   : Φ ♯.⊢⇓ `⋆} {X} → Γ ∋ α → Γ ,♯ X ∋ ♯.weaken-⊢⇓ α


-- prefixed abbreviations

Z : ∀ {Φ} {Γ : Context Φ} {α : Φ ♯.⊢⇓ `⋆} → Γ , α ∋ α
Z = head

S_ : ∀ {Φ} {Γ : Context Φ} → {α β : Φ ♯.⊢⇓ `⋆} → Γ ∋ β → Γ , α ∋ β
S_ = tail

S♯_ : ∀ {Φ} {Γ : Context Φ} {α : Φ ♯.⊢⇓ `⋆} {X} → Γ ∋ α → Γ ,♯ X ∋ ♯.weaken-⊢⇓ α
S♯_ = tail♯



-- ===================================================================
-- Term with Normal Type
-- ===================================================================


data _⊢_ {Φ} Γ : Φ ♯.⊢⇓ `⋆ → Set where

  -- unit
  `● :
    ------------------------------------------------
    Γ ⊢ ♯.↓ `⊤

  -- name
  `_ : ∀ {α} →
    Γ ∋ α →
    ------------------------------------------------
    Γ ⊢ α

  -- function
  `λ_ : ∀ {α β} →
    Γ , α ⊢ β →
    ------------------------------------------------
    Γ     ⊢ α `→ β

  -- application
  _`∙_ : ∀ {α β} →
    Γ ⊢ α `→ β →
    Γ ⊢ α →
    ------------------------------------------------
    Γ ⊢ β

  -- polymorphism function
  `Λ_ : ∀ {A β} →
    Γ ,♯ A ⊢ β →
    ------------------------------------------------
    Γ      ⊢ `Π β

  -- polymorphism application
  _`∙♯_ : ∀ {A β} →
                        Γ ⊢ `Π β →
    ------------------------------------------------
    ∀ (α : Φ ♯.⊢⇓ A) → Γ ⊢ β ♯.[ α ]⇓

  -- fixpoint fold
  `fold :
    ∀ α →
    Γ ⊢ α ♯.[ `μ α ]⇓ →
    ------------------------------------------------
    Γ ⊢ `μ α
    
  -- fixpoint unfold
  `unfold :
    ∀ {α} →
    Γ ⊢ `μ α →
    ------------------------------------------------
    Γ ⊢ α ♯.[ `μ α ]⇓



-- ===================================================================
-- Soundness of Typing
-- ===================================================================


-- embed Normal Context to unnormalized Context
embed-Context : ∀ {Φ} → Context Φ → ⅋.Context Φ
embed-Context  ø       = ⅋.ø
embed-Context (Γ ,♯ A) = embed-Context Γ ⅋.,♯ A
embed-Context (Γ ,  α) = embed-Context Γ ⅋., ♯.embed-⊢⇓ α


-- embed Normal Type Name to unnormalized Context
embed-TypeName : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} →
  Γ                 ∋ α →
  embed-Context Γ ⅋.∋ ♯.embed-⊢⇓ α

embed-TypeName  head             = ⅋.head
embed-TypeName (tail ξ)          = ⅋.tail (embed-TypeName ξ)
embed-TypeName (tail♯ {α = α} ξ) = ⅋.cast-∋ (≡.sym (♯.rename-embed-⊢⇓ ♯.tail α)) (⅋.tail♯ (embed-TypeName ξ))


-- embed Normal substitution to unnormalized substitution
embed-[] : ∀ {Φ A} (α : Φ ♯.⊢⇓ A) (β : Φ , A ♯.⊢⇓ `⋆) →
  ♯.embed-⊢⇓  β ♯.[ ♯.embed-⊢⇓ α ] ♯.≅ₜ
  ♯.embed-⊢⇓ (β ♯.[ α ]⇓)

embed-[] α β =
  ≡.subst (♯.embed-⊢⇓ β ♯.[ ♯.embed-⊢⇓ α ] ♯.≅ₜ_)
    (≡.cong ♯.embed-⊢⇓
      (≡.trans (≡.trans (♯.substitute-evaluate-≅ₛ (♯.embed-⊢⇓ β) ♯.id-≅ₑ (♯.extend-∋→⊢ `_ (♯.embed-⊢⇓ α)))
                 (♯.extend-evaluate-id-≅ₛ
                   (λ { head → ♯.extend-evaluate-id-≅ₛ ♯.id-≅ₑ (♯.embed-⊢⇓ α) ; (tail α) → ♯.reflect-≅ₛ (≡.refl {x = ` α}) }) (♯.embed-⊢⇓ β)))
      (≡.sym (♯.substitute-evaluate-≅ₛ (♯.embed-⊢⇓ β) ♯.id-≅ₑ (♯.embed-⊢⇓ ∘ ♯.extend-∋→⊢⇓ (↓_ ∘ `_) α)))))
    (♯.soundness (♯.embed-⊢⇓ β ♯.[ ♯.embed-⊢⇓ α ]))


-- embed Normal fixpoint to unnormalized fixpoint
embed-μ : ∀ {Γ} (α : Γ ♯., `⋆ ♯.⊢⇓ `⋆) →
  ♯.embed-⊢⇓ (α ♯.[ `μ α            ]⇓) ♯.≅ₜ
  ♯.embed-⊢⇓  α ♯.[ `μ ♯.embed-⊢⇓ α ]

embed-μ α =
  ≡.subst (♯._≅ₜ ♯.embed-⊢⇓ α ♯.[ `μ ♯.embed-⊢⇓ α ])
    (≡.cong ♯.embed-⊢⇓
      (≡.trans (♯.substitute-evaluate-≅ₛ (♯.embed-⊢⇓ α) ♯.id-≅ₑ (♯.extend-∋→⊢ `_ (`μ ♯.embed-⊢⇓ α)))
        (≡.trans (♯.extend-evaluate-id-≅ₛ (λ { head → ≡.refl ; (tail α) → ♯.id-≅ₑ α }) (♯.embed-⊢⇓ α))
          (≡.sym (♯.substitute-evaluate-≅ₛ (♯.embed-⊢⇓ α) ♯.id-≅ₑ (♯.embed-⊢⇓ ∘ (♯.extend-∋→⊢⇓ (↓_ ∘ `_) (`μ α))))))))
    (♯.sym (♯.soundness (♯.embed-⊢⇓ α ♯.[ `μ ♯.embed-⊢⇓ α ])))


-- embed Normal Type to unnormalized Type
embed-Type : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} →
  Γ ⊢ α →
  embed-Context Γ ⅋.⊢ ♯.embed-⊢⇓ α
embed-Type  `●                 = ⅋.`●
embed-Type (` x)               = ⅋.` embed-TypeName x
embed-Type (`λ b)              = ⅋.`λ embed-Type b
embed-Type (b `∙ a)            = (embed-Type b) ⅋.`∙ (embed-Type a)
embed-Type (`Λ a)              = ⅋.`Λ embed-Type a
embed-Type (_`∙♯_ {β = β} b α) = ⅋.`cast (embed-[] α β) (embed-Type b ⅋.`∙♯ ♯.embed-⊢⇓ α)
embed-Type (`fold β b)         = ⅋.`fold (♯.embed-⊢⇓ β) (⅋.`cast (embed-μ β) (embed-Type b))
embed-Type (`unfold {α = α} a) = ⅋.`cast (♯.sym (embed-μ α)) (⅋.`unfold (embed-Type a))


soundness : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} →
  Γ ⊢ α →
  embed-Context Γ ⅋.⊢ ♯.embed-⊢⇓ α
soundness = embed-Type



-- ===================================================================
-- Completeness of Typing
-- ===================================================================


-- cast Term Names with syntactically equivalent Types
cast-∋ : ∀ {Φ Γ} {α α′ : Φ ♯.⊢⇓ `⋆} →
  α ≡ α′ →
  Γ ∋ α →
  Γ ∋ α′
cast-∋ ≡.refl a = a

-- cast Terms with syntactically equivalent Types
cast-⊢ : ∀ {Φ Γ} {α α′ : Φ ♯.⊢⇓ `⋆} →
  α ≡ α′ →
  Γ ⊢ α →
  Γ ⊢ α′
cast-⊢ ≡.refl a = a


normalize-Context : ∀ {Φ} → ⅋.Context Φ → Context Φ
normalize-Context  ⅋.ø       = ø
normalize-Context (Γ ⅋., ξ)  = normalize-Context Γ , ♯.normalize ξ 
normalize-Context (Γ ⅋.,♯ A) = normalize-Context Γ ,♯ A


-- Lemma. commute Normal Renaming and normalization
rename-normalize : ∀ {Φ Ψ A} {𝔖 : Φ ♯.∋→∋ Ψ} {α : Φ ♯.⊢ A} →
  ♯.rename-⊢⇓ 𝔖 (♯.normalize α) ≡
  ♯.normalize (♯.rename 𝔖 α)

rename-normalize {_} {_} {_} {𝔖} {α} =
  ≡.trans
    (♯.rename-reify 𝔖 (♯.extend-evaluate-id-≅ₛ ♯.id-≅ₑ α))
    (♯.reify-≅ₛ (♯.trans-≅ₛ
      (♯.rename-⊨-evaluate α ♯.id-≅ₑ 𝔖)
      (♯.trans-≅ₛ
        (♯.extend-evaluate-id-≅ₛ (♯.rename-⊨-reflect 𝔖 ∘ `_) α)
        (♯.sym-≅ₛ (♯.rename-evaluate-≅ₛ α ♯.id-≅ₑ 𝔖)))))


normalize-TypeName : ∀ {Φ Γ} → {α : Φ ♯.⊢ `⋆} → Γ ⅋.∋ α → normalize-Context Γ ∋ ♯.normalize α
normalize-TypeName          ⅋.head                     = head
normalize-TypeName         (⅋.tail          ξ)         = tail (normalize-TypeName ξ)
normalize-TypeName {Γ , B} (⅋.tail♯ {α = α} {B = B} ξ) = cast-∋ (rename-normalize {𝔖 = tail} {α = α}) (tail♯ (normalize-TypeName ξ))


-- Lemma.
postulate
  normalize-Π : ∀ {Φ A} (β : Φ , A ♯.⊢ `⋆) →
    `Π ♯.normalize β ≡ ♯.normalize (`Π β)


-- Lemma.
postulate
  normalize-μ : ∀ {Φ} (β : Φ , `⋆ ♯.⊢ `⋆) →
    `μ ♯.normalize β ≡ ♯.normalize (`μ β)


-- Lemma.
postulate
  normalize-[μ] : ∀ {Φ} (β : Φ , `⋆ ♯.⊢ `⋆) →
    ♯.normalize (β ♯.[ `μ β ]) ≡ ♯.normalize β ♯.[ `μ ♯.normalize β ]⇓


-- Lemma.
postulate
  normalize-[] : ∀ {Φ A} (α : Φ ♯.⊢⇓ A) (β : Φ , A ♯.⊢⇓ `⋆) →
    β ♯.[ α ]⇓ ≡ ♯.normalize (♯.substitute (♯.extend-∋→⊢ `_ (♯.embed-⊢⇓ α)) (♯.embed-⊢⇓ β))


-- Lemma.
postulate
  evaluate-[normalize] : ∀ {Φ A} (α : Φ ♯.⊢ A) (β : Φ , A ♯.⊢ `⋆) →
    ♯.evaluate β (♯.weakenₑ ♯.εₑ) ♯.[ ♯.normalize α ]⇓ ≡ ♯.normalize (♯.substitute (♯.extend-∋→⊢ `_ α) β)


normalize-Type : ∀ {Φ Γ} {α : Φ ♯.⊢ `⋆} →
  Γ ⅋.⊢ α →
  normalize-Context Γ ⊢ ♯.normalize α
normalize-Type  ⅋.`●                 = `●
normalize-Type (⅋.` x)               = ` normalize-TypeName x
normalize-Type (⅋.`λ b)              = `λ normalize-Type b
normalize-Type (b ⅋.`∙ a)            = normalize-Type b `∙ normalize-Type a
normalize-Type (⅋.`Λ_ {A} {B} b)     = cast-⊢ (normalize-Π B)
                                              (`Λ normalize-Type b)
normalize-Type (⅋._`∙♯_ {A} {β} b α) = cast-⊢ (evaluate-[normalize] α β)
                                              (normalize-Type b `∙♯ ♯.normalize α)
normalize-Type (⅋.`fold α a)         = admitted where postulate admitted : normalize-Context _ ⊢ ♯.normalize (`μ α)
                                       -- cast-⊢ (normalize-μ α) -- (normalize-μ α)
                                       --   (`fold (♯.normalize α) {!normalize-Type a !})
normalize-Type (⅋.`unfold {α = α} a) = admitted where postulate admitted : normalize-Context _ ⊢ ♯.normalize (α ♯.[ `μ α ])
                                       -- cast-⊢ (≡.sym (normalize-[μ] α))
                                       --   (`unfold (cast-⊢ (≡.sym (normalize-[μ] {!α!}))
                                       --     (normalize-Type a)))
normalize-Type (⅋.`cast α≅α′ a)      = cast-⊢ (♯.completeness α≅α′)
                                              (normalize-Type a)



-- ===================================================================
-- Operational Semantics
-- ===================================================================
-- given by call-by-value small-step reduction relation


-- Term Renaming
_∋→∋⟨_⟩_ : ∀ {Φ Ψ} → Context Φ → Φ ♯.∋→∋ Ψ → Context Ψ → Set
Γ ∋→∋⟨ ℜ ⟩ Δ = ∀ {α : _ ♯.⊢⇓ `⋆} →
  Γ ∋ α →
  Δ ∋ ♯.rename-⊢⇓ ℜ α


-- weaken Term Renaming to Type-larger Context
weaken-∋→∋ : ∀ {Φ Ψ Γ Δ} {ℜ : Φ ♯.∋→∋ Ψ} →
                     Γ      ∋→∋⟨ ℜ ⟩ Δ →
  {β : Φ ♯.⊢⇓ `⋆} → (Γ , β) ∋→∋⟨ ℜ ⟩ Δ , ♯.rename-⊢⇓ ℜ β
weaken-∋→∋ 𝔯  head    = head
weaken-∋→∋ 𝔯 (tail x) = tail (𝔯 x)


-- weaken Term Renaming to Kind-larger Context
weaken-∋→∋♯ : ∀ {Φ Ψ Γ Δ} {ℜ : Φ ♯.∋→∋ Ψ} →
           Γ      ∋→∋⟨ ℜ            ⟩ Δ →
  (∀ {A} → Γ ,♯ A ∋→∋⟨ ♯.weaken-∋→∋ ℜ ⟩ Δ ,♯ A)
weaken-∋→∋♯ 𝔯 (tail♯ x) = cast-∋ (≡.trans (≡.sym (♯.rename-⊢⇓-compose _))
                               (♯.rename-⊢⇓-compose _)) (tail♯ (𝔯 x))



-- -------------------------------------------------------------------
-- Substitution
-- -------------------------------------------------------------------


-- apply Term Renaming
rename : ∀ {Φ Ψ Γ Δ} {ℜ : Φ ♯.∋→∋ Ψ} → Γ ∋→∋⟨ ℜ ⟩ Δ → (∀ {α : Φ ♯.⊢⇓ `⋆} → Γ ⊢ α → Δ ⊢ ♯.rename-⊢⇓ ℜ α)
rename 𝔯  `●                 = `●
rename 𝔯 (` x)               = ` 𝔯 x
rename 𝔯 (`λ a)              = `λ rename (weaken-∋→∋ 𝔯) a 
rename 𝔯 (b `∙ a)            = rename 𝔯 b `∙ rename 𝔯 a
rename 𝔯 (`Λ a)              = `Λ rename (weaken-∋→∋♯ 𝔯) a
rename 𝔯 (_`∙♯_ {β = β} b α) = cast-⊢ (≡.sym (♯.rename-[]⇓ _ β α)) (rename 𝔯 b `∙♯ ♯.rename-⊢⇓ _ α)
rename 𝔯 (`fold α a)         = `fold _ (cast-⊢ (♯.rename-[]⇓ _ α (`μ α)) (rename 𝔯 a))
rename 𝔯 (`unfold {α = α} a) = cast-⊢ (≡.sym (♯.rename-[]⇓ _ α (`μ α) )) (`unfold (rename 𝔯 a))


-- weaken Term to Type-larger Context
weaken : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} {β : Φ ♯.⊢⇓ `⋆} →
  Γ     ⊢ α →
  Γ , β ⊢ α
weaken {α = α} a = cast-⊢ (♯.rename-⊢⇓-identity α) (rename (cast-∋ (≡.sym (♯.rename-⊢⇓-identity _)) ∘ tail) a)


-- weaken Term to Kind-larger Context
weaken♯ : ∀ {Φ Γ} {α : Φ ♯.⊢⇓ `⋆} {A} →
  Γ ⊢ α →
  Γ ,♯ A ⊢ ♯.weaken-⊢⇓ α
weaken♯ a = rename tail♯ a


-- Term Substitution
_∋→⊢⟨_⟩_ : ∀ {Φ Ψ} (Γ : Context Φ) (𝔖 : Φ ♯.∋→⊢⇓ Ψ) (Δ : Context Ψ) → Set
Γ ∋→⊢⟨ 𝔖 ⟩ Δ = ∀ {α : _ ♯.⊢⇓ `⋆} → Γ ∋ α → Δ ⊢ ♯.substitute-⊢⇓ 𝔖 α


-- weaken Term Substitution to Type-larger Context
weaken-∋→⊢ : ∀ {Φ Ψ Γ Δ} (𝔖 : Φ ♯.∋→⊢⇓ Ψ) →
                      Γ     ∋→⊢⟨ 𝔖 ⟩ Δ →
  ∀ {β : _ ♯.⊢⇓ `⋆} → Γ , β ∋→⊢⟨ 𝔖 ⟩ Δ , ♯.substitute-⊢⇓ 𝔖 β

weaken-∋→⊢ _ 𝔰  head    = ` head
weaken-∋→⊢ _ 𝔰 (tail x) = weaken (𝔰 x)


-- weaken Term Substitution to Kind-larger Context
weaken-∋→⊢♯ : ∀ {Φ Ψ Γ Δ} (𝔖 : Φ ♯.∋→⊢⇓ Ψ) →
          Γ      ∋→⊢⟨ 𝔖 ⟩             Δ →
  ∀ {A} → Γ ,♯ A ∋→⊢⟨ ♯.weaken-∋→⊢⇓ 𝔖 ⟩ Δ ,♯ A

weaken-∋→⊢♯ 𝔖 𝔰 (tail♯ {α = α} x) = cast-⊢ (♯.weaken-⊢⇓-substitute-⊢⇓ 𝔖 α) (weaken♯ (𝔰 x))


-- apply Term Substitution
substitute : ∀ {Φ Ψ Γ Δ} (𝔖 : Φ ♯.∋→⊢⇓ Ψ) →
  Γ ∋→⊢⟨ 𝔖 ⟩ Δ →
  (∀ {α : Φ ♯.⊢⇓ `⋆} →
    Γ ⊢ α →
    Δ ⊢ ♯.substitute-⊢⇓ 𝔖 α)

substitute 𝔖 𝔰  `●                 = `●
substitute 𝔖 𝔰 (` x)               = 𝔰 x
substitute 𝔖 𝔰 (`λ a)              = `λ substitute 𝔖 (weaken-∋→⊢ 𝔖 𝔰) a
substitute 𝔖 𝔰 (b `∙ a)            = substitute 𝔖 𝔰 b `∙ substitute 𝔖 𝔰 a
substitute 𝔖 𝔰 (`Λ_ {β = β} a)     = `Λ cast-⊢ (♯.substitute-⊢⇓-weaken-∋→⊢⇓ 𝔖 β) (substitute (♯.weaken-∋→⊢⇓ 𝔖) (weaken-∋→⊢♯ 𝔖 𝔰) a) 
substitute 𝔖 𝔰 (_`∙♯_ {β = β} a α) = cast-⊢ (≡.sym (♯.substitute-⊢⇓-[]⇓ 𝔖 α β))
                                      (substitute 𝔖 𝔰 a `∙♯ ♯.substitute-⊢⇓ 𝔖 α)
substitute 𝔖 𝔰 (`fold α a)         = `fold _ (cast-⊢ (♯.substitute-⊢⇓-[]⇓ 𝔖 (`μ α) α) (substitute 𝔖 𝔰 a))
substitute 𝔖 𝔰 (`unfold {α = α} a)         = cast-⊢ (≡.sym (♯.substitute-⊢⇓-[]⇓ 𝔖 (`μ α) α)) (`unfold (substitute 𝔖 𝔰 a))


-- extend Term Substitution to Type-larger source Context
extend : ∀ {Φ Ψ Γ Δ} →
  (𝔖 : ∀ {A} → Φ ♯.∋ A → Ψ ♯.⊢⇓ A) →
  (∀ {α : Φ ♯.⊢⇓ `⋆} →               Γ    ∋ α → Δ ⊢ ♯.substitute-⊢⇓ 𝔖 α) →
  (∀ {α : Φ ♯.⊢⇓ `⋆} →
    (a : Δ ⊢ ♯.substitute-⊢⇓ 𝔖 α) →
    (∀ {β : Φ ♯.⊢⇓ `⋆} →
                                     Γ , α ∋ β → Δ ⊢ ♯.substitute-⊢⇓ 𝔖 β))

extend 𝔖 𝔰 a  head    = a
extend 𝔖 𝔰 a (tail x) = 𝔰 x


-- apply single Term Substitution by a Term
_[_] : ∀ {Φ Γ} {α β : Φ ♯.⊢⇓ `⋆} →
  Γ , α ⊢ β →
  Γ     ⊢ α →
  Γ     ⊢ β
_[_] {α = α} {β} b a = cast-⊢ (♯.substitute-⊢⇓-identity β)
                       (substitute (↓_ ∘ `_)
                                   (extend (↓_ ∘ `_)
                                           (cast-⊢ (≡.sym (♯.substitute-⊢⇓-identity _)) ∘ `_)
                                           (cast-⊢ (≡.sym (♯.substitute-⊢⇓-identity α)) a))
                                    b)


-- apply single Term Substitution by a Type
_[_]♯ : ∀ {Φ Γ A} {β : Φ , A ♯.⊢⇓ `⋆} →
                   Γ ,♯ A ⊢ β →
  (α : Φ ♯.⊢⇓ A) → Γ      ⊢ β ♯.[ α ]⇓
b [ α ]♯ = substitute (♯.extend-∋→⊢⇓ (↓_ ∘ `_) α) lem b
  where
    lem : ∀ {Φ Γ A} {β : Φ , A ♯.⊢⇓ `⋆} {α : Φ ♯.⊢⇓ A} →
      Γ ,♯ A ∋ β →
      Γ      ⊢ ♯.substitute-⊢⇓ (♯.extend-∋→⊢⇓ (↓_ ∘ `_) α) β
    lem (tail♯ x) = cast-⊢ (♯.weaken-⊢⇓-[] _ _) (` x)



-- -------------------------------------------------------------------
-- Reduction
-- -------------------------------------------------------------------

-- Term Value
data _⇓ {Φ Γ} : {α : Φ ♯.⊢⇓ `⋆} → Γ ⊢ α → Set where
  ●⇓    :                                         `● ⇓
  λ⇓    : ∀ {α β} (b : Γ ,  α ⊢ β)              → `λ b ⇓
  Λ⇓    : ∀ {A β} {b : Γ ,♯ A ⊢ β}        → b ⇓ → `Λ b ⇓
  fold⇓ : ∀ {α  } {a : Γ ⊢ α ♯.[ `μ α ]⇓} → a ⇓ → `fold α a ⇓


-- Relation. Term Reduction
data _⟶_ {Φ} {Γ} : {α : Φ ♯.⊢⇓ `⋆} → Rel (Γ ⊢ α) Level.zero where

  applicant : ∀ {α β} {b b′ : Γ ⊢ α `→ β} {a : Γ ⊢ α} →
    b ⟶ b′ →
    ------------------------------------------------
    b `∙ a ⟶ b′ `∙ a

  argument : ∀ {α β} {b : Γ ⊢ α `→ β} {a a′ : Γ ⊢ α} →
    a ⟶ a′ →
    b ⇓ →
    ------------------------------------------------
    b `∙ a ⟶ b `∙ a′

  function♯ : ∀ {A β} {a a′ : Γ ,♯ A ⊢ β} →
    a ⟶ a′ →
    ------------------------------------------------
    `Λ a ⟶ `Λ a′

  applicant♯ : ∀ {A β} {b b′ : Γ ⊢ `Π β} {α : Φ ♯.⊢⇓ A} →
    b ⟶ b′ →
    ------------------------------------------------
    b `∙♯ α ⟶ b′ `∙♯ α

  unfold-argument : ∀ {α} {a a′ : Γ ⊢ `μ α} →
    a ⟶ a′ →
    ------------------------------------------------
    `unfold a ⟶ `unfold a′

  fold-argument : ∀ {α : Φ , `⋆ ♯.⊢⇓ `⋆} {a a′ : Γ ⊢ α ♯.[ `μ α ]⇓} →
    a ⟶ a′ →
    ------------------------------------------------
    `fold α a ⟶ `fold α a′

  apply : ∀ {α β} {b : Γ , α ⊢ β} {a : Γ ⊢ α} →
    a ⇓ →
    ------------------------------------------------
    `λ b `∙ a ⟶ b [ a ]

  apply♯ : ∀ {A β} {b : Γ ,♯ A ⊢ β} {α : Φ ♯.⊢⇓ A} →
    ------------------------------------------------
    `Λ b `∙♯ α ⟶ b [ α ]♯

  unfold-fold : ∀ {α} {a : Γ ⊢ α ♯.[ `μ α ]⇓} →
    `unfold (`fold α a) ⟶ a



-- -------------------------------------------------------------------
-- Preservation
-- -------------------------------------------------------------------
-- Preservation follows trivially from intrinsic typing


-- -------------------------------------------------------------------
-- Progress
-- -------------------------------------------------------------------
-- Progress: reduction does not get "stuck"


-- Predicate. Context contains no Type Names (may contains Kind Names)
NameFree : ∀ {Φ} → Context Φ → Set
NameFree  ø       = ⊤
NameFree (Γ ,  α) = ⊥
NameFree (Γ ,♯ A) = NameFree Γ


-- Lemma. if a name is in ``Γ``, then ``Γ`` is not ``NameFree``.
¬-NameFree-∋ : ∀ {Φ Γ} → NameFree Γ → {α : Φ ♯.⊢⇓ `⋆} → ¬ Γ ∋ α
¬-NameFree-∋ NF (tail♯ x) = ¬-NameFree-∋ NF x


-- Theorem. A Term either is a value or reduces
progress : ∀ {Φ} {Γ} → NameFree Γ → ∀ {α : Φ ♯.⊢⇓ `⋆} (a : Γ ⊢ α) →
  a ⇓  ⊎  ∃[ a′ ] (a ⟶ a′)

progress NF  `● = inj₁ ●⇓

progress NF (` x) = ⊥-elim (¬-NameFree-∋ NF x)

progress NF (`λ b) = inj₁ (λ⇓ b)

progress NF (b `∙ a)  with progress NF b      | progress NF a
progress NF (`λ .b `∙ a) | inj₁ (λ⇓ b)        | inj₁ a⇓            = inj₂ (b [ a ] & apply a⇓)
{-# CATCHALL #-}
progress NF (b `∙ a)     | inj₁ b⇓            | inj₂ (a′ & a⟶a′) = inj₂ (b `∙ a′ & argument a⟶a′ b⇓)
progress NF (b `∙ a)     | inj₂ (b′ & b⟶b′) | _                  = inj₂ (b′ `∙ a & applicant b⟶b′)

progress NF (`Λ b) with progress NF b
progress NF (`Λ b) | inj₁ b⇓            = inj₁ (Λ⇓ b⇓)
progress NF (`Λ b) | inj₂ (b′ & b⟶b′) = inj₂ (`Λ b′ & function♯ b⟶b′)

progress NF (b `∙♯ α) with progress NF b
progress {Φ} {Γ} NF (_`∙♯_ {β = β} b α)    | inj₁ b⇓            = admitted where postulate admitted : b `∙♯ α ⇓ ⊎ Product.Σ (Γ ⊢ ♯.evaluate (♯.substitute (λ x → ♯.embed-⊢⇓ (♯.extend-∋→⊢⇓ (λ x₁ → ↓ ` x₁) α x)) (♯.embed-⊢⇓ β)) (λ x → ♯.reflect (` x))) (_⟶_ (b `∙♯ α))
-- progress NF (_`∙♯_ (`Λ b) α) | inj₁ b⇓ = {!!}
progress NF (b `∙♯ α)        | inj₂ (b′ & b⟶b′) = inj₂ (b′ `∙♯ α & applicant♯ b⟶b′)


progress NF (`fold α a) with progress NF a
progress NF (`fold α a)    | inj₁ a⇓            = inj₁ (fold⇓ a⇓)
progress NF (`fold α a)    | inj₂ (a′ & a⟶a′) = inj₂ (`fold α a′ & fold-argument a⟶a′)

progress NF (`unfold a) with progress NF a
progress {Φ} {Γ} NF (`unfold {α = α} a)    | inj₁ a⇓            = admitted where postulate admitted : `unfold a ⇓ ⊎ Product.Σ (Γ ⊢ ♯.evaluate (♯.substitute (λ x → ♯.embed-⊢⇓ (♯.extend-∋→⊢⇓ (λ x₁ → ↓ ` x₁) (`μ α) x)) (♯.embed-⊢⇓ α)) (λ x → ♯.reflect (` x))) (_⟶_ (`unfold a))

progress NF (`unfold a)    | inj₂ (a′ & a⟶a′) = inj₂ (`unfold a′ & unfold-argument a⟶a′)


-- Corrolarry. progress in an empty Context
progress-ø : ∀ {A} (a : ø ⊢ A) →
  a ⇓  ⊎  ∃[ a′ ] (a ⟶ a′)
progress-ø = progress tt



-- ===================================================================
-- Evaluation
-- ===================================================================
-- Evaluation via iterative applications of `progress`.


-- Relation. multi-step reduction
data _⟶*_ {Φ Γ} : {α : Φ ♯.⊢⇓ `⋆} → Rel (Γ ⊢ α) Level.zero where

  refl : ∀ {α} {a : Γ ⊢ α} →
    a ⟶* a

  chain : ∀ {α} {a a′ a″ : Γ ⊢ α} →
    a  ⟶  a′ →
    a′ ⟶* a″ →
    a  ⟶* a″


-- apply at least ``steps`` number of reduction, yeilding the combined reductions applied and the resulting value if it was reached
evaluate : ∀ {α : ø ♯.⊢⇓ `⋆} (steps : ℕ) (a : ø ⊢ α) →
  ∃[ a′ ] ((a ⟶* a′) × Maybe (a′ ⇓))

evaluate  zero     a = a & refl & nothing 
evaluate (suc steps) a with progress-ø a
evaluate (suc steps) a | inj₁ a⇓ = a & refl & just a⇓
evaluate (suc steps) a | inj₂ (a′ & a⟶*a′) with evaluate steps a′
evaluate (suc steps) a | inj₂ (a′ & a⟶*a′) | a″ & a′⟶*a″ & ma″⇓ = a″ & chain a⟶*a′ a′⟶*a″ & ma″⇓


-- Relation. equal results after ``n`` reduction steps
_≅[_]_ : ∀ {α : ø ♯.⊢⇓ `⋆} → (ø ⊢ α) → ℕ → (ø ⊢ α) → Set
a ≅[ steps ] a′ = proj₁ (evaluate steps a) ≡ proj₁ (evaluate steps a′)


-- ===================================================================
-- Examples
-- ===================================================================


module ChurchNumerals where

  `Chℕ : ∀ {Φ} → Φ ♯.⊢⇓ `⋆
  `Chℕ = `Π ↓ ` ♯.Z `→ (↓ ` ♯.Z `→ ↓ ` ♯.Z) `→ ↓ ` ♯.Z
  
  `zero : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ
  `zero = `Λ `λ `λ ` S Z
  
  `suc : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ `→ `Chℕ
  `suc = `λ `Λ `λ `λ (` Z `∙ ((` S S S♯ Z) `∙♯ ↓ ` ♯.Z `∙ ` S Z `∙ ` Z))
  
  `1 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ
  `1 = `suc `∙ `zero
  
  `2 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ
  `2 = `suc `∙ `1

  `1+1 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ
  `1+1 = (`2 `∙♯ `Chℕ) `∙ `1 `∙ `suc

  -- _ : `2 ≅[ 100 ] `1+1
  -- _ = ≡.refl

  `4 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ
  `4 = `suc `∙ (`suc `∙ (`suc `∙ `zero))

  `2+2 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Chℕ
  `2+2 = (`2 `∙♯ `Chℕ) `∙ `2 `∙ `suc
  


module ScottNumerals where

  `Scℕ : ∀ {Φ} → Φ ♯.⊢⇓ `⋆
  `Scℕ = α ♯.[ `μ α ]⇓ where α = `Π ↓ ` ♯.Z `→ (↓ ` ♯.S ♯.Z `→ ↓ ` ♯.Z) `→ ↓ ` ♯.Z

  `zero : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Scℕ
  `zero = `Λ `λ `λ ` S Z

  `suc : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Scℕ `→ `Scℕ
  `suc = `λ `Λ `λ `λ (` Z `∙ `fold _ (` S S S♯ Z))

  `1 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Scℕ
  `1 = `suc `∙ `zero

  `2 : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Scℕ
  `2 = `suc `∙ `1

  -- `case : ∀ {Φ} {Γ : Context Φ} → Γ ⊢ `Scℕ `→ (`Π ↓ ` ♯.Z `→ (`Scℕ `→ ↓ ` ♯.Z) `→ ↓ ` ♯.Z)
  -- `case = `λ `Λ `λ `λ
  --   ((` S S S♯ Z) `∙♯ (↓ ` ♯.Z) `∙ (` S Z) `∙ (`λ ` S Z `∙ `unfold (` Z)))
