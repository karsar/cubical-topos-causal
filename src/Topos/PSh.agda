{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.PSh — presheaves over a regime base C (= objects of
-- the presheaf topos Set^Cᵒᵖ) and their natural transformations.
--
-- Contravariant: a morphism f : Hom x y restricts F₀ y → F₀ x.
-- `Nat≡` is the extensionality lemma: two natural transformations
-- are equal as soon as their components agree pointwise (the
-- naturality square is propositional because the codomain is a set).
-- This is the lemma that lets Topos.Rule1 assemble a pointwise
-- identity into an equality of internal morphisms.
-- ============================================================

module Topos.PSh where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt; isSetUnit)
open import Topos.Cat

record PSh {ℓo ℓh} (C : Precategory ℓo ℓh) (ℓ : Level)
       : Type (ℓ-suc (ℓ-max (ℓ-max ℓo ℓh) ℓ)) where
  open Precategory C
  field
    F₀      : Ob → Type ℓ
    F₁      : ∀ {x y} → Hom x y → F₀ y → F₀ x
    F-id    : ∀ {x} (a : F₀ x) → F₁ idn a ≡ a
    F-comp  : ∀ {x y z} (f : Hom x y) (g : Hom y z) (a : F₀ z)
            → F₁ (f ⋆ g) a ≡ F₁ f (F₁ g a)
    isSetF₀ : ∀ x → isSet (F₀ x)

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- naturality of a family of component maps
  IsNat : ∀ {ℓ ℓ'} (X : PSh C ℓ) (Y : PSh C ℓ')
        → (∀ c → F₀ X c → F₀ Y c) → Type (ℓ-max (ℓ-max ℓo ℓh) (ℓ-max ℓ ℓ'))
  IsNat X Y α = ∀ x y (f : Hom x y) (a : F₀ X y)
              → α x (F₁ X f a) ≡ F₁ Y f (α y a)

  -- a natural transformation X ⇒ Y
  Nat : ∀ {ℓ ℓ'} (X : PSh C ℓ) (Y : PSh C ℓ') → Type _
  Nat X Y = Σ[ α ∈ (∀ c → F₀ X c → F₀ Y c) ] IsNat X Y α

  -- the terminal presheaf, and internal global elements (sections)
  𝟙 : PSh C ℓ-zero
  𝟙 = record
    { F₀ = λ _ → Unit ; F₁ = λ _ _ → tt
    ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → isSetUnit }

  Section : ∀ {ℓ} → PSh C ℓ → Type (ℓ-max (ℓ-max ℓo ℓh) ℓ)
  Section Y = Nat 𝟙 Y

  -- product of presheaves (restriction componentwise)
  _×ᴾ_ : ∀ {ℓ ℓ'} → PSh C ℓ → PSh C ℓ' → PSh C (ℓ-max ℓ ℓ')
  X ×ᴾ Y = record
    { F₀ = λ c → F₀ X c × F₀ Y c
    ; F₁ = λ f p → (F₁ X f (fst p) , F₁ Y f (snd p))
    ; F-id = λ p → ΣPathP (F-id X (fst p) , F-id Y (snd p))
    ; F-comp = λ f g p → ΣPathP (F-comp X f g (fst p) , F-comp Y f g (snd p))
    ; isSetF₀ = λ c → isSet× (isSetF₀ X c) (isSetF₀ Y c) }

  isPropIsNat : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'}
                (α : ∀ c → F₀ X c → F₀ Y c) → isProp (IsNat X Y α)
  isPropIsNat {Y = Y} α =
    isPropΠ λ x → isPropΠ λ y → isPropΠ λ f → isPropΠ λ a → isSetF₀ Y x _ _

  -- extensionality: pointwise-equal components ⇒ equal natural transformations
  Nat≡ : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'} (n₁ n₂ : Nat X Y)
       → (∀ c a → fst n₁ c a ≡ fst n₂ c a) → n₁ ≡ n₂
  Nat≡ {X = X} {Y} n₁ n₂ h =
    ΣPathP (αp , isProp→PathP (λ i → isPropIsNat {X = X} {Y = Y} (αp i)) (snd n₁) (snd n₂))
    where
      αp : fst n₁ ≡ fst n₂
      αp = funExt λ c → funExt λ a → h c a
