{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Cat — the regime base category for directed topos
-- causal models (Stage 1).
--
-- A record for a precategory.  An object is a regime, that is,
-- a context in which the causal model is read.  A morphism is
-- an admissible map between regimes.  Stage 1 needs only a
-- finite poset instance.  We keep C abstract, so that later
-- stages can use another base.
--
-- Composition is written in diagrammatic order.  So  f ⋆ g  is
-- "f then g".  Topos.PSh restricts presheaves contravariantly.
-- In this order the restriction law reads
-- F₁ (f ⋆ g) a ≡ F₁ f (F₁ g a), with f and g in the same order
-- on both sides.
-- ============================================================

module Topos.Cat where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude

record Precategory (ℓo ℓh : Level) : Type (ℓ-suc (ℓ-max ℓo ℓh)) where
  field
    Ob      : Type ℓo
    Hom     : Ob → Ob → Type ℓh
    idn     : ∀ {x} → Hom x x
    _⋆_     : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    ⋆-idL   : ∀ {x y} (f : Hom x y) → (idn ⋆ f) ≡ f
    ⋆-idR   : ∀ {x y} (f : Hom x y) → (f ⋆ idn) ≡ f
    ⋆-assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
            → ((f ⋆ g) ⋆ h) ≡ (f ⋆ (g ⋆ h))
    isSetHom : ∀ {x y} → isSet (Hom x y)

  infixr 9 _⋆_
