{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Cat — the regime base category for directed topos
-- causal models (Stage 1).
--
-- A minimal (pre)category record. Objects are regimes /
-- contexts; morphisms are admissible regime maps. For Stage 1
-- a finite poset instance suffices, but we keep C abstract.
--
-- Composition is in DIAGRAMMATIC order:  f ⋆ g  is  "f then g".
-- This makes contravariant presheaf restriction read cleanly
-- in Topos.PSh.
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
