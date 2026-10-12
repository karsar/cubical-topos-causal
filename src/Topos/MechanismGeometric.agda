{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MechanismGeometric: admissibility restricts along an
-- abstraction.
--
-- A base functor F abstracts a fine site C to a coarse site D.
-- Take a coarse mechanism m at the image App₀ c, and suppose m is
-- admissible: at every arrow into App₀ c and every parent value,
-- m returns the point mass at x₀.
--
-- Then m is also admissible when we test it only at the images
-- App₁ g of fine arrows g into c.  These images are among the
-- arrows the coarse witness already covers.  So the proof is an
-- instantiation of that witness, and it needs no condition on F.
--
-- The scope is narrow.  This is preservation in one direction.
-- We do not identify the pulled-back exponential with the
-- exponential of the pulled-back objects.  We also do not prove
-- that quantification over mechanisms transfers.  The theorem of
-- Topos.AbstractionTiers about ⇒ does not give that result.
--
-- Results:
--   pullMech        a coarse mechanism, read at fine contexts.
--   Adm-pullback    admissibility holds at every image arrow.
-- ============================================================

module Topos.MechanismGeometric where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isPropΠ)
open import Cubical.Data.Sigma using (_,_; fst; snd)

open import FDist-Convex using (pure; trunc)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.Exponential
open import Topos.BaseChange
open import Topos.MechanismObject using (Mech; Adm; pt)

module _ {ℓ} {C D : Precategory ℓ ℓ} (F : BaseFunctor C D)
         (Par Val : PSh D ℓ) (x₀ : Section {C = D} Val) where
  private
    module Cc = Precategory C
    module Dc = Precategory D
  open BaseFunctor F
  open PSh

  pullMech : (c : Cc.Ob) → F₀ (Mech Par Val x₀) (App₀ c)
           → (d : Dc.Ob) → Dc.Hom d (App₀ c) → F₀ Par d → F₀ (Dist_E {C = D} Val) d
  pullMech c m = fst m

  Adm-pullback : (c : Cc.Ob) (m : F₀ (Mech Par Val x₀) (App₀ c))
               → fst (Adm Par Val x₀ (App₀ c) m)
               → (d : Cc.Ob) (g : Cc.Hom d c) (p : F₀ Par (App₀ d))
               → fst m (App₀ d) (App₁ g) p ≡ pure (pt Par Val x₀ (App₀ d))
  Adm-pullback c m adm d g p = adm (App₀ d) (App₁ g) p
