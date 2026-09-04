{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MechanismGeometric — admissibility survives abstraction.
--
-- Topos.BaseChange shows that the comparison map of an
-- abstraction preserves ⊤, ⊥, ∧ and ∨ for every base functor,
-- and Topos.AbstractionTiers shows that ⇒ and ¬ need the back
-- condition.  That split has a causal reading, and this module
-- puts admissibility on the right side of it.
--
-- Admissibility says a mechanism returns the point mass at x₀,
-- which is an equation.  Equations are built from ⊤ and ∧, the
-- part of the logic every abstraction carries.  So the property
-- of BEING a do-mechanism transfers along every abstraction of
-- contexts, with no condition on the abstraction.
--
-- The contrast is with a property stated by quantifying over
-- mechanisms, which needs ⇒ and therefore needs the back
-- condition.  Adm-pullback below is the transferable half.
--
-- The proof reuses Topos.MechanismObject's admissibility and the
-- comparison map directly; nothing about probability enters.
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

  -- ----------------------------------------------------------
  -- A coarse mechanism, read on the fine site.  The exponential
  -- and the distribution object are both computed downstairs;
  -- what travels is the element.
  -- ----------------------------------------------------------
  pullMech : (c : Cc.Ob) → F₀ (Mech Par Val x₀) (App₀ c)
           → (d : Dc.Ob) → Dc.Hom d (App₀ c) → F₀ Par d → F₀ (Dist_E {C = D} Val) d
  pullMech c m = fst m

  -- ----------------------------------------------------------
  -- ADMISSIBILITY IS PRESERVED, with no condition on F.
  --
  -- The witness downstairs quantifies over all arrows into
  -- App₀ c; the witness needed upstairs quantifies over the
  -- images of arrows into c, which are among them.  So the
  -- transfer is an instantiation, not a construction.
  -- ----------------------------------------------------------
  Adm-pullback : (c : Cc.Ob) (m : F₀ (Mech Par Val x₀) (App₀ c))
               → fst (Adm Par Val x₀ (App₀ c) m)
               → (d : Cc.Ob) (g : Cc.Hom d c) (p : F₀ Par (App₀ d))
               → fst m (App₀ d) (App₁ g) p ≡ pure (pt Par Val x₀ (App₀ d))
  Adm-pullback c m adm d g p = adm (App₀ d) (App₁ g) p

  -- ----------------------------------------------------------
  -- THE CONTRAST.
  --
  -- Adm-pullback needs nothing of F because admissibility is an
  -- equation, and Topos.BaseChange preserves ⊤, ⊥, ∧ and ∨ for
  -- every base functor.  A property stated by quantifying over
  -- mechanisms is built with ⇒ instead, and Topos.AbstractionTiers
  -- shows ⇒ transfers only when F satisfies the back condition
  -- (φB-⇒, which takes BackCond∥ as a hypothesis).  So being a
  -- do-mechanism survives every coarse-graining of contexts,
  -- while being the do-operator for a variable need not.
  --
  -- We do not formalise the reflection direction here.
  -- ----------------------------------------------------------
