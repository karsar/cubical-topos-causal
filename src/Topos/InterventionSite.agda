{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.InterventionSite — the intervention poset as a site.
--
-- This is the base for Gate 1 of the topos-directed-homotopy
-- programme.  Gate 1 recomputes the modality on a coverage that
-- is not degenerate.  The question is whether the ⊤-collapse is
-- caused by the coverage or by invertibility.
--
-- Base category (a thin poset):
--     do0 ─→ obs ←─ do1
-- `obs` is the observational context, that is, do(∅).  `do0` and
-- `do1` are the two interventions do(X:=0) and do(X:=1).  Each of
-- them refines `obs`.  In the discrete two-regime site of
-- Topos.ContingentCI the only arrow into an object is its
-- identity.  Here `obs` has the covering family {do0, do1}.  The
-- causal reading is "observing is covered by intervening at every
-- value".
-- ============================================================

module Topos.InterventionSite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Prelude using (isProp→isSet)

open import Topos.Cat

-- ------------------------------------------------------------
-- Objects and morphisms of the intervention poset.
-- ------------------------------------------------------------
data IObj : Type where
  obs do0 do1 : IObj

data IHom : IObj → IObj → Type where
  idₒ : IHom obs obs
  id₀ : IHom do0 do0
  id₁ : IHom do1 do1
  e0  : IHom do0 obs      -- do0 ≤ obs
  e1  : IHom do1 obs      -- do1 ≤ obs

-- Thin: every hom-set is a proposition.
isPropIHom : (x y : IObj) → isProp (IHom x y)
isPropIHom obs obs idₒ idₒ = refl
isPropIHom do0 do0 id₀ id₀ = refl
isPropIHom do1 do1 id₁ id₁ = refl
isPropIHom do0 obs e0  e0  = refl
isPropIHom do1 obs e1  e1  = refl
isPropIHom obs do0 ()
isPropIHom obs do1 ()
isPropIHom do0 do1 ()
isPropIHom do1 do0 ()

-- Identities and composition.  Thinness determines both.
idI : ∀ {x} → IHom x x
idI {obs} = idₒ
idI {do0} = id₀
idI {do1} = id₁

_⋆I_ : ∀ {x y z} → IHom x y → IHom y z → IHom x z
idₒ ⋆I g = g
id₀ ⋆I g = g
id₁ ⋆I g = g
e0  ⋆I idₒ = e0
e1  ⋆I idₒ = e1

-- ------------------------------------------------------------
-- The intervention poset as a Precategory.  Every category law
-- is an equality in a hom-set, so propositionality proves it.
-- ------------------------------------------------------------
Iv : Precategory ℓ-zero ℓ-zero
Iv = record
  { Ob       = IObj
  ; Hom      = IHom
  ; idn      = idI
  ; _⋆_      = _⋆I_
  ; ⋆-idL    = λ f → isPropIHom _ _ (idI ⋆I f) f
  ; ⋆-idR    = λ f → isPropIHom _ _ (f ⋆I idI) f
  ; ⋆-assoc  = λ f g h → isPropIHom _ _ ((f ⋆I g) ⋆I h) (f ⋆I (g ⋆I h))
  ; isSetHom = λ {x} {y} → isProp→isSet (isPropIHom x y)
  }
