{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.InterventionSite — the intervention poset as a site, for
-- Gate 1 of the topos-directed-homotopy programme: recompute the
-- modality on a NON-degenerate coverage and see whether the
-- ⊤-collapse survives (coverage cause) or persists (invertibility).
--
-- Base category (a thin poset):
--     do0 ─→ obs ←─ do1
-- `obs` is the observational context (do(∅)); `do0`, `do1` are the
-- two interventions do(X:=0), do(X:=1), each refining `obs`.  Unlike
-- the discrete two-regime site of Topos.ContingentCI, here `obs` has
-- a genuine non-trivial covering family {do0, do1} — the causal
-- reading "observing is covered by intervening at every value".
-- ============================================================

module Topos.InterventionSite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp→isSet)

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

-- Identities and composition (determined, since thin).
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
-- The intervention poset as a Precategory.  All the category laws
-- are equalities in a hom-set, hence hold by propositionality.
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
