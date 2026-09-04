{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.DoClassifier — the gate probe: wiring Ω into the do-
-- operator.
--
-- Stage 1 built Ω (Topos.Omega) and proved do-calculus Rule1/2/3
-- for a do-operator defined operationally.  There, do-X replaces
-- the X-prior with a point mass.  This module connects the two
-- descriptions.  It exhibits the intervention do(X := x₀) as a
-- characteristic map
--
--     χ : X ⇒ Ω
--
-- into the subobject classifier.  χ classifies the value-fixing
-- subobject  {x₀} ↪ X.  This is the topos-internal content of
-- Mahadevan's "intervention via the subobject classifier", which
-- Omega's header comment only asserted.
--
-- One point of scope.  A topos-internal intervention fixes X to
-- a natural global element  x₀ : Section X.  Topos.SCM.do-XE
-- currently accepts a bare regime-indexed family, which is
-- weaker.  The naturality is what makes the value-fixing family
-- a subpresheaf, and it is also what makes χ natural.
--
-- This module provides:
--   χ              : X ⇒ Ω                       (an internal morphism)
--   true→fixed     : χ c b = ⊤  →  b = x₀ c       (χ classifies {x₀})
--   fixed→true     : b = x₀ c  →  χ c b = ⊤
--   do-classified  : χ c (x₀ c) = ⊤              (the forced value is χ-true)
--   do-prior       : prior of do-XE x₀ m  =  pure (x₀ c)  (bridge to Stage 1)
-- ============================================================

module Topos.DoClassifier where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*; tt)

open import FDist-Convex using (FDist; pure)
open import RuleDoCalc   using (SCM₂)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.SCM

-- We work at a single universe level ℓ.  Base regimes, hom-sets
-- and value spaces all sit at ℓ.  This is the setting of
-- Topos.Example.  It also keeps Ω's membership level, which is
-- the hom level, equal to the level of the value presheaf's
-- fibres.  X is the value presheaf.  x₀ is the intervened value,
-- given as a natural global element.
module _ {ℓ} {C : Precategory ℓ ℓ} (X : PSh C ℓ) (x₀ : Section {C = C} X) where
  open Precategory C
  open PSh

  -- The intervened value, regime by regime, and its naturality.
  pt : (c : Ob) → F₀ X c
  pt c = fst x₀ c tt

  pt-nat : (x y : Ob) (f : Hom x y) → pt x ≡ F₁ X f (pt y)
  pt-nat x y f = snd x₀ x y f tt

  -- ----------------------------------------------------------
  -- The characteristic map χ : X ⇒ Ω.
  --
  -- χ_c(b) is the sieve of those f : d → c along which b
  -- restricts to the fixed value.  That is, { f | F₁ X f b =
  -- pt d }.  b lies in the value-fixing subobject exactly when
  -- this sieve is maximal.  The proof is below.
  -- ----------------------------------------------------------

  χ-mem : (c : Ob) → F₀ X c → SieveMem {C = C} c
  χ-mem c b d f = (F₁ X f b ≡ pt d) , isSetF₀ X d (F₁ X f b) (pt d)

  χ-closed : (c : Ob) (b : F₀ X c) → Closure {C = C} c (χ-mem c b)
  χ-closed c b d e k f pf =
    F-comp X k f b ∙ cong (F₁ X k) pf ∙ sym (pt-nat e d k)

  χ-sieve : (c : Ob) → F₀ X c → Sieve {C = C} c
  χ-sieve c b = χ-mem c b , χ-closed c b

  -- Naturality.  χ commutes with restriction, which on Ω is
  -- sieve pullback.
  χ-nat : IsNat X Ω (λ c b → χ-sieve c b)
  χ-nat x y f b =
    Sieve≡ {C = C} (χ-sieve x (F₁ X f b)) (pull {C = C} f (χ-sieve y b))
      (funExt λ d → funExt λ g →
        cong (λ z → (z ≡ pt d) , isSetF₀ X d z (pt d)) (sym (F-comp X g f b)))

  χ : Nat X Ω
  χ = (λ c b → χ-sieve c b) , χ-nat

  -- ----------------------------------------------------------
  -- χ classifies the value-fixing subobject {x₀} ↪ X:
  --   χ_c(b) is the maximal sieve  ⇔  b = x₀ c.
  -- ----------------------------------------------------------

  fixed→true : (c : Ob) (b : F₀ X c) → b ≡ pt c → χ-sieve c b ≡ maximal {C = C} c
  fixed→true c b hyp =
    Sieve≡ {C = C} (χ-sieve c b) (maximal {C = C} c)
      (funExt λ d → funExt λ f →
        ⇔toPath {P = (F₁ X f b ≡ pt d) , isSetF₀ X d (F₁ X f b) (pt d)}
                {Q = Unit* , isPropUnit*}
                (λ _ → tt*)
                (λ _ → cong (F₁ X f) hyp ∙ sym (pt-nat d c f)))

  true→fixed : (c : Ob) (b : F₀ X c) → χ-sieve c b ≡ maximal {C = C} c → b ≡ pt c
  true→fixed c b eq =
    sym (F-id X b) ∙ transport (λ i → fst (q (~ i))) tt*
    where
      -- Membership of the identity at c.  It is the equality
      -- (F₁ X idn b ≡ pt c) ≡ Unit*.
      q : ((F₁ X idn b ≡ pt c) , isSetF₀ X c (F₁ X idn b) (pt c))
        ≡ (Unit* , isPropUnit*)
      q = cong (λ S → fst S c idn) eq

  -- The value that do(X := x₀) forces is the χ-true point.
  do-classified : (c : Ob) → χ-sieve c (pt c) ≡ maximal {C = C} c
  do-classified c = fixed→true c (pt c) refl

  -- ----------------------------------------------------------
  -- Bridge to Stage 1.  The operational intervention do-XE sets
  -- the X-prior to a point mass.  It forces the value pt c, and
  -- χ sends that point to ⊤.  So χ is the characteristic map of
  -- the do-XE intervention.
  -- ----------------------------------------------------------
  module _ {ℓ'} (Y : PSh C ℓ') (m : SCM-E {C = C} X Y) where
    do-prior : (c : Ob) → SCM₂.pX (do-XE {C = C} {X = X} {Y = Y} pt m c) ≡ pure (pt c)
    do-prior c = refl
