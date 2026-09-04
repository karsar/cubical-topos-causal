{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Rule1 — internal Pearl Rule 1, the Stage 1 result.
--
-- A regime is an object of the base category C.  An internal
-- SCM is a family of SCMs, one for each regime.
--
-- Internal Pearl Rule 1.  Assume structural independence Y ⫫ X.
-- Then the internal intervention do(X := x₀) leaves the internal
-- Y-marginal unchanged, at every regime.  The proof applies the
-- verified core theorem RuleDoCalc.rule1-marginal at each regime.
-- The topos layer adds no causal content of its own.  It wraps
-- the machine-checked Rule 1 of the core.
--
-- The statement is written inline, in the form that checks
-- without unfolding.  It is definitionally the internal
-- statement
--     marginalY-E (do-XE x₀ m) c ≡ marginalY-E m c
-- where marginalY-E and do-XE are the internal operations of
-- Topos.SCM: mapF snd ∘ joint-of, and regime-wise do-X.
-- ============================================================

module Topos.Rule1 where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (snd)

open import FDist-Convex using (mapF)
open import RuleDoCalc   using (joint-of; do-X; rule1-marginal)

open import Topos.Cat
open import Topos.PSh
open import Topos.InternalDist
open import Topos.SCM

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- Internal Rule 1, one regime at a time.  The left side is
  -- marginalY-E (do-XE x₀ m) c and the right side is
  -- marginalY-E m c, both definitionally.
  rule1-E : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'}
            (m : SCM-E X Y) (ind : Indep-E {X = X} {Y = Y} m) (x₀ : (c : Ob) → F₀ X c)
          → (c : Ob)
          → mapF snd (joint-of (do-X (x₀ c) (m c))) ≡ mapF snd (joint-of (m c))
  rule1-E m ind x₀ c = rule1-marginal (m c) (ind c) (x₀ c)

  -- ----------------------------------------------------------------
  -- Internal Rule 1 at the level of internal morphisms.
  --
  -- Natural means that the internal Y-marginal of m commutes with
  -- regime restriction.  A natural marginal is an internal global
  -- element, that is, a Section of Dist_E Y.  Naturality is a
  -- hypothesis here, carried by the witnesses `ndo` and `nm`.  It
  -- is established separately, and holds once the SCM's prior and
  -- kernel are natural.  Given the witnesses, Nat≡ turns the
  -- pointwise rule1-E into an equality of internal morphisms
  -- `𝟙 ⇒ Dist_E Y`.
  -- ----------------------------------------------------------------
  rule1-E-nat : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'}
    (m : SCM-E X Y) (ind : Indep-E {X = X} {Y = Y} m) (x₀ : (c : Ob) → F₀ X c)
    (ndo : IsNat 𝟙 (Dist_E Y) (λ c _ → mapF snd (joint-of (do-X (x₀ c) (m c)))))
    (nm  : IsNat 𝟙 (Dist_E Y) (λ c _ → mapF snd (joint-of (m c))))
    → _≡_ {A = Section (Dist_E Y)}
        ((λ c _ → mapF snd (joint-of (do-X (x₀ c) (m c)))) , ndo)
        ((λ c _ → mapF snd (joint-of (m c))) , nm)
  rule1-E-nat {X = X} {Y = Y} m ind x₀ ndo nm =
    Nat≡ {X = 𝟙} {Y = Dist_E Y} _ _ (λ c _ → rule1-E {X = X} {Y = Y} m ind x₀ c)
