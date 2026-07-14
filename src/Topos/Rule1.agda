{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Rule1 — THE STAGE-1 DELIVERABLE.
--
-- Internal Pearl Rule 1: under structural independence Y ⫫ X,
-- the internal intervention do(X := x₀) leaves the internal
-- Y-marginal invariant, at every regime — by lifting the
-- verified core theorem RuleDoCalc.rule1-marginal pointwise.
-- No causal content is re-proved: the topos layer wraps the
-- machine-checked Rule 1 of the core.
--
-- The statement is written in the manifestly-checking inline
-- form; it is *definitionally* the internal statement
--     marginalY-E (do-XE x₀ m) c ≡ marginalY-E m c
-- with marginalY-E / do-XE the internal API of Topos.SCM
-- (mapF snd ∘ joint-of, and regime-wise do-X).
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

  -- internal Rule 1, regime-wise.
  -- LHS ≡ marginalY-E (do-XE x₀ m) c ,  RHS ≡ marginalY-E m c   (definitionally).
  rule1-E : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'}
            (m : SCM-E X Y) (ind : Indep-E {X = X} {Y = Y} m) (x₀ : (c : Ob) → F₀ X c)
          → (c : Ob)
          → mapF snd (joint-of (do-X (x₀ c) (m c))) ≡ mapF snd (joint-of (m c))
  rule1-E m ind x₀ c = rule1-marginal (m c) (ind c) (x₀ c)

  -- ----------------------------------------------------------------
  -- Nat≡ upgrade: internal Rule 1 at the level of internal MORPHISMS.
  --
  -- When the internal Y-marginal of m is natural (coheres with regime
  -- restriction) — supplied here as the witnesses `ndo`, `nm`, the
  -- separately-establishable fact that holds once the SCM's prior and
  -- kernel are natural — it is an internal global element (a Section of
  -- Dist_E Y).  Internal Rule 1 then upgrades from a pointwise family
  -- identity to an EQUALITY OF INTERNAL MORPHISMS `𝟙 ⇒ Dist_E Y`,
  -- obtained by feeding the pointwise rule1-E to Nat≡.
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
