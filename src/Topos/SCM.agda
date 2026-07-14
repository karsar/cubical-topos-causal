{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.SCM — internal structural causal models over the
-- regime base C.  An internal SCM on presheaves X, Y is,
-- regime-wise, an ordinary verified SCM₂ from the core; the
-- internal intervention do(X := x₀) is regime-wise kernel
-- substitution (the core's `do-X`); the internal Y-marginal is
-- a regime-indexed section of the internal distribution object
-- Dist_E Y.
-- ============================================================

module Topos.SCM where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; snd)

open import FDist-Convex using (FDist; mapF)
open import RuleDoCalc   using (SCM₂; joint-of; do-X; Y-indep-X)

open import Topos.Cat
open import Topos.PSh
open import Topos.InternalDist

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- internal SCM: regime-wise an ordinary SCM₂
  SCM-E : ∀ {ℓ ℓ'} → PSh C ℓ → PSh C ℓ' → Type (ℓ-max (ℓ-max ℓo ℓ) ℓ')
  SCM-E X Y = (c : Ob) → SCM₂ (F₀ X c) (F₀ Y c)

  -- internal intervention do(X := x₀): regime-wise kernel substitution
  do-XE : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'}
        → ((c : Ob) → F₀ X c) → SCM-E X Y → SCM-E X Y
  do-XE x₀ m = λ c → do-X (x₀ c) (m c)

  -- internal structural independence: regime-wise Y ⫫ X
  Indep-E : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'} → SCM-E X Y → Type (ℓ-max ℓo (ℓ-max ℓ ℓ'))
  Indep-E m = (c : Ob) → Y-indep-X (m c)

  -- internal Y-marginal: a regime-indexed section of Dist_E Y
  marginalY-E : ∀ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'}
              → SCM-E X Y → ((c : Ob) → F₀ (Dist_E Y) c)
  marginalY-E m = λ c → mapF snd (joint-of (m c))
