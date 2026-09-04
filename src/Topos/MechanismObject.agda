{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MechanismObject — classifying the intervention, not
-- its target.
--
-- Topos.DoClassifier classifies the value-fixing subobject
-- "X = x₀" inside the value presheaf.  That subobject is the
-- same whether the value is reached by surgery or by
-- observation, so its characteristic map cannot separate the
-- two.  The paper records the remaining route: classify a
-- subobject of a presheaf of MECHANISMS.  This module takes
-- that route.
--
-- The mechanism object is the exponential
--     Mech = Exp Par (Dist_E Val),
-- an object of the same topos (Topos.Exponential).  A mechanism
-- is admissible for the fixed value x₀ when it ignores its
-- parents and returns the point mass at x₀, at every stage.
--
-- Results:
--   Adm-closed    admissibility is closed under restriction.
--   χ-do          the characteristic map Mech ⇒ Ω, obtained from
--                 the universal property of Topos.Classifier.
--   do-true       the do-mechanism is classified true.
--   χ-do-unique   χ-do is the only such map.
--
-- So Ω does classify the intervention once the classifier is
-- pointed at mechanisms rather than at values.  Separation from
-- observation is Topos.MechanismSeparation.
-- ============================================================

module Topos.MechanismObject where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)

open import FDist-Convex using (FDist; pure; trunc)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.Exponential
open import Topos.Classifier using (Classifies; χ; χ-sieve; χ-classifies; unique)

module _ {ℓ} {C : Precategory ℓ ℓ}
         (Par Val : PSh C ℓ) (x₀ : Section {C = C} Val) where
  open Precategory C
  open PSh

  -- The fixed value, stage by stage.
  pt : (c : Ob) → F₀ Val c
  pt c = fst x₀ c _

  -- ----------------------------------------------------------
  -- The mechanism object: kernels from the parents to the
  -- variable, as an object of the topos.
  -- ----------------------------------------------------------
  Mech : PSh C ℓ
  Mech = Exp {C = C} Par (Dist_E {C = C} Val)

  -- ----------------------------------------------------------
  -- Admissibility.  A mechanism is a do-mechanism for x₀ when
  -- it returns the point mass at x₀ whatever its parents say,
  -- at every stage below c.
  -- ----------------------------------------------------------
  Adm : (c : Ob) → F₀ Mech c → hProp ℓ
  Adm c m =
    ( (d : Ob) (g : Hom d c) (p : F₀ Par d) → fst m d g p ≡ pure (pt d) )
    , isPropΠ λ d → isPropΠ λ g → isPropΠ λ p → trunc _ _

  -- Closure under restriction.  Restricting a mechanism
  -- precomposes its index arrow, so an admissibility witness at
  -- c is reused at d by composing.
  Adm-closed : (d e : Ob) (k : Hom e d) (m : F₀ Mech d)
             → fst (Adm d m) → fst (Adm e (F₁ Mech k m))
  Adm-closed d e k m adm d' g p = adm d' (g ⋆ k) p

  -- ----------------------------------------------------------
  -- The classifier of the intervention.
  -- ----------------------------------------------------------
  χ-do : Nat Mech (Ω {C = C})
  χ-do = χ Mech Adm Adm-closed

  χ-do-sieve : (c : Ob) → F₀ Mech c → Sieve {C = C} c
  χ-do-sieve = χ-sieve Mech Adm Adm-closed

  -- The classification theorem, at the level of mechanisms: the
  -- sieve is maximal exactly on the do-mechanisms.
  χ-do-classifies : Classifies Mech Adm Adm-closed (λ c m → χ-do-sieve c m)
  χ-do-classifies = χ-classifies Mech Adm Adm-closed

  -- And it is the only such map.
  χ-do-unique : (χ' : Nat Mech (Ω {C = C}))
              → Classifies Mech Adm Adm-closed (fst χ') → χ' ≡ χ-do
  χ-do-unique = unique Mech Adm Adm-closed
