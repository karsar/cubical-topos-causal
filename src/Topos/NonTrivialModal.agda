{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.NonTrivialModal — Stage 2 (a) payoff: the modal results
-- instantiated at the NON-TRIVIAL double-negation topology.
--
-- do-j-stable and modal-rule1 (Topos.InterventionModal /
-- Topos.ModalRule1) hold for every Lawvere–Tierney topology, but
-- the only instance proved so far was trivialLT (identity), making
-- them vacuous.  Here we instantiate them at ¬¬LT (Topos.Double-
-- Negation) — a genuinely non-degenerate topology whose sheaves
-- are the ¬¬-separated objects (the Boolean localization).
--
-- Conclusion: the intervention classifier and Pearl Rule 1 are
-- BOTH ¬¬-closed — they survive passage to the double-negation
-- sheaf subtopos.  This is the first non-vacuous witness of the
-- j-do-calculus thesis.
-- ============================================================

module Topos.NonTrivialModal where

open import Cubical.Core.Primitives

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.SCM
open import Topos.DoClassifier
open import Topos.LawvereTierney
open import Topos.DoubleNegation
open import Topos.InterventionModal
open import Topos.ModalRule1

module _ {ℓ} {C : Precategory ℓ ℓ} (X Y : PSh C ℓ)
         (m : SCM-E {C = C} X Y) (ind : Indep-E {C = C} {X = X} {Y = Y} m)
         (x₀ : Section {C = C} X) where
  open Precategory C

  -- the intervention do(X := x₀) is classified by a ¬¬-closed sieve:
  -- the do-fact survives the double-negation (Boolean) localization.
  do-¬¬-stable : (c : Ob)
               → is-j-closed (¬¬LT {C = C}) c (do-sieve X x₀ c)
  do-¬¬-stable c = do-j-stable X x₀ (¬¬LT {C = C}) c

  -- Pearl Rule 1 holds in the ¬¬-sheaf subtopos: its internalised
  -- conclusion is ¬¬-closed.
  rule1-¬¬-modal : (c : Ob)
                 → is-j-closed (¬¬LT {C = C}) c
                     (rule1-Ω X Y m ind (pt X x₀) c)
  rule1-¬¬-modal c = modal-rule1 X Y m ind (pt X x₀) (¬¬LT {C = C}) c
