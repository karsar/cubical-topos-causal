{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.NonTrivialModal — Stage 2 (a): the modal results
-- instantiated at the double-negation topology.
--
-- do-j-stable and modal-rule1 (Topos.InterventionModal and
-- Topos.ModalRule1) hold for every Lawvere–Tierney topology.  The
-- only instance proved before this module was trivialLT, the
-- identity, which makes them vacuous.  Here they are instantiated
-- at ¬¬LT (Topos.DoubleNegation).  That topology is not
-- degenerate: its sheaves are the ¬¬-separated objects, which
-- form the Boolean localization.
--
-- Both the intervention classifier and Pearl Rule 1 are ¬¬-closed.
-- They survive passage to the double-negation sheaf subtopos.
-- This is the first non-vacuous witness of the j-do-calculus
-- thesis.
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
open import Topos.ModalRules
open import Topos.Rule2 using (SCM-conf-E; X-indep-Z-E)
open import Topos.Rule3 using (SCM₃-E)

module _ {ℓ} {C : Precategory ℓ ℓ} (X Y : PSh C ℓ)
         (m : SCM-E {C = C} X Y) (ind : Indep-E {C = C} {X = X} {Y = Y} m)
         (x₀ : Section {C = C} X) where
  open Precategory C

  -- The intervention do(X := x₀) is classified by a ¬¬-closed
  -- sieve.  The do-fact survives the double-negation (Boolean)
  -- localization.
  do-¬¬-stable : (c : Ob)
               → is-j-closed (¬¬LT {C = C}) c (do-sieve X x₀ c)
  do-¬¬-stable c = do-j-stable X x₀ (¬¬LT {C = C}) c

  -- Pearl Rule 1 holds in the ¬¬-sheaf subtopos.  Its internalised
  -- conclusion is ¬¬-closed.
  rule1-¬¬-modal : (c : Ob)
                 → is-j-closed (¬¬LT {C = C}) c
                     (rule1-Ω X Y m ind (pt X x₀) c)
  rule1-¬¬-modal c = modal-rule1 X Y m ind (pt X x₀) (¬¬LT {C = C}) c

-- ------------------------------------------------------------
-- Rules 2 and 3 at the double-negation topology.
--
-- modal-rule2 and modal-rule3 are proved for an arbitrary
-- topology, so instantiating them at ¬¬ is one application
-- each.  We write them out rather than leave them implied.
-- ------------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} (X Z Y : PSh C ℓ)
         (m : SCM-conf-E {C = C} X Z Y)
         (ind : X-indep-Z-E {C = C} {X = X} {Z = Z} {Y = Y} m)
         (x₀ : (c : Precategory.Ob C) → PSh.F₀ X c) where
  open Precategory C

  rule2-¬¬-modal : (c : Ob)
                 → is-j-closed (¬¬LT {C = C}) c (rule2-Ω X Z Y m ind x₀ c)
  rule2-¬¬-modal c = modal-rule2 X Z Y m ind x₀ (¬¬LT {C = C}) c

module _ {ℓ} {C : Precategory ℓ ℓ} (X Y Z : PSh C ℓ)
         (m : SCM₃-E {C = C} X Y Z)
         (z₀ : (c : Precategory.Ob C) → PSh.F₀ Z c) where
  open Precategory C

  rule3-¬¬-modal : (c : Ob)
                 → is-j-closed (¬¬LT {C = C}) c (rule3-Ω X Y Z m z₀ c)
  rule3-¬¬-modal c = modal-rule3 X Y Z m z₀ (¬¬LT {C = C}) c
