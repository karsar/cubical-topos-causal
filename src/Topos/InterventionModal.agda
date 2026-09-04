{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.InterventionModal — the Stage-2 causal payload: the
-- value an intervention forces is j-CLOSED under every Lawvere–
-- Tierney topology.
--
-- Stage 1 (Topos.DoClassifier) showed that do(X := x₀) is
-- classified by a characteristic map χ : X ⇒ Ω, and that the
-- forced value pt c goes to the maximal sieve ⊤ (do-classified).
-- Stage 2 (Topos.LawvereTierney) introduced topologies j : Ω → Ω
-- and their j-closed sieves.
--
-- This module connects them.  For ANY topology J, the sieve that
-- classifies the intervened value is j-closed:
--
--     is-j-closed J c (χ_c (x₀ c)).
--
-- Causal reading.  An intervention is invariant under every
-- modality ◯, that is, under sheafification or localization.
-- do(X := x₀) is "j-stable discovery" in the sense of
-- outline.md:85, since the do-fact survives passage to any
-- sub-topos of j-sheaves.  The j-do-calculus thesis (j = lex
-- modality) is here made internal and machine-checked for the
-- intervention classifier.
-- ============================================================

module Topos.InterventionModal where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.DoClassifier
open import Topos.LawvereTierney
open LawvereTierney

module _ {ℓ} {C : Precategory ℓ ℓ} (X : PSh C ℓ) (x₀ : Section {C = C} X) where
  open Precategory C

  -- the characteristic sieve of the intervened value, regime-wise
  do-sieve : (c : Ob) → Sieve {C = C} c
  do-sieve c = χ-sieve X x₀ c (pt X x₀ c)

  -- The intervention classifier is j-closed for every Lawvere–
  -- Tierney topology J.  Proof: do-classified sends it to ⊤, and
  -- ⊤ is j-closed by truth-preservation.
  do-j-stable : (J : LawvereTierney {C = C}) (c : Ob)
              → is-j-closed J c (do-sieve c)
  do-j-stable J c =
    cong (jop J c) e ∙ j-⊤ J c ∙ sym e
    where
      e : do-sieve c ≡ maximal {C = C} c
      e = do-classified X x₀ c
