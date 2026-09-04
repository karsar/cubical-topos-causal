{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.ModalCI — Stage 3 of the modal-layer repair: j-stability
-- of the contingent CI, applied to a truth value that is not ⊤.
--
-- Topos.ContingentCI built `ci-Ω`.  It is a causal claim whose
-- internal truth value is ⊤ at one regime and the empty sieve at
-- the other.  That is the first input to the modality which is
-- not ⊤ everywhere.  The Stage-3 question is whether this
-- contingent truth value is j-stable.  For the double-negation
-- topology (Topos.DoubleNegation, the one non-degenerate topology
-- available here) it is, at BOTH regimes:
--   • at `false`, ci-Ω = ⊤, and ⊤ is ¬¬-closed;
--   • at `true`,  ci-Ω = ⊥ (the CI fails), and ⊥ is ¬¬-closed.
-- The true-regime instance applies to a sieve that is not
-- maximal, so it avoids the "always ⊤" collapse of
-- `modal-rule1/2/3`.
--
-- Causal reading.  At a regime the conditional-independence claim
-- either holds (⊤) or fails (⊥).  Either verdict survives the
-- Boolean (¬¬) localisation.
-- ============================================================

module Topos.ModalCI where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty using (⊥*; isProp⊥*) renaming (rec to ⊥rec; rec* to ⊥rec*)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney using (is-j-closed)
open import Topos.DoubleNegation using (¬¬S; ¬¬LT; ⊥S; _≤S_; ≤-antisym; dne-unit; j-⊤-¬¬)
open import Topos.ContingentCI using (C; ci-Ω; ci-Ω-false-⊤; P; ¬P-true)

-- ------------------------------------------------------------
-- The true regime.  ci-Ω true is the empty sieve, because the CI
-- fails there.  The empty sieve is its own double negation.
-- ------------------------------------------------------------
private
  open Precategory C using (Ob; Hom; idn)

  -- ci-Ω true is the empty sieve.  Its membership is the false
  -- proposition `P true`, which is equivalent to ⊥ at every
  -- arrow.
  ci-Ω-true-⊥ : ci-Ω true ≡ ⊥S {C = C} true
  ci-Ω-true-⊥ =
    Sieve≡ {C = C} (ci-Ω true) (⊥S {C = C} true)
      (funExt λ d → funExt λ f →
        ⇔toPath {P = P true} {Q = ⊥* , isProp⊥*}
          (λ pt → ⊥rec (¬P-true pt))
          (λ b → ⊥rec* b))

  -- The empty sieve is its own double negation (⊥ is ¬¬-closed).
  ⊥true : Sieve {C = C} true
  ⊥true = ⊥S {ℓ = ℓ-zero} {C = C} true

  ¬¬-⊥-≤ : _≤S_ {ℓ = ℓ-zero} {C = C} (¬¬S {ℓ = ℓ-zero} {C = C} ⊥true) ⊥true
  ¬¬-⊥-≤ d f nn = nn d (idn {x = d}) (λ e g x → x)

  ¬¬-⊥-closed : ¬¬S {ℓ = ℓ-zero} {C = C} ⊥true ≡ ⊥true
  ¬¬-⊥-closed =
    ≤-antisym {ℓ = ℓ-zero} {C = C} (¬¬S {ℓ = ℓ-zero} {C = C} ⊥true) ⊥true
      ¬¬-⊥-≤ (dne-unit {ℓ = ℓ-zero} {C = C} ⊥true)

  true-closed : is-j-closed (¬¬LT {C = C}) true (ci-Ω true)
  true-closed =
    cong (¬¬S {ℓ = ℓ-zero} {C = C}) ci-Ω-true-⊥ ∙ ¬¬-⊥-closed ∙ sym ci-Ω-true-⊥

  -- The false regime.  ci-Ω false = ⊤, and ¬¬⊤ = ⊤.
  false-closed : is-j-closed (¬¬LT {C = C}) false (ci-Ω false)
  false-closed =
    cong (¬¬S {ℓ = ℓ-zero} {C = C}) ci-Ω-false-⊤
      ∙ j-⊤-¬¬ {ℓ = ℓ-zero} {C = C} false ∙ sym ci-Ω-false-⊤

-- ------------------------------------------------------------
-- STAGE 3 DELIVERABLE: the contingent CI is ¬¬-stable at every
-- regime.  The true-regime instance applies to a sieve that is
-- NOT maximal, so it says more than the "j ⊤ = ⊤" step used by
-- the modal-rule theorems.
-- ------------------------------------------------------------
ci-Ω-¬¬-closed : (c : Bool) → is-j-closed (¬¬LT {C = C}) c (ci-Ω c)
ci-Ω-¬¬-closed false = false-closed
ci-Ω-¬¬-closed true  = true-closed
