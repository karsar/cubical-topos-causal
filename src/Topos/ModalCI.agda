{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.ModalCI — Stage 3 of the modal-layer repair: j-stability
-- of the contingent CI, applied to something that is NOT ⊤.
--
-- Topos.ContingentCI exhibited `ci-Ω`, a causal claim whose internal
-- truth value is ⊤ at one regime and a non-maximal (in fact empty)
-- sieve at another — the first non-vacuous input the modality has.
-- Here we ask the Stage-3 question: is that contingent truth value
-- j-stable?  For the double-negation topology (Topos.DoubleNegation,
-- the one non-degenerate instance we have) the answer is YES at BOTH
-- regimes, and — crucially — non-vacuously:
--   • at `false`, ci-Ω = ⊤, and ⊤ is ¬¬-closed;
--   • at `true`,  ci-Ω = ⊥ (the CI fails), and ⊥ is ¬¬-closed.
-- Neither case is the "always ⊤" collapse of `modal-rule1/2/3`: the
-- true-regime value is genuinely non-maximal, yet still ¬¬-stable.
--
-- Causal reading: whether the conditional-independence claim holds
-- (⊤) or fails (⊥) at a regime, that verdict survives the Boolean
-- (¬¬) localisation — j-stability with content, not with ⊤.
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
-- The true regime: ci-Ω true is the empty sieve (the CI fails), and
-- the empty sieve is its own double negation.
-- ------------------------------------------------------------
private
  open Precategory C using (Ob; Hom; idn)

  -- ci-Ω true IS the empty sieve: its membership (the false prop
  -- P true) is logically equivalent to ⊥ at every arrow.
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

  -- The false regime: ci-Ω false = ⊤, and ¬¬⊤ = ⊤.
  false-closed : is-j-closed (¬¬LT {C = C}) false (ci-Ω false)
  false-closed =
    cong (¬¬S {ℓ = ℓ-zero} {C = C}) ci-Ω-false-⊤
      ∙ j-⊤-¬¬ {ℓ = ℓ-zero} {C = C} false ∙ sym ci-Ω-false-⊤

-- ------------------------------------------------------------
-- STAGE 3 DELIVERABLE: the contingent CI is ¬¬-stable at every
-- regime — a j-stability theorem whose true-regime instance is
-- applied to a NON-maximal sieve, so it is not the vacuous
-- "j ⊤ = ⊤" of the modal-rule theorems.
-- ------------------------------------------------------------
ci-Ω-¬¬-closed : (c : Bool) → is-j-closed (¬¬LT {C = C}) c (ci-Ω c)
ci-Ω-¬¬-closed false = false-closed
ci-Ω-¬¬-closed true  = true-closed
