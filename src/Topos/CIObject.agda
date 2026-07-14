{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.CIObject — Stage 2 of the modal-layer repair: the
-- contingent CI as a genuine SUBOBJECT (a natural transformation
-- into Ω), with restriction-stability PROVED, not assumed.
--
-- Topos.ContingentCI packaged the contingent claim regime-by-regime
-- as `ci-Ω c = prop→sieve c (P c)`.  Here we upgrade it to a single
-- internal morphism `ci-Ω-nat : 𝟙 ⇒ Ω`, obtained from the universal
-- property of Ω (Topos.Classifier.χ): a subobject of the terminal
-- presheaf, i.e. an internal truth value.  The classifier turns the
-- arrow-indexed family "the claim holds after restriction along f"
-- into the sieve χ_c(*) = { f : d → c | P holds at d }, and the
-- restriction-stability obligation `P-closed` — Mahadevan's
-- "refinement preserves the claim" — is discharged for this base.
--
-- HONEST SCOPE.  The base here is the two-regime discrete category,
-- on which morphisms are equalities, so `P-closed` holds by
-- transport and is not yet the substantive "conditioning preserves
-- conditional independence" statement.  That substantive form is
-- exactly where the content — and a genuine obstruction — lives:
-- for a COLLIDER, conditioning on the collider vertex OPENS the
-- path, so CI is NOT preserved under that refinement (Berkson's
-- paradox).  Hence `ci-Ω` is a sieve only when refinement is
-- restricted to CI-preserving conditioning; the collider is a
-- counterexample to unrestricted restriction-stability.  Making
-- that precise needs Bayesian conditioning on the convex-HIT and
-- the general d-separation soundness theorem, which is future work
-- (see Topos.ContingentCI and the companion d-separation layer).
-- ============================================================

module Topos.CIObject where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Classifier using (χ; maximal→mem)
open import Topos.ContingentCI using (C; P; ¬P-true)

open Precategory C using (Ob; Hom; idn)
open PSh

-- ------------------------------------------------------------
-- The predicate P on the terminal presheaf 𝟙, and its
-- restriction-stability.  On the discrete base a morphism k : e → d
-- is an equality e ≡ d, so the claim transports along it.
-- ------------------------------------------------------------
P-𝟙 : (c : Ob) → F₀ (𝟙 {C = C}) c → hProp ℓ-zero
P-𝟙 c _ = P c

P-𝟙-closed : (d e : Ob) (k : Hom e d) (b : F₀ (𝟙 {C = C}) d)
           → fst (P-𝟙 d b) → fst (P-𝟙 e (F₁ (𝟙 {C = C}) k b))
P-𝟙-closed d e k b pd = subst (λ z → fst (P z)) (sym k) pd

-- ------------------------------------------------------------
-- ci-Ω as a genuine internal morphism 𝟙 ⇒ Ω — a subobject of the
-- terminal presheaf, i.e. an internal truth value, classified by χ.
-- ------------------------------------------------------------
ci-Ω-nat : Nat (𝟙 {C = C}) (Ω {C = C})
ci-Ω-nat = χ (𝟙 {C = C}) P-𝟙 P-𝟙-closed

-- its regime-wise sieve
ci-sieve : (c : Ob) → Sieve {C = C} c
ci-sieve c = fst ci-Ω-nat c tt

-- ------------------------------------------------------------
-- STAGE 2 DELIVERABLE: ci-Ω is a natural transformation (subobject)
-- and it is still non-maximal at the `true` regime — a genuine,
-- classified, contingent truth value in Ω, not merely ⊤ everywhere.
-- ------------------------------------------------------------
ci-nat-non-maximal : Σ[ c ∈ Ob ] (¬ (ci-sieve c ≡ maximal {C = C} c))
ci-nat-non-maximal = true , λ eq → ¬P-true (maximal→mem {C = C} (ci-sieve true) eq true idn)
