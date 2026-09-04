{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.CIObject — Stage 2 of the modal-layer repair: the
-- contingent CI as a SUBOBJECT, that is, as a natural
-- transformation into Ω, with restriction-stability proved.
--
-- Topos.ContingentCI packaged the contingent claim regime by
-- regime, as `ci-Ω c = prop→sieve c (P c)`.  Here it becomes one
-- internal morphism `ci-Ω-nat : 𝟙 ⇒ Ω`.  That morphism comes from
-- the universal property of Ω (Topos.Classifier.χ).  It is a
-- subobject of the terminal presheaf, that is, an internal truth
-- value.  The classifier takes the arrow-indexed family "the
-- claim holds after restriction along f" to the sieve
-- χ_c(*) = { f : d → c | P holds at d }.  The obligation
-- `P-closed` is Mahadevan's "refinement preserves the claim", and
-- it is discharged for this base.
--
-- SCOPE.  The base here is the discrete category on two regimes.
-- Its morphisms are equalities, so `P-closed` holds by transport.
-- This is weaker than the statement "conditioning preserves
-- conditional independence", which is where the content and a
-- real obstruction lie.  For a COLLIDER, conditioning on the
-- collider vertex OPENS the path, so CI is NOT preserved under
-- that refinement (Berkson's paradox).  So `ci-Ω` is a sieve only
-- when refinement is restricted to conditioning that preserves
-- CI.  The collider is a counterexample to restriction-stability
-- without that restriction.  A precise treatment needs Bayesian
-- conditioning on the convex-HIT and the general d-separation
-- soundness theorem.  Both are future work; see
-- Topos.ContingentCI and the companion d-separation layer.
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
-- restriction-stability.  On the discrete base a morphism
-- k : e → d is an equality e ≡ d, so the claim transports along
-- it.
-- ------------------------------------------------------------
P-𝟙 : (c : Ob) → F₀ (𝟙 {C = C}) c → hProp ℓ-zero
P-𝟙 c _ = P c

P-𝟙-closed : (d e : Ob) (k : Hom e d) (b : F₀ (𝟙 {C = C}) d)
           → fst (P-𝟙 d b) → fst (P-𝟙 e (F₁ (𝟙 {C = C}) k b))
P-𝟙-closed d e k b pd = subst (λ z → fst (P z)) (sym k) pd

-- ------------------------------------------------------------
-- ci-Ω as an internal morphism 𝟙 ⇒ Ω.  It is a subobject of the
-- terminal presheaf, that is, an internal truth value, and χ
-- classifies it.
-- ------------------------------------------------------------
ci-Ω-nat : Nat (𝟙 {C = C}) (Ω {C = C})
ci-Ω-nat = χ (𝟙 {C = C}) P-𝟙 P-𝟙-closed

-- its regime-wise sieve
ci-sieve : (c : Ob) → Sieve {C = C} c
ci-sieve c = fst ci-Ω-nat c tt

-- ------------------------------------------------------------
-- STAGE 2 DELIVERABLE: ci-Ω is a natural transformation, so it is
-- a subobject, and it is still not maximal at the `true` regime.
-- It is a classified contingent truth value in Ω, rather than ⊤
-- at every regime.
-- ------------------------------------------------------------
ci-nat-non-maximal : Σ[ c ∈ Ob ] (¬ (ci-sieve c ≡ maximal {C = C} c))
ci-nat-non-maximal = true , λ eq → ¬P-true (maximal→mem {C = C} (ci-sieve true) eq true idn)
