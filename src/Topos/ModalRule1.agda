{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.ModalRule1 — Stage 2 (c): a do-calculus rule made modal.
--
-- Pearl Rule 1 (Topos.Rule1) says do(X := x₀) leaves the internal
-- Y-marginal invariant under structural independence.  Here we
-- INTERNALISE that conclusion as a truth value in Ω and show it is
-- ◯-modal — j-closed for EVERY Lawvere–Tierney topology j.
--
-- That is the j-do-calculus claim (translation.md:25, j = lex
-- modality ◯) made concrete: Rule 1 is valid in the internal logic
-- of every sheaf subtopos, so it survives sheafification /
-- localization to any modality.  Unlike do-j-stable (which is about
-- the INTERVENTION classifier), this is about a do-calculus RULE's
-- conclusion — and the proof genuinely runs through rule1-E, the
-- causal content, not just ⊤.
-- ============================================================

module Topos.ModalRule1 where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)

open import FDist-Convex using (mapF; trunc)
open import RuleDoCalc   using (joint-of; do-X)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.SCM
open import Topos.Rule1
open import Topos.LawvereTierney
open LawvereTierney

module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C
  open PSh

  -- ----------------------------------------------------------
  -- Embed a truth value into Ω: the sieve whose membership is the
  -- constant prop P.  It is maximal exactly when P holds.
  -- ----------------------------------------------------------
  prop→sieve : (c : Ob) → hProp ℓ → Sieve {C = C} c
  prop→sieve c P = (λ d f → P) , (λ d e k f p → p)

  prop→sieve-true : (c : Ob) (P : hProp ℓ) → fst P
                  → prop→sieve c P ≡ maximal {C = C} c
  prop→sieve-true c P p =
    Sieve≡ {C = C} (prop→sieve c P) (maximal {C = C} c)
      (funExt λ d → funExt λ f →
        ⇔toPath {P = P} {Q = Unit* , isPropUnit*} (λ _ → tt*) (λ _ → p))

-- ----------------------------------------------------------
-- Modal Rule 1, for a fixed internal SCM m with Y ⫫ X.
-- ----------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} (X Y : PSh C ℓ)
         (m : SCM-E {C = C} X Y) (ind : Indep-E {C = C} {X = X} {Y = Y} m)
         (x₀ : (c : Precategory.Ob C) → PSh.F₀ X c) where
  open Precategory C
  open PSh

  -- internalised Rule-1 conclusion at regime c, as a truth value
  -- (FDist is a set, so the marginal equality is a proposition)
  rule1-prop : (c : Ob) → hProp ℓ
  rule1-prop c =
    (mapF snd (joint-of (do-X (x₀ c) (m c))) ≡ mapF snd (joint-of (m c)))
    , trunc _ _

  -- Rule 1 internalised as an element of Ω
  rule1-Ω : (c : Ob) → Sieve {C = C} c
  rule1-Ω c = prop→sieve {C = C} c (rule1-prop c)

  -- it collapses to ⊤, because Rule 1 holds (rule1-E)
  rule1-Ω-true : (c : Ob) → rule1-Ω c ≡ maximal {C = C} c
  rule1-Ω-true c =
    prop→sieve-true {C = C} c (rule1-prop c)
      (rule1-E {C = C} {X = X} {Y = Y} m ind x₀ c)

  -- HEADLINE: internalised Rule 1 is ◯-modal (j-closed) for every
  -- Lawvere–Tierney topology — j-do-calculus for Rule 1.
  modal-rule1 : (J : LawvereTierney {C = C}) (c : Ob)
              → is-j-closed J c (rule1-Ω c)
  modal-rule1 J c =
    cong (jop J c) e ∙ j-⊤ J c ∙ sym e
    where
      e : rule1-Ω c ≡ maximal {C = C} c
      e = rule1-Ω-true c
