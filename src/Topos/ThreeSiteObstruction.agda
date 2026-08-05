{-# OPTIONS --cubical --guardedness #-}
-- ============================================================
-- Topos.ThreeSiteObstruction
--
-- Three sites, overlapping variables, pairwise consistent, and no
-- global dataset. On counts, so it survives noise.
--
-- WHY THIS EXISTS
-- ===============
-- `Topos.Contextuality` in the companion development proves the
-- possibilistic version: Specker's triangle, three contexts,
-- pairwise consistent, no global section, with `Topos.Cohomology`
-- computing the non-zero class in H¹. That obstruction needs PERFECT
-- anti-correlation on every pair, which no dataset exhibits, so it
-- says nothing about data.
--
-- This is the noise-tolerant version, and it is the one that could be
-- used. Three sites each measure two of three binary attributes and
-- report a COUNT TABLE. The tables agree on every shared margin, so
-- every pairwise consistency check a practitioner would run passes.
-- No global dataset has those pairwise tables, and the reason is an
-- inequality rather than a parity argument, so it degrades
-- gracefully: the tables here disagree 18 times in 20 rather than 20
-- in 20.
--
-- THE ARGUMENT
-- ============
-- In any global table over three binary attributes, each of the eight
-- cells has 0 or 2 disagreeing PAIRS, never 1 or 3, because an odd
-- cycle of disequalities is unsatisfiable. Summing over cells,
--
--     dis(A,B) + dis(B,C) + dis(C,A) + 2 * (both-agree cells)
--       = 2 * total
--
-- exactly. The observed tables give 18 + 18 + 18 = 54 with total 20,
-- and 54 + something = 40 has no solution.
--
-- WHERE THIS BELONGS
-- ==================
-- It was written in the follow-up development and moved here, because
-- it continues THIS paper's obstruction rather than that paper's
-- thesis about typed preconditions. `Topos.Contextuality` and
-- `Topos.Cohomology` are its immediate neighbours and it upgrades
-- them from a possibilistic statement to one that survives noise.
--
-- The identity in Section 2 is a sixteen-term commutative
-- rearrangement, which `Cubical.Tactics.NatSolver` discharges in one
-- line and which is a page of error-prone steps by hand.
--
-- WHAT THIS IS AND IS NOT
-- =======================
-- It IS a machine-checked demonstration that pairwise consistency is
-- strictly weaker than global consistency for count data over
-- overlapping variable sets, that the gap survives noise, and that
-- every margin check passes on data having no global model.
--
-- It is NOT a method. Deciding global consistency in general is
-- linear feasibility, and the inequality here is one facet of that
-- polytope, chosen because this example violates it.
-- `Topos.CechCohomology` is the general direction.
--
-- Zero postulates, zero holes.
-- ============================================================

module Topos.ThreeSiteObstruction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import Cubical.Data.Nat.Properties using (snotz; inj-m+; +-zero)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Tactics.NatSolver

-- ============================================================
-- Section 1: a global table over three binary attributes.
-- ============================================================

record Global : Set where
  constructor global
  field
    aTTT aTTF aTFT aTFF aFTT aFTF aFFT aFFF : ℕ

open Global

total : Global → ℕ
total g = aTTT g + aTTF g + aTFT g + aTFF g
        + aFTT g + aFTF g + aFFT g + aFFF g

-- pairwise disagreement counts, read off the global table
disAB : Global → ℕ
disAB g = aTFT g + aTFF g + aFTT g + aFTF g

disBC : Global → ℕ
disBC g = aTTF g + aTFT g + aFTF g + aFFT g

disCA : Global → ℕ
disCA g = aTTF g + aFTT g + aTFF g + aFFT g

-- the cells on which all three agree
allAgree : Global → ℕ
allAgree g = aTTT g + aFFF g

-- ============================================================
-- Section 2: the Bell-Boole identity, with its slack exhibited.
--
-- Stated as an equation rather than an inequality, which is stronger
-- and needs no order: the three disagreement counts plus twice the
-- all-agree cells is exactly twice the total.
-- ============================================================

bell : (g : Global)
     → (disAB g + disBC g + disCA g) + 2 · allAgree g ≡ 2 · total g
bell (global a b c d e f h i) = solveℕ!

-- ============================================================
-- Section 3: the observed data, and the contradiction.
--
-- Each site reports 20 units with 18 disagreements: cells (T,F) and
-- (F,T) at 9 each, (T,T) and (F,F) at 1 each. Every shared margin is
-- 10 against 10, so pairwise consistency holds at every overlap.
-- ============================================================

record Observed (g : Global) : Set where
  field
    obsAB : disAB g ≡ 18
    obsBC : disBC g ≡ 18
    obsCA : disCA g ≡ 18
    obsN  : total g ≡ 20

open Observed

-- 54 + 2k = 40 has no solution in the naturals
split : (k : ℕ) → 54 + 2 · k ≡ 40 + (14 + 2 · k)
split k = solveℕ!

no-solution : (k : ℕ) → ¬ (54 + 2 · k ≡ 40)
no-solution k q =
  snotz (inj-m+ (sym (split k) ∙ q ∙ sym (+-zero 40)))

no-global : (g : Global) → Observed g → ⊥
no-global g o = no-solution (allAgree g) step
  where
    sum54 : disAB g + disBC g + disCA g ≡ 54
    sum54 = cong₂ _+_ (cong₂ _+_ (obsAB o) (obsBC o)) (obsCA o)

    step : 54 + 2 · allAgree g ≡ 40
    step = cong (λ z → z + 2 · allAgree g) (sym sum54)
         ∙ bell g
         ∙ cong (λ z → 2 · z) (obsN o)
