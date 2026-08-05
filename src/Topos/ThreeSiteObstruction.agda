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
-- Both halves are checked, which took Sections 4 to 9. Sections 1 to 3
-- constrain a global table by four numbers and refute it; on their own
-- they leave the load-bearing half asserted, since the refutation is
-- worth something only if compatible site tables carrying those
-- numbers exist. Section 6 checks the compatibility and Section 8
-- reaches the contradiction from the tables rather than from the four
-- numbers.
--
-- Section 10 is the control. A refutation looks the same whether the
-- notion is unsatisfiable at these numbers or was mis-stated so that
-- nothing could inhabit it, so a realisable family is exhibited
-- against a witness.
--
-- It is NOT a method. Deciding global consistency in general is
-- linear feasibility; dropping the remainder from the identity below
-- leaves one facet of that polytope, singled out because this example
-- violates it. `Topos.CechCohomology` is the general direction.
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
-- Section 2: the Bell-Boole identity, with its remainder written out.
--
-- Stated as an equation rather than an inequality, which is the
-- stronger statement and needs no order: the three disagreement counts
-- plus twice the all-agree cells is exactly twice the total.
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

-- ============================================================
-- Section 4: the site tables themselves.
--
-- Sections 1-3 constrain a global table by four numbers. That leaves
-- the interesting half on trust: the numbers are worth something only
-- if three compatible site tables actually carry them. So here are the
-- tables, and here is their compatibility, checked rather than
-- asserted.
--
-- A site sees two of the three attributes and reports a 2x2 count
-- table. `sDis` counts the units on which its two attributes differ.
-- ============================================================

record Table : Set where
  constructor table
  field
    tTT tTF tFT tFF : ℕ

open Table

sTotal : Table → ℕ
sTotal t = tTT t + tTF t + tFT t + tFF t

sDis : Table → ℕ
sDis t = tTF t + tFT t

-- the four one-variable margins of a site table
fstT fstF sndT sndF : Table → ℕ
fstT t = tTT t + tTF t
fstF t = tFT t + tFF t
sndT t = tTT t + tFT t
sndF t = tTF t + tFF t

-- ============================================================
-- Section 5: what the three sites report.
--
-- Site AB measures (A,B), site BC measures (B,C), site CA measures
-- (C,A), so consecutive sites share exactly one attribute and the
-- three overlaps close a cycle. Each reports 20 units of which 18
-- disagree.
-- ============================================================

tableAB tableBC tableCA : Table
tableAB = table 1 9 9 1
tableBC = table 1 9 9 1
tableCA = table 1 9 9 1

-- 18 disagreements in 20 units, at each site
disAB-18 : sDis tableAB ≡ 18
disAB-18 = refl

disBC-18 : sDis tableBC ≡ 18
disBC-18 = refl

disCA-18 : sDis tableCA ≡ 18
disCA-18 = refl

totalAB-20 : sTotal tableAB ≡ 20
totalAB-20 = refl

totalBC-20 : sTotal tableBC ≡ 20
totalBC-20 = refl

totalCA-20 : sTotal tableCA ≡ 20
totalCA-20 = refl

-- ============================================================
-- Section 6: the family is compatible.
--
-- Two sites overlap in one attribute, and agreement means their
-- margins on it match. AB and BC share B, which is AB's second and
-- BC's first; BC and CA share C; CA and AB share A. Ten against ten
-- everywhere, so every pairwise consistency check a practitioner would
-- run passes -- and each of these is a check, not a remark.
-- ============================================================

-- AB and BC agree on B
compat-B-T : sndT tableAB ≡ fstT tableBC
compat-B-T = refl

compat-B-F : sndF tableAB ≡ fstF tableBC
compat-B-F = refl

-- BC and CA agree on C
compat-C-T : sndT tableBC ≡ fstT tableCA
compat-C-T = refl

compat-C-F : sndF tableBC ≡ fstF tableCA
compat-C-F = refl

-- CA and AB agree on A
compat-A-T : sndT tableCA ≡ fstT tableAB
compat-A-T = refl

compat-A-F : sndF tableCA ≡ fstF tableAB
compat-A-F = refl

-- ============================================================
-- Section 7: marginalising a global table down to a site.
--
-- A global table over (A,B,C) induces one at each site by summing out
-- the attribute that site does not see.
-- ============================================================

margAB : Global → Table
margAB g = table (aTTT g + aTTF g) (aTFT g + aTFF g)
                 (aFTT g + aFTF g) (aFFT g + aFFF g)

margBC : Global → Table
margBC g = table (aTTT g + aFTT g) (aTTF g + aFTF g)
                 (aTFT g + aFFT g) (aTFF g + aFFF g)

margCA : Global → Table
margCA g = table (aTTT g + aTFT g) (aFTT g + aFFT g)
                 (aTTF g + aTFF g) (aFTF g + aFFF g)

-- the site-level counts of a marginal are the global ones of Section 1
sDis-margAB : (g : Global) → sDis (margAB g) ≡ disAB g
sDis-margAB (global a b c d e f h i) = solveℕ!

sDis-margBC : (g : Global) → sDis (margBC g) ≡ disBC g
sDis-margBC (global a b c d e f h i) = solveℕ!

sDis-margCA : (g : Global) → sDis (margCA g) ≡ disCA g
sDis-margCA (global a b c d e f h i) = solveℕ!

sTotal-margAB : (g : Global) → sTotal (margAB g) ≡ total g
sTotal-margAB (global a b c d e f h i) = solveℕ!

-- ============================================================
-- Section 8: the theorem the paragraph actually states.
--
-- No global table marginalises to the three reported tables. This is
-- Section 3's contradiction reached from the tables rather than from
-- four numbers taken on faith, so `Observed` is now derived and not
-- assumed.
-- ============================================================

record Marginalises (g : Global) : Set where
  field
    mAB : margAB g ≡ tableAB
    mBC : margBC g ≡ tableBC
    mCA : margCA g ≡ tableCA

open Marginalises

marginalises→observed : (g : Global) → Marginalises g → Observed g
marginalises→observed g m = record
  { obsAB = sym (sDis-margAB g) ∙ cong sDis (mAB m)
  ; obsBC = sym (sDis-margBC g) ∙ cong sDis (mBC m)
  ; obsCA = sym (sDis-margCA g) ∙ cong sDis (mCA m)
  ; obsN  = sym (sTotal-margAB g) ∙ cong sTotal (mAB m)
  }

no-global-table : (g : Global) → Marginalises g → ⊥
no-global-table g m = no-global g (marginalises→observed g m)

-- ============================================================
-- Section 9: the two halves together.
--
-- Compatible (Section 6) and unrealisable (Section 8). Pairwise
-- consistency is therefore strictly weaker than global consistency for
-- count data over overlapping variable sets, and it stays weaker at 18
-- in 20 rather than only at 20 in 20.
-- ============================================================

pairwise-consistent-and-globally-impossible :
    ((sndT tableAB ≡ fstT tableBC) × (sndF tableAB ≡ fstF tableBC))
  × ((sndT tableBC ≡ fstT tableCA) × (sndF tableBC ≡ fstF tableCA))
  × ((sndT tableCA ≡ fstT tableAB) × (sndF tableCA ≡ fstF tableAB))
  × ((g : Global) → Marginalises g → ⊥)
pairwise-consistent-and-globally-impossible =
  (compat-B-T , compat-B-F) ,
  (compat-C-T , compat-C-F) ,
  (compat-A-T , compat-A-F) ,
  no-global-table

-- ============================================================
-- Section 10: the control, without which Section 8 proves nothing.
--
-- `no-global-table` refutes `Marginalises`, and a refutation looks the
-- same whether the notion is genuinely unsatisfiable at these numbers
-- or unsatisfiable because it was mis-stated and nothing could ever
-- inhabit it. So: a family that IS realisable, satisfying the same
-- record against a witness.
--
-- Twenty units, ten agreeing on all three attributes and ten
-- disagreeing on none. Compatible by the same margin checks, and this
-- time a global table marginalises to it. Section 8's emptiness is
-- therefore about the numbers 18 and 20 and not about the definitions.
-- ============================================================

agreeTable : Table
agreeTable = table 10 0 0 10

witness : Global
witness = global 10 0 0 0 0 0 0 10

-- the same compatibility checks pass here
control-compat-B : (sndT agreeTable ≡ fstT agreeTable)
                 × (sndF agreeTable ≡ fstF agreeTable)
control-compat-B = refl , refl

-- and unlike Section 8, this family has a global table
control-AB : margAB witness ≡ agreeTable
control-AB = refl

control-BC : margBC witness ≡ agreeTable
control-BC = refl

control-CA : margCA witness ≡ agreeTable
control-CA = refl

-- with the right size, and no disagreement anywhere
control-total : sTotal (margAB witness) ≡ 20
control-total = refl

control-dis : sDis (margAB witness) ≡ 0
control-dis = refl
