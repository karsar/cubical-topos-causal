{-# OPTIONS --safe --cubical --guardedness #-}
-- ============================================================
-- Topos.ThreeSiteObstruction
--
-- Three sites, overlapping variables, pairwise consistent, and no
-- global dataset. The statement is about counts, so it tolerates
-- noise.
--
-- WHY THIS EXISTS
-- ===============
-- `Topos.Contextuality` in the companion development proves the
-- possibilistic version. Specker's triangle has three contexts, is
-- pairwise consistent, and has no global section, and
-- `Topos.Cohomology` computes its non-zero class in H¹. That
-- obstruction assumes perfect anti-correlation on every pair. Count
-- data never has that, so the argument does not apply to data.
--
-- The version here tolerates noise. Three sites each measure two of
-- three binary attributes and report a count table. The tables agree
-- on every shared margin, so every pairwise consistency check a
-- practitioner would run passes. No global dataset has those pairwise
-- tables. The reason is a counting identity, not a parity argument,
-- so the conclusion still holds away from the extreme: the tables
-- here disagree 18 times in 20, and not 20 in 20.
--
-- THE ARGUMENT
-- ============
-- In any global table over three binary attributes, each of the eight
-- cells has 0 or 2 disagreeing pairs, and never 1 or 3, because an
-- odd cycle of disequalities is unsatisfiable. Summing over cells,
--
--     dis(A,B) + dis(B,C) + dis(C,A) + 2 * (both-agree cells)
--       = 2 * total
--
-- exactly. The observed tables give 18 + 18 + 18 = 54 with total 20,
-- and 54 + 2k = 40 has no solution in the naturals.
--
-- WHERE THIS BELONGS
-- ==================
-- It was written in the follow-up development and moved here. It
-- belongs to this paper's obstruction thread, and not to the
-- follow-up paper's thesis about typed preconditions.
-- `Topos.Contextuality` and `Topos.Cohomology` are its immediate
-- neighbours, and it upgrades their possibilistic statement to one
-- that tolerates noise.
--
-- The identity in Section 2 is a sixteen-term commutative
-- rearrangement. `Cubical.Tactics.NatSolver` discharges it in one
-- line. By hand it takes a page of error-prone steps.
--
-- SCOPE AND LIMITS
-- ================
-- The module is a machine-checked demonstration of three things.
-- Pairwise consistency is strictly weaker than global consistency
-- for count data over overlapping variable sets. The gap holds away
-- from the noiseless extreme. Every margin check passes on data that
-- has no global model.
--
-- Both halves are checked, in Sections 4 to 9. Sections 1 to 3
-- constrain a global table by four numbers and refute it. On their
-- own they leave the load-bearing half asserted, because the
-- refutation matters only if compatible site tables carry those
-- numbers. Section 6 checks the compatibility, and Section 8 reaches
-- the contradiction from the tables rather than from the four
-- numbers.
--
-- Section 10 is the control. A refutation looks the same whether the
-- notion is unsatisfiable at these numbers or was mis-stated so that
-- nothing could inhabit it. So a realisable family is exhibited
-- against a witness.
--
-- The module is not a method. Deciding global consistency in general
-- is linear feasibility. Dropping the remainder from the identity
-- below leaves one facet of that polytope, singled out because this
-- example violates it. `Topos.CechCohomology` is the general
-- direction.
--
-- The module has no postulates and no holes.
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
-- The identity is stated as an equation. An equation is stronger
-- than the usual inequality form and needs no order relation on ℕ.
-- The three disagreement counts plus twice the all-agree cells equal
-- twice the total.
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
-- one half on trust: the numbers matter only if three compatible site
-- tables carry them. This section gives the tables, and Section 6
-- checks their compatibility.
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
-- Site AB measures (A,B), site BC measures (B,C), and site CA
-- measures (C,A). Consecutive sites share exactly one attribute, so
-- the three overlaps close a cycle. Each site reports 20 units, of
-- which 18 disagree.
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
-- Two sites overlap in one attribute. They agree when their margins
-- on it match. AB and BC share B, which is AB's second attribute and
-- BC's first. BC and CA share C. CA and AB share A. Every margin is
-- ten against ten, so every pairwise consistency check a practitioner
-- would run passes. Each equation below is machine-checked.
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
-- Section 8: no global table marginalises to the three tables.
--
-- This is Section 3's contradiction, reached from the tables instead
-- of from four assumed numbers. `Observed` becomes a consequence of
-- the tables.
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
-- The family is compatible (Section 6) and has no global table
-- (Section 8). So pairwise consistency is strictly weaker than global
-- consistency for count data over overlapping variable sets. The gap
-- is present at 18 disagreements in 20, and not only at the noiseless
-- 20 in 20.
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
-- Section 10: the control for Section 8.
--
-- `no-global-table` refutes `Marginalises`. A refutation looks the
-- same whether the notion is unsatisfiable at these numbers or was
-- mis-stated so that nothing could inhabit it. This section rules out
-- the second case: a family that is realisable and satisfies the same
-- record against a witness.
--
-- The control has twenty units. Ten agree on all three attributes and
-- ten disagree on none. It passes the same margin checks, and a
-- global table marginalises to it. So Section 8's emptiness comes
-- from the numbers 18 and 20 and not from the definitions.
-- ============================================================

agreeTable : Table
agreeTable = table 10 0 0 10

witness : Global
witness = global 10 0 0 0 0 0 0 10

-- the same compatibility checks pass here
control-compat-B : (sndT agreeTable ≡ fstT agreeTable)
                 × (sndF agreeTable ≡ fstF agreeTable)
control-compat-B = refl , refl

-- this family, unlike Section 8's, has a global table
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
