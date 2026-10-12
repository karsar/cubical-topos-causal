{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.IdentProbe: an elementary probe of the identification
-- type.
--
-- This is the first, elementary version of the identification
-- development.  The paper's results are in Topos.Identification,
-- Topos.IdentificationModels and Topos.IdentificationSieve.  This
-- module is kept because earlier versions of the paper cite it.
--
-- Its three parts prove less than their names suggest:
--   Unit≢Bool      distinguishes two TYPES.  It does not build two
--                  correct causal strategies.
--   same-strat     proves two functions equal when BOTH are
--                  assumed equal to one constant t₀ at every input.
--                  The constant is a hypothesis, not a result.
--   Ident          is a family we stipulate by cases.  No model
--                  or data determines its values.
--
-- Results:
--   Unit≢Bool           the types Unit and Bool are distinct.
--   same-strat          two functions with the same constant values
--                       are equal (funext).
--   ident-closed        the stipulated family is closed under
--                       restriction.
--   ident-at-do₀/₁      it is inhabited at do₀ and do₁.
--   ident-not-obs       it is empty at obs.
-- ============================================================

module Topos.IdentProbe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)

-- ============================================================
-- PART 1. Two distinct types.
-- ============================================================

-- If Unit ≡ Bool, transport gives isContr Bool.
-- But Bool has two distinct elements.  This is a contradiction.
Unit≢Bool : ¬ (Unit ≡ Bool)
Unit≢Bool p = true≢false (sym (snd cb true) ∙ snd cb false)
  where
    cb : isContr Bool
    cb = subst isContr p (tt , isPropUnit tt)


-- ============================================================
-- PART 2. Functions with the same constant values are equal.
-- ============================================================

-- Both functions are assumed equal to t₀ at every input.
-- Function extensionality then makes them equal.
same-strat : {A T : Type} {t₀ : T}
           → (f g : A → T)
           → ((a : A) → f a ≡ t₀)
           → ((a : A) → g a ≡ t₀)
           → f ≡ g
same-strat f g pf pg = funExt λ a → pf a ∙ sym (pg a)


-- ============================================================
-- PART 3. A stipulated family over the intervention site.
-- ============================================================

-- The intervention site (mirrors Topos.InterventionSite).
data Ctx : Type where
  obs do₀ do₁ : Ctx

data Arr : Ctx → Ctx → Type where
  idO : Arr obs obs
  id0 : Arr do₀ do₀
  id1 : Arr do₁ do₁
  e₀  : Arr do₀ obs
  e₁  : Arr do₁ obs


-- The values below are chosen by cases.  Topos.IdentificationModels
-- computes the same pattern from two causal models.
Ident : Ctx → Type
Ident obs = ⊥
Ident do₀ = Unit
Ident do₁ = Unit

isPropIdent : (c : Ctx) → isProp (Ident c)
isPropIdent obs = isProp⊥
isPropIdent do₀ = isPropUnit
isPropIdent do₁ = isPropUnit

-- Closure under restriction: the sieve condition.
ident-closed : {c d : Ctx} → Arr d c → Ident c → Ident d
ident-closed idO ()
ident-closed e₀  ()
ident-closed e₁  ()
ident-closed id0 h = h
ident-closed id1 h = h


ident-at-do₀ : Ident do₀
ident-at-do₀ = tt

ident-at-do₁ : Ident do₁
ident-at-do₁ = tt

ident-not-obs : ¬ (Ident obs)
ident-not-obs ()
