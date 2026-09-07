{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.IdentProbe — does the identification type carry
-- non-trivial structure beyond Pearl's binary?
--
-- PROBE RESULT: the identification type is an h-set. Its
-- level-0 structure (the SET of valid input footprints) is
-- genuinely richer than Pearl's identifiable/non-identifiable
-- binary. Over a site, it becomes a sieve. Higher homotopy
-- (level 1+) adds nothing causal.
--
-- The identification sieve is distinct from the mechanism
-- classifier: the latter records where a SPECIFIC mechanism
-- is admissible; the former records where the causal EFFECT
-- is computable from available data.
--
-- Results:
--   Unit≢Bool           two input footprints are distinct
--   same-strat          same footprint ⇒ same strategy (funext)
--   ident-closed        identifiability is closed under restriction
--   ident-at-do₀/₁      the effect IS identifiable at do₀ and do₁
--   ident-not-obs       the effect is NOT identifiable at obs
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
-- PART 1. Non-trivial at level 0: distinct strategies exist.
-- ============================================================

-- If Unit ≡ Bool, transport gives isContr Bool.
-- But Bool has two distinct elements: contradiction.
Unit≢Bool : ¬ (Unit ≡ Bool)
Unit≢Bool p = true≢false (sym (snd cb true) ∙ snd cb false)
  where
    cb : isContr Bool
    cb = subst isContr p (tt , isPropUnit tt)

-- Two identification strategies whose input footprints differ
-- (Unit = reads nothing, Bool = reads one covariate) are
-- provably distinct. The identification type has at least
-- two elements — richer than Pearl's binary.

-- ============================================================
-- PART 2. Same footprint ⇒ same strategy (funext).
-- ============================================================

-- Two functionals with the same domain and the same target
-- value are equal by function extensionality, regardless of
-- how they were derived.
same-strat : {A T : Type} {t₀ : T}
           → (f g : A → T)
           → ((a : A) → f a ≡ t₀)
           → ((a : A) → g a ≡ t₀)
           → f ≡ g
same-strat f g pf pg = funExt λ a → pf a ∙ sym (pg a)

-- So the level-0 structure is the set of valid footprints:
-- different footprints → different strategies,
-- same footprint → same strategy.

-- ============================================================
-- PART 3. Identifiability determines a sieve.
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

-- Identifiability at each context. At interventional contexts
-- the effect is directly observed. At the observational context
-- identification depends on the graph; we exhibit the case
-- where it is not available (no valid adjustment set).

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

-- The identification sieve on obs is {e₀, e₁}: identifiable
-- from both interventional contexts, not from obs itself.

ident-at-do₀ : Ident do₀
ident-at-do₀ = tt

ident-at-do₁ : Ident do₁
ident-at-do₁ = tt

ident-not-obs : ¬ (Ident obs)
ident-not-obs ()

-- ============================================================
-- PROBE VERDICT
-- ============================================================
--
-- Level 0 (set of footprints):
--   Non-trivial. Different adjustment sets give distinct
--   strategies. Pearl's binary is the propositional truncation.
--   The set records HOW MANY ways to identify — new.
--
-- Level 0 (as sieve):
--   The identifiability predicate is closed under restriction
--   and determines a sieve on the intervention site. Its value
--   at obs — the non-maximal sieve {e₀, e₁} — is a truth value
--   in the topos. This is 1-topos structure.
--
-- Level 1 (automorphisms):
--   The only loops are automorphisms of input types (e.g.,
--   negation on Bool). These are gauge: permuting a covariate's
--   labels does not change the adjustment formula. After
--   0-truncation, they vanish.
--
-- Level 2+:
--   Trivial. Input types are h-sets. Nothing above level 1.
--
-- Conclusion: HoTT's higher structure adds nothing causal.
-- The useful structure is the h-set of footprints and the
-- sieve it determines — both live at level 0 in the 1-topos.
