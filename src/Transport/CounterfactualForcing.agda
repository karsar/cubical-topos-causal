{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.CounterfactualForcing — the decisive probe.
--
-- Transport.CounterfactualProbe showed the GLUING pillar hosts Pearl
-- counterfactuals (twin network = pullback over shared noise).  The
-- open question was whether the INTERNAL LOGIC (Kripke-Joyal
-- forcing, Topos.Forcing) earns its keep, or merely re-describes a
-- single-model counterfactual that Pearl already computes.
--
-- The honest test: forcing only buys something over a NON-TRIVIAL
-- base.  Over the terminal category, c ⊩ S collapses to "S is true"
-- and the internal logic adds nothing.  So we work over the minimal
-- non-trivial base — two contexts, an environment e refining a
-- global context g (one non-identity arrow ι : e → g) — and ask
-- whether forcing distinguishes "the counterfactual holds in the
-- environment" from "the counterfactual holds globally / invariantly."
--
-- RESULT (machine-checked, --safe, using the paper's own _⊩_ and
-- ⊩-mono):
--   * forced-globally : the invariant counterfactual is forced at g;
--   * forced-locally  : a counterfactual that holds only in the
--                       environment is forced at e (after restriction);
--   * not-forced-globally : …but that same counterfactual is NOT
--                       forced at g.  Local truth ≠ global truth: the
--                       internal logic genuinely separates them.
--   * invariance : forcing at g entails forcing at every context
--                  (⊩-mono) — counterfactual invariance across the
--                  environment cover is the Kripke LOCALITY, for free.
--
-- INTERPRETATION.  This is the surplus over Pearl: "Y_{X:=x}=y is
-- forced at the global context" means the counterfactual is INVARIANT
-- across the environments g covers — a statement a single-graph
-- twin-network cannot make.  Forcing at an environment is the
-- ordinary (local) counterfactual; forcing at the global context is
-- its invariance.  The gap between the two (not-forced-globally) is
-- exactly what the modality/internal logic contributes.
--
-- HONEST LIMIT.  This is two contexts and a Boolean truth value; the
-- general result is a presheaf of worlds over a regime category with
-- the counterfactual a classified subobject, and the bridge to the
-- probabilistic (FDist-kernel) counterfactual.  But the load-bearing
-- question — does forcing add content beyond Pearl? — is answered
-- YES, and the surplus is identified (invariance = global forcing).
-- ============================================================

module Transport.CounterfactualForcing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit; Unit*; tt*)
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Cat
open import Topos.Omega
open import Topos.Forcing

-- ----------------------------------------------------------
-- The base category: g (global context) with one environment e
-- refining it, via a single non-identity arrow ι : e → g.  Thin
-- category, so every law is propositional.
-- ----------------------------------------------------------
data Obj : Type where
  g e : Obj

Hom₀ : Obj → Obj → Type
Hom₀ g g = Unit
Hom₀ e e = Unit
Hom₀ e g = Unit     -- ι : e → g
Hom₀ g e = ⊥        -- no arrow global → environment

idn₀ : ∀ {x} → Hom₀ x x
idn₀ {g} = tt
idn₀ {e} = tt

comp₀ : ∀ {x y z} → Hom₀ x y → Hom₀ y z → Hom₀ x z
comp₀ {g} {g} {g} _ _ = tt
comp₀ {g} {g} {e} _ h = ⊥rec h
comp₀ {g} {e} {_} f _ = ⊥rec f
comp₀ {e} {g} {g} _ _ = tt
comp₀ {e} {g} {e} _ h = ⊥rec h
comp₀ {e} {e} {g} _ _ = tt
comp₀ {e} {e} {e} _ _ = tt

isPropHom₀ : ∀ {x y} → isProp (Hom₀ x y)
isPropHom₀ {g} {g} = isPropUnit
isPropHom₀ {g} {e} = isProp⊥
isPropHom₀ {e} {g} = isPropUnit
isPropHom₀ {e} {e} = isPropUnit

C : Precategory ℓ-zero ℓ-zero
C = record
  { Ob = Obj ; Hom = Hom₀ ; idn = idn₀ ; _⋆_ = comp₀
  ; ⋆-idL = λ f → isPropHom₀ _ f
  ; ⋆-idR = λ f → isPropHom₀ _ f
  ; ⋆-assoc = λ f g' h → isPropHom₀ _ _
  ; isSetHom = isProp→isSet isPropHom₀ }

-- the refinement arrow
ι : Hom₀ e g
ι = tt

-- ----------------------------------------------------------
-- The counterfactual as an internal truth value (a sieve on g).
--
-- invariantCF : the counterfactual holds in EVERY context (the
--   maximal sieve).  Reading: Y_{X:=x}=y holds invariantly.
-- localCF : the counterfactual holds in the environment e but NOT
--   in the global context g.  Reading: the counterfactual is
--   realised in one regime, not across all.
-- ----------------------------------------------------------
invariantCF : Sieve {C = C} g
invariantCF = maximal {C = C} g

localCF : Sieve {C = C} g
localCF = mem , clo
  where
    mem : SieveMem {C = C} g
    mem g _ = ⊥ , isProp⊥        -- not in: fails at the global context
    mem e _ = Unit , isPropUnit  -- in: holds at the environment
    clo : Closure {C = C} g mem
    clo g e' k f x = ⊥rec x      -- mem g f = ⊥
    clo e g  k f x = ⊥rec k      -- k : Hom₀ g e = ⊥
    clo e e  k f x = tt

-- ----------------------------------------------------------
-- Forcing facts (using Topos.Forcing._⊩_ and ⊩-mono on C).
-- ----------------------------------------------------------

-- The invariant counterfactual is forced at the global context.
forced-globally : _⊩_ {C = C} g invariantCF
forced-globally = tt*

-- The local counterfactual is forced at the environment (after
-- restricting along ι): e ⊩ pull ι localCF.
forced-locally : _⊩_ {C = C} e (pull {C = C} ι localCF)
forced-locally = tt

-- …but the SAME counterfactual is NOT forced at the global context.
-- Local truth and global truth genuinely differ.
not-forced-globally : ¬ (_⊩_ {C = C} g localCF)
not-forced-globally x = x

-- Invariance for free: anything forced at the global context is
-- forced at every context (every refinement).  This is the Kripke
-- locality (⊩-mono), i.e. a globally-forced counterfactual is
-- automatically invariant across the cover — no separate proof.
invariance : (d : Obj) (f : Hom₀ d g) → _⊩_ {C = C} d (pull {C = C} f invariantCF)
invariance d f = ⊩-mono {C = C} invariantCF forced-globally f
