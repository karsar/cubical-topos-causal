{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.CounterfactualForcing — the decisive probe.
--
-- Transport.CounterfactualProbe shows that the GLUING pillar hosts
-- Pearl counterfactuals: a twin network is a pullback over shared
-- noise.  The open question was whether the INTERNAL LOGIC
-- (Kripke-Joyal forcing, Topos.Forcing) adds content, or only
-- re-describes a single-model counterfactual that Pearl already
-- computes.
--
-- Forcing can add something only over a NON-TRIVIAL base.  Over the
-- terminal category, c ⊩ S reduces to "S is true", and the internal
-- logic contributes nothing.  So we work over the minimal
-- non-trivial base: two contexts, an environment e refining a global
-- context g, with one non-identity arrow ι : e → g.  The question is
-- whether forcing separates "the counterfactual holds in the
-- environment" from "the counterfactual holds globally, that is,
-- invariantly".
--
-- RESULT (machine-checked, --safe, using the paper's own _⊩_ and
-- ⊩-mono):
--   * forced-globally : the invariant counterfactual is forced at g;
--   * forced-locally  : a counterfactual that holds only in the
--                       environment is forced at e, after
--                       restriction;
--   * not-forced-globally : that same counterfactual is NOT forced
--                       at g.  Local truth and global truth differ,
--                       and the internal logic separates them.
--   * invariance : forcing at g gives forcing at every context, by
--                  ⊩-mono.  Invariance of a counterfactual across
--                  the environment cover is Kripke LOCALITY, and it
--                  needs no separate proof.
--
-- INTERPRETATION.  This is the surplus over Pearl.  "Y_{X:=x}=y is
-- forced at the global context" says the counterfactual is INVARIANT
-- across the environments that g covers, and a single-graph twin
-- network cannot say that.  Forcing at an environment is the
-- ordinary local counterfactual.  Forcing at the global context is
-- its invariance.  The gap between the two, recorded in
-- not-forced-globally, is what the modality and the internal logic
-- contribute.
--
-- HONEST LIMIT.  This module has two contexts and a Boolean truth
-- value.  The general result needs a presheaf of worlds over a
-- regime category, with the counterfactual a classified subobject,
-- together with a bridge to the probabilistic (FDist-kernel)
-- counterfactual.  The load-bearing question here is narrower: does
-- forcing add content beyond Pearl?  The answer is yes, and the
-- surplus is invariance, which is global forcing.
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
-- The base category has a global context g and one environment e
-- that refines it, along a single non-identity arrow ι : e → g.  The
-- category is thin, that is, it has at most one arrow between any
-- two objects, so every law is propositional.
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
-- The counterfactual as an internal truth value, that is, a sieve
-- on g.
--
-- invariantCF : the counterfactual holds in EVERY context, so the
--   sieve is the maximal one.  Read it as: Y_{X:=x}=y holds
--   invariantly.
-- localCF : the counterfactual holds in the environment e and fails
--   in the global context g.  Read it as: the counterfactual is
--   realised in one regime and not across all of them.
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

-- The local counterfactual is forced at the environment, after
-- restricting along ι: e ⊩ pull ι localCF.
forced-locally : _⊩_ {C = C} e (pull {C = C} ι localCF)
forced-locally = tt

-- The SAME counterfactual is NOT forced at the global context.
-- Local truth and global truth differ.
not-forced-globally : ¬ (_⊩_ {C = C} g localCF)
not-forced-globally x = x

-- Anything forced at the global context is forced at every context,
-- that is, at every refinement.  This is the Kripke locality
-- (⊩-mono).  A globally-forced counterfactual is therefore invariant
-- across the cover, with no separate proof.
invariance : (d : Obj) (f : Hom₀ d g) → _⊩_ {C = C} d (pull {C = C} f invariantCF)
invariance d f = ⊩-mono {C = C} invariantCF forced-globally f
