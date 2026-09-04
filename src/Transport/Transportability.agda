{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.Transportability — from witness to theorem.
--
-- The weld (Transport.CounterfactualWeld) shows, for two specific
-- worlds, that forcing the computed counterfactual at the global
-- context is transportability.  This module upgrades that twice:
--
--   1.  The counterfactual becomes a proper internal predicate
--       χ : W ⇒ Ω over a presheaf W of worlds.  That is a natural
--       transformation, so a classified subobject, and naturality is
--       PROVED.  The weld gave only one sieve per world.
--
--   2.  The transport result is stated for all predicates instead of
--       for a pair of witnesses:
--         global-transport→everywhere :
--           for ANY restriction-stable regime predicate, if the
--           counterfactual transports to the global context then it
--           transports to every regime the context covers.
--       The hypothesis, restriction-stability, is the sieve closure
--       condition.  Causally it says a globally-true counterfactual
--       is locally true.  A predicate that fails it has no internal
--       truth value at all, and that failure is the obstruction to
--       transportability inside the internal logic.
--
-- We then instantiate at the SCM counterfactual of the weld,
-- do(X:=true) with query Y=true.  The transportable world and the
-- non-transportable world come back as corollaries of the general
-- theorem.
--
-- HONEST LIMITS (unchanged from the weld).  The model is
-- deterministic.  The regime category is finite.  Worlds are the
-- shared exogenous noise.  "Transport" here is the internal notion,
-- forcing at a context.  It is NOT yet proved equivalent to the
-- Bareinboim-Pearl s-hedge criterion; that equivalence and the
-- probabilistic (FDist-kernel) case are the remaining theory.  What
-- this module adds over the weld: the predicate is a genuine
-- W ⇒ Ω, and transport-invariance holds for a class of models.
-- ============================================================

module Transport.Transportability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isSet×)
open import Cubical.Data.Bool using (Bool; true; false; not; isSetBool; false≢true)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty using () renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Forcing

open import Transport.CounterfactualForcing using (Obj; g; e; Hom₀; ι; C)
open import Transport.CounterfactualProbe using (U)
open import Transport.CounterfactualWeld using (cfoG; cfoE; andb-R)

open PSh

-- ----------------------------------------------------------
-- The presheaf of worlds.  A world is the shared exogenous noise of
-- the twin network.  It is the same in every regime, so restriction
-- is the identity.
-- ----------------------------------------------------------
W : PSh C ℓ-zero
W = record
  { F₀ = λ _ → U
  ; F₁ = λ _ a → a
  ; F-id = λ _ → refl
  ; F-comp = λ _ _ _ → refl
  ; isSetF₀ = λ _ → isSet× isSetBool isSetBool }

-- ----------------------------------------------------------
-- A regime predicate says "the counterfactual holds at regime c and
-- world u".  It is prop-valued and RESTRICTION-STABLE: if it holds
-- at c and there is an arrow d → c, then it holds at d.  Stability
-- is what makes the predicate a sieve.
-- ----------------------------------------------------------
record RegPred : Type₁ where
  field
    P       : Obj → U → Type
    isPropP : (c : Obj) (u : U) → isProp (P c u)
    stable  : (c d : Obj) (k : Hom₀ d c) (u : U) → P c u → P d u

-- ----------------------------------------------------------
-- Every restriction-stable regime predicate gives a genuine internal
-- predicate χ : W ⇒ Ω.  Naturality is proved.  It holds because
-- sieve membership reads only the source regime.
-- ----------------------------------------------------------
χ : (R : RegPred) → Nat W Ω
χ R = α , nat
  where
    open RegPred R
    α : (c : Obj) → U → Sieve {C = C} c
    α c u = (λ d h → P d u , isPropP d u) , (λ d e' k f pf → stable d e' k u pf)
    nat : IsNat W Ω α
    nat x y f u = Sieve≡ {C = C} (α x u) (pull {C = C} f (α y u)) refl

-- The counterfactual TRANSPORTS to regime c at world u exactly when
-- it is forced there, that is, when c ⊩ S for S the sieve component
-- of χ at c and u.
transports-to : RegPred → Obj → U → Type
transports-to R c u = _⊩_ {C = C} c (fst (χ R) c u)

-- Forcing the predicate at a regime is the predicate holding there.
-- The two are definitionally equal: forcing is the per-regime truth.
forced→holds : (R : RegPred) (c : Obj) (u : U)
             → transports-to R c u → RegPred.P R c u
forced→holds R c u h = h
holds→forced : (R : RegPred) (c : Obj) (u : U)
             → RegPred.P R c u → transports-to R c u
holds→forced R c u h = h

-- THE GENERAL THEOREM.  If the counterfactual transports to the
-- global context, it transports to every regime that context covers.
-- This is locality in the internal logic, where sieve closure is
-- restriction-stability.  A single causal graph has no way to state
-- it.
global-transport→everywhere :
    (R : RegPred) (u : U)
  → transports-to R g u → (d : Obj) → transports-to R d u
global-transport→everywhere R u tg g = tg
global-transport→everywhere R u tg e = RegPred.stable R g e ι u tg

-- ----------------------------------------------------------
-- Instantiation at the SCM counterfactual of the weld: do(X:=true)
-- with query Y=true.  cfoG and cfoE are its global outcome and its
-- environment outcome.  Restriction-stability is andb-R.
-- ----------------------------------------------------------
cfo : Obj → U → Bool
cfo g u = cfoG u
cfo e u = cfoE u

scmPred : RegPred
RegPred.P scmPred c u = cfo c u ≡ true
RegPred.isPropP scmPred c u = isSetBool (cfo c u) true
RegPred.stable scmPred g g k u p = p
RegPred.stable scmPred g e k u p = andb-R (fst u) (not (snd u)) p
RegPred.stable scmPred e g k u p = ⊥rec k
RegPred.stable scmPred e e k u p = p

-- Transport-invariance for the SCM counterfactual, as a corollary.
scm-transport-invariance :
    (u : U) → transports-to scmPred g u → (d : Obj) → transports-to scmPred d u
scm-transport-invariance = global-transport→everywhere scmPred

-- The two worlds of the weld, recovered as instances.
scm-transportable : transports-to scmPred g (true , false)
scm-transportable = refl

scm-local : transports-to scmPred e (false , false)
scm-local = refl

scm-not-transportable : ¬ (transports-to scmPred g (false , false))
scm-not-transportable p = false≢true p
