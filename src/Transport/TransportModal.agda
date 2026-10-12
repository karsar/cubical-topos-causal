{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportModal: a transported counterfactual is
-- j-closed for every topology.
--
-- A counterfactual is TRANSPORTABLE to the global context g when
-- it is forced there.  This module shows that its truth value is
-- then the maximal sieve ⊤.  The paper's ⊤-j-closed then makes it
-- j-closed for every Lawvere-Tierney topology.  This is the same
-- collapse to ⊤ that do-j-stable and the modal rules use.
--
-- The theorem names contain "invariant".  Here that word means
-- j-closed.  It does not mean that a causal effect takes the same
-- value in every regime.
--
-- This is one direction only.  The converse needs more than
-- closedness: the closure must also be forced.
-- Transport.TransportDescent proves that equivalence for every
-- base and topology.  Transport.TransportSoundness proves the
-- two-regime instance, with local truth, and shows that local
-- truth cannot be dropped.
--
-- Results:
--   transportable→⊤-gen          forced at g gives truth value ⊤,
--                                for ANY R : RegPred.
--   transportable→invariant-gen  hence j-closed for EVERY J.
--   transportable→⊤, transportable→invariant
--                                the scmPred instances.
--
-- The base category of regimes is the fixed two-object one of
-- Transport.CounterfactualForcing.  The equivalence with the
-- Bareinboim-Pearl s-hedge criterion is not proved here.
-- ============================================================

module Transport.TransportModal where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Forcing
open import Topos.LawvereTierney

open import Transport.CounterfactualForcing using (Obj; g; e; ι; C)
open import Transport.CounterfactualProbe using (U)
open import Transport.Transportability using (χ; scmPred; transports-to; RegPred)

-- ----------------------------------------------------------
-- A transported counterfactual has truth value ⊤, the maximal sieve.
-- Both regimes satisfy it.  Regime g satisfies it by the forcing
-- hypothesis.  Regime e satisfies it by restriction-stability, which
-- is the sieve closure condition.
-- ----------------------------------------------------------
-- The general form takes ANY restriction-stable regime predicate,
-- not only scmPred.  The proof uses RegPred.stable and
-- RegPred.isPropP and nothing else.
transportable→⊤-gen : (R : RegPred) (u : U) → transports-to R g u
                    → fst (χ R) g u ≡ maximal {C = C} g
transportable→⊤-gen R u t =
  Sieve≡ {C = C} (fst (χ R) g u) (maximal {C = C} g)
    (funExt λ d → funExt λ h → inhab d)
  where
    inhab : (d : Obj)
          → (RegPred.P R d u , RegPred.isPropP R d u) ≡ (Unit* , isPropUnit*)
    inhab g = ⇔toPath (λ _ → tt*) (λ _ → t)
    inhab e = ⇔toPath (λ _ → tt*) (λ _ → RegPred.stable R g e ι u t)

transportable→⊤ : (u : U) → transports-to scmPred g u
                → fst (χ scmPred) g u ≡ maximal {C = C} g
transportable→⊤ = transportable→⊤-gen scmPred

-- ----------------------------------------------------------
-- Transportability therefore gives invariance.  A transported
-- counterfactual is j-closed for EVERY Lawvere-Tierney topology, by
-- the paper's ⊤-j-closed.  This is the collapse to ⊤ that
-- do-j-stable also uses.
-- ----------------------------------------------------------
transportable→invariant-gen :
    (R : RegPred) (u : U) → transports-to R g u
  → (J : LawvereTierney {C = C}) → is-j-closed J g (fst (χ R) g u)
transportable→invariant-gen R u t J =
  subst (λ S → is-j-closed J g S) (sym (transportable→⊤-gen R u t)) (⊤-j-closed J g)

transportable→invariant :
    (u : U) → transports-to scmPred g u
  → (J : LawvereTierney {C = C}) → is-j-closed J g (fst (χ scmPred) g u)
transportable→invariant = transportable→invariant-gen scmPred
