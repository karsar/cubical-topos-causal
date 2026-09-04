{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportModal — transportability is the invariance
-- modality.
--
-- The modal layer of the paper (Topos.LawvereTierney,
-- InterventionModal, ModalRules) proves that interventions and
-- Pearl's rules are j-CLOSED for EVERY Lawvere-Tierney topology.
-- j-closed means invariant under the localization that the topology
-- defines.  One mechanism does the work there: the truth value of
-- the statement is the maximal sieve ⊤, and ⊤ is j-closed for every
-- topology (⊤-j-closed = j-⊤).
--
-- The transportability story (Transport.Transportability) reaches
-- the same point.  A counterfactual is TRANSPORTABLE to the global
-- context when it is forced there.  This module shows that in that
-- case its internal truth value is the maximal sieve ⊤.  By the
-- paper's own ⊤-j-closed it is then j-closed for every topology,
-- that is, invariant under every localization.
--
--   transportable→⊤-gen        : forced at the global context gives
--                                truth value ⊤, for ANY R : RegPred.
--   transportable→invariant-gen: hence j-closed for EVERY topology J,
--                                by the same ⊤-collapse that the
--                                paper's do-j-stable and modal-rules
--                                use.
--   transportable→⊤, transportable→invariant: the scmPred instances.
--
-- Both general forms quantify over the regime predicate.  The base
-- category of regimes is still the fixed two-object one of
-- Transport.CounterfactualForcing.
--
-- The reading: transportability, j-stability and invariance coincide
-- here.  The modality the paper studies for interventions is, for
-- counterfactuals, transportability.  A counterfactual that holds
-- only in an environment does not transport.  Its truth value is
-- then below ⊤, so it is not j-closed for the regime topology, and
-- it is not yet invariant.
--
-- STILL OPEN (unchanged): the equivalence with the Bareinboim-Pearl
-- s-hedge criterion, and the probabilistic case.  This module gives
-- the bridge to the paper's modal layer.  It does not give that
-- equivalence.
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
