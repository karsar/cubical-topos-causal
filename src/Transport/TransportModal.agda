{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportModal — transportability IS the invariance
-- modality.  The conceptual unification.
--
-- The paper's modal layer (Topos.LawvereTierney, InterventionModal,
-- ModalRules) proves that interventions and Pearl's rules are
-- j-CLOSED for EVERY Lawvere-Tierney topology — invariant under every
-- localization — by a single mechanism: their truth value collapses
-- to ⊤, and ⊤ is j-closed for every topology (⊤-j-closed = j-⊤).
--
-- The transportability story (Transport.Transportability) lands on
-- exactly the same point.  A counterfactual is TRANSPORTABLE to the
-- global context iff it is forced there; and we show that when it is,
-- its internal truth value is the MAXIMAL sieve ⊤ — so it is j-closed
-- for every topology, i.e. INVARIANT under every localization, by the
-- paper's own ⊤-j-closed.
--
--   transportable→⊤-gen        : forced at the global context ⟹ the
--                                counterfactual's truth value is ⊤,
--                                for ANY R : RegPred.
--   transportable→invariant-gen: hence j-closed for EVERY topology J —
--                                the same ⊤-collapse the paper's
--                                do-j-stable / modal-rules use.
--   transportable→⊤, transportable→invariant: the scmPred instances.
--
-- Both general forms quantify over the regime predicate; the base
-- category of regimes is still the fixed two-object one of
-- Transport.CounterfactualForcing.
--
-- So: transportability = j-stability = invariance.  The modality the
-- paper studies for interventions is, for counterfactuals, exactly
-- transportability.  A counterfactual that holds only in an
-- environment (not transportable) is NOT ⊤, hence not j-closed for the
-- regime topology — it has not yet become invariant.
--
-- STILL OPEN (unchanged): the equivalence with the Bareinboim-Pearl
-- s-hedge criterion, and the probabilistic case.  This module supplies
-- the conceptual bridge to the paper's modal layer, not that
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
-- A transported counterfactual has truth value ⊤ (the maximal sieve).
-- Both regimes satisfy it: g by the forcing hypothesis, e by
-- restriction-stability (the sieve closure).
-- ----------------------------------------------------------
-- General form: ANY restriction-stable regime predicate, not just scmPred.
-- The proof uses only RegPred.stable and RegPred.isPropP.
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
-- Hence transportability ⟹ invariance: a transported counterfactual
-- is j-closed for EVERY Lawvere-Tierney topology, by the paper's
-- ⊤-j-closed.  This is the same collapse-to-⊤ as do-j-stable.
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
