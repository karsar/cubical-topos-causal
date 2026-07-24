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
--   transportable→⊤        : forced at the global context ⟹ the
--                            counterfactual's truth value is ⊤.
--   transportable→invariant: hence j-closed for EVERY topology J —
--                            the same ⊤-collapse the paper's
--                            do-j-stable / modal-rules use.
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
transportable→⊤ : (u : U) → transports-to scmPred g u
                → fst (χ scmPred) g u ≡ maximal {C = C} g
transportable→⊤ u t =
  Sieve≡ {C = C} (fst (χ scmPred) g u) (maximal {C = C} g)
    (funExt λ d → funExt λ h → inhab d)
  where
    inhab : (d : Obj)
          → (RegPred.P scmPred d u , RegPred.isPropP scmPred d u) ≡ (Unit* , isPropUnit*)
    inhab g = ⇔toPath (λ _ → tt*) (λ _ → t)
    inhab e = ⇔toPath (λ _ → tt*) (λ _ → RegPred.stable scmPred g e ι u t)

-- ----------------------------------------------------------
-- Hence transportability ⟹ invariance: a transported counterfactual
-- is j-closed for EVERY Lawvere-Tierney topology, by the paper's
-- ⊤-j-closed.  This is the same collapse-to-⊤ as do-j-stable.
-- ----------------------------------------------------------
transportable→invariant :
    (u : U) → transports-to scmPred g u
  → (J : LawvereTierney {C = C}) → is-j-closed J g (fst (χ scmPred) g u)
transportable→invariant u t J =
  subst (λ S → is-j-closed J g S) (sym (transportable→⊤ u t)) (⊤-j-closed J g)
