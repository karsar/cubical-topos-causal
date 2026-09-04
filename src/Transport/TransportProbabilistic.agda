{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportProbabilistic — step 2, the probabilistic lift.
--
-- The general theorem (Transport.TransportGeneral) is stated for ANY
-- presheaf of worlds and ANY prop-valued, restriction-stable
-- predicate.  The probabilistic case is therefore an INSTANTIATION
-- of it, and it needs no new scaffolding.  Worlds are finite
-- probability distributions, from the companion paper's FDist monad,
-- and the counterfactual is an equality of distributions.
--
-- One fact makes this work.  FDist A is a SET, because its HIT
-- carries the `trunc` constructor.  A statement `d ≡ q` about
-- distributions is then a PROPOSITION, which is what StablePred
-- requires.  Hence:
--
--   Wp        — a presheaf of probabilistic worlds (FDist Bool);
--   probPred  — the predicate "the world distribution equals a
--               target".  It is restriction-stable, so it is a
--               genuine StablePred;
--   χp        — the general theorem then gives a subobject
--               χ : Wp ⇒ Ω, so probabilistic counterfactual
--               statements are internal truth values;
--   prob-transport-invariant — transport, that is forcing, of a
--               distributional counterfactual is downward-closed.
--               The proof is the one from the deterministic case;
--
--   transport→dist — the bridge.  A transported deterministic
--               counterfactual has a determinate DISTRIBUTION in
--               every regime, the point mass at the queried outcome.
--               Here cfd c u = pure (cfo c u), and transport gives
--               cfd ≡ pure true.
--
-- So the transport, forcing and invariance results carry over from
-- Boolean outcomes to probability distributions unchanged.
--
-- STILL OPEN (step 3 territory).  In this module the per-regime
-- distributions are point masses, and restriction-stability is the
-- Boolean condition lifted.  The genuinely probabilistic refinement
-- is the next step, built on this instantiation: worlds carrying
-- kernels, abduction as Bayesian conditioning, restriction-stability
-- as invariance under conditioning, and the SOUNDNESS direction,
-- that invariant implies transportable.
-- ============================================================

module Transport.TransportProbabilistic where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Forcing

open import Transport.CounterfactualForcing using (Obj; g; e; Hom₀; C)
open import Transport.CounterfactualProbe using (U)
open import Transport.Transportability using (scmPred; transports-to; cfo; global-transport→everywhere)
import Transport.TransportGeneral as TG

open import FDist-Convex using (FDist; pure; trunc)

-- ----------------------------------------------------------
-- FDist Bool is a set, so distributional equality is a proposition.
-- ----------------------------------------------------------
isSetFDistBool : isSet (FDist Bool)
isSetFDistBool = trunc

-- ----------------------------------------------------------
-- A presheaf of probabilistic worlds.  A world is a finite
-- distribution over outcomes.  It is shared across regimes, as in
-- the twin network, so restriction is the identity.
-- ----------------------------------------------------------
Wp : PSh C ℓ-zero
Wp = record
  { F₀ = λ _ → FDist Bool
  ; F₁ = λ _ d → d
  ; F-id = λ _ → refl
  ; F-comp = λ _ _ _ → refl
  ; isSetF₀ = λ _ → isSetFDistBool }

-- ----------------------------------------------------------
-- The probabilistic counterfactual predicate says "the world
-- distribution equals the target".  It is prop-valued, because FDist
-- is a set, and it is restriction-stable.  It is therefore a genuine
-- StablePred, and the general theorem applies.
-- ----------------------------------------------------------
probPred : TG.StablePred {C = C} Wp
probPred = record
  { pred   = λ c w → (w ≡ pure true) , trunc w (pure true)
  ; stable = λ f a pf → pf }

-- The probabilistic counterfactual is an internal predicate χ : Wp ⇒ Ω.
χp : Nat Wp Ω
χp = TG.chi probPred

-- Transport, that is forcing, of a distributional counterfactual is
-- downward-closed.  Forced at a regime gives forced at every regime
-- restricting into it.
prob-transport-invariant :
    {c : Obj} (w : FDist Bool) → _⊩_ {C = C} c (TG.chiSieve probPred c w)
  → {d : Obj} (f : Hom₀ d c) → _⊩_ {C = C} d (TG.chiSieve probPred d w)
prob-transport-invariant w h f = TG.transport-invariant probPred w h f

-- ----------------------------------------------------------
-- Bridge to the deterministic transport result.  The transported
-- counterfactual has a determinate distribution in every regime,
-- namely a point mass.
-- ----------------------------------------------------------
cfd : Obj → U → FDist Bool
cfd c u = pure (cfo c u)

transport→dist : (u : U) → transports-to scmPred g u
               → (d : Obj) → cfd d u ≡ pure true
transport→dist u t d = cong pure (global-transport→everywhere scmPred u t d)
