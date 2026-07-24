{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportProbabilistic — step 2, the probabilistic lift.
--
-- The general theorem (Transport.TransportGeneral) is stated for
-- ANY presheaf of worlds and ANY prop-valued, restriction-stable
-- predicate.  The probabilistic case is therefore an INSTANTIATION,
-- not new scaffolding: worlds are finite probability distributions
-- (the companion paper's FDist monad), and the counterfactual is a
-- DISTRIBUTIONAL equality.
--
-- The one fact that makes this work: FDist A is a SET (its HIT carries
-- the `trunc` constructor), so a distributional statement `d ≡ q` is a
-- PROPOSITION — exactly what StablePred requires.  Hence:
--
--   Wp        — a presheaf of probabilistic worlds (FDist Bool);
--   probPred  — the predicate "the world distribution equals a target",
--               restriction-stable, so a genuine StablePred;
--   χp        — therefore a subobject χ : Wp ⇒ Ω (from the general
--               theorem): probabilistic counterfactual statements are
--               internal truth values;
--   prob-transport-invariant — and transport (forcing) of a
--               distributional counterfactual is downward-closed, for
--               free, exactly as in the deterministic case.
--
--   transport→dist — the bridge: a transported (deterministic)
--               counterfactual has a determinate DISTRIBUTION — the
--               point mass at the queried outcome — in every regime.
--               (cfd c u = pure (cfo c u); transport ⟹ cfd ≡ pure true.)
--
-- So the whole transport / forcing / invariance story carries over
-- from Boolean outcomes to probability distributions unchanged.
--
-- STILL OPEN (step 3 territory).  Here the per-regime distributions are
-- point masses and restriction-stability is the Boolean one lifted.  The
-- genuinely probabilistic refinement — worlds carrying kernels, abduction
-- as Bayesian conditioning, restriction-stability as conditioning-
-- invariance, and the SOUNDNESS direction (invariant ⟹ transportable) —
-- is the next step, built on this instantiation.
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
-- A presheaf of probabilistic worlds: a world is a finite distribution
-- over outcomes, shared across regimes (twin network), so restriction
-- is the identity.
-- ----------------------------------------------------------
Wp : PSh C ℓ-zero
Wp = record
  { F₀ = λ _ → FDist Bool
  ; F₁ = λ _ d → d
  ; F-id = λ _ → refl
  ; F-comp = λ _ _ _ → refl
  ; isSetF₀ = λ _ → isSetFDistBool }

-- ----------------------------------------------------------
-- The probabilistic counterfactual predicate: "the world distribution
-- equals the target".  Prop-valued (FDist is a set) and restriction-
-- stable, hence a genuine StablePred — so the general theorem applies.
-- ----------------------------------------------------------
probPred : TG.StablePred {C = C} Wp
probPred = record
  { pred   = λ c w → (w ≡ pure true) , trunc w (pure true)
  ; stable = λ f a pf → pf }

-- The probabilistic counterfactual is an internal predicate χ : Wp ⇒ Ω.
χp : Nat Wp Ω
χp = TG.chi probPred

-- Transport (forcing) of a distributional counterfactual is downward-
-- closed: forced at a regime ⟹ forced at every regime restricting in.
prob-transport-invariant :
    {c : Obj} (w : FDist Bool) → _⊩_ {C = C} c (TG.chiSieve probPred c w)
  → {d : Obj} (f : Hom₀ d c) → _⊩_ {C = C} d (TG.chiSieve probPred d w)
prob-transport-invariant w h f = TG.transport-invariant probPred w h f

-- ----------------------------------------------------------
-- Bridge to the deterministic transport result: the transported
-- counterfactual has a determinate distribution (a point mass) in
-- every regime.
-- ----------------------------------------------------------
cfd : Obj → U → FDist Bool
cfd c u = pure (cfo c u)

transport→dist : (u : U) → transports-to scmPred g u
               → (d : Obj) → cfd d u ≡ pure true
transport→dist u t d = cong pure (global-transport→everywhere scmPred u t d)
