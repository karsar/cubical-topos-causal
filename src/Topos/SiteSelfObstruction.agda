{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.SiteSelfObstruction — the intervention site cannot
-- express the paper's own do-versus-see result.
--
-- Topos.ColliderObstruction shows that a predicate some
-- refinement falsifies is not a truth value.  This module draws
-- the instance that bears on the development itself.
--
-- On the intervention site the arrows run do0 -> obs and
-- do1 -> obs: an intervention REFINES the observational
-- context.  Sieves are closed under precomposition, so a sieve
-- on obs that contains the identity contains e0 and e1 as well.
--
-- Hence no truth value on obs holds observationally and fails
-- under an intervention.  That is exactly the shape of the
-- confounded claim of Topos.DoSeeDistinct, where the outcome is
-- certain given the observation and uncertain under the
-- surgery.  On this site that claim has no internal truth value.
--
-- The moral is a design constraint, not a defect in the proofs.
-- Putting causal claims into a sheaf semantics over regimes
-- requires the refinement order to be chosen so that the claims
-- of interest are monotone along it.  The natural reading, that
-- intervening refines observing, makes non-invariance under
-- intervention inexpressible.  Reversing the arrows would
-- express it and would break the covering story instead, since
-- obs would no longer be covered by its interventions.
--
-- Results:
--   obs-forces-e0     forcing at obs propagates to do0,
--   obs-forces-e1     and to do1.
--   no-see-not-do     so no sieve holds at obs and fails at do0.
-- ============================================================

module Topos.SiteSelfObstruction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Cat
open import Topos.Omega
open import Topos.Forcing using (_⊩_)
open import Topos.InterventionSite

-- ------------------------------------------------------------
-- Forcing at the observational context propagates to both
-- interventions.  This is downward closure of sieves, at the
-- two arrows the site provides.
-- ------------------------------------------------------------
obs-forces-e0 : (S : Sieve {C = Iv} obs)
              → _⊩_ {C = Iv} obs S → fst (fst S do0 e0)
obs-forces-e0 S h = snd S obs do0 e0 idₒ h

obs-forces-e1 : (S : Sieve {C = Iv} obs)
              → _⊩_ {C = Iv} obs S → fst (fst S do1 e1)
obs-forces-e1 S h = snd S obs do1 e1 idₒ h

-- ------------------------------------------------------------
-- THE OBSTRUCTION.  No truth value on this site holds
-- observationally and fails under an intervention, which is the
-- pattern the confounded example of Topos.DoSeeDistinct
-- exhibits at the level of kernels.
-- ------------------------------------------------------------
no-see-not-do
  : ¬ ( Σ[ S ∈ Sieve {C = Iv} obs ]
          ( (_⊩_ {C = Iv} obs S) × (¬ (fst (fst S do0 e0))) ) )
no-see-not-do (S , holds , fails) = fails (obs-forces-e0 S holds)

-- The same for the other intervention.
no-see-not-do₁
  : ¬ ( Σ[ S ∈ Sieve {C = Iv} obs ]
          ( (_⊩_ {C = Iv} obs S) × (¬ (fst (fst S do1 e1))) ) )
no-see-not-do₁ (S , holds , fails) = fails (obs-forces-e1 S holds)
