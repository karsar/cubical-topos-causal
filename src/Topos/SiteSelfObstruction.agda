{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.SiteSelfObstruction: the certainty pattern of the
-- confounded model has no truth value on the intervention site.
--
-- On the intervention site the arrows run do0 -> obs and
-- do1 -> obs: an intervention REFINES the observational
-- context.  Sieves are closed under precomposition, so a sieve
-- on obs that contains the identity contains e0 and e1 as well.
-- Hence no truth value holds observationally and fails under an
-- intervention.
--
-- The confounded model of Topos.DoSeeDistinct has that pattern.
-- Given the observation X = 1, the outcome is certain.  Under
-- the surgery do(X = 1) it is not.  So the stagewise predicate
-- "the outcome is certain" has no natural classifier here.
--
-- The inequality between the two probabilities is a different
-- proposition.  It holds at every context, so it is a constant
-- truth value, and it is forced everywhere.  The site can state
-- the inequality.  It cannot state the varying certainty pattern.
--
-- Results:
--   obs-forces-e0/e1      forcing at obs propagates to do0, do1.
--   no-see-not-do         so no sieve holds at obs and fails at
--                         do0.
--   no-see-not-do₁        nor one that holds at obs and fails at
--                         do1.
--   no-natural-certainty  no natural α : 𝟙 ⇒ Ω is forced exactly
--                         where the outcome is certain.
--   difference-name       the inequality as a natural α : 𝟙 ⇒ Ω,
--   difference-forced     forced at every context,
--   difference-maximal    so its sieve is ⊤ at every context.
-- ============================================================

module Topos.SiteSelfObstruction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (isProp¬)

open import Topos.Cat
open import Topos.Omega
open import Topos.Forcing using (_⊩_)
open import Topos.InterventionSite
open import Topos.PSh
open import Topos.ModalRule1 using (prop→sieve; prop→sieve-true)
open import Topos.DoSeeDistinct
open import FDist-Convex using (𝔼)
open import WeightQ using (Weight; w1; isSetWeight)

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
-- observationally and fails under an intervention.  That is the
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

-- ------------------------------------------------------------
-- THE CERTAINTY PREDICATE.  probability c is the outcome
-- probability the confounded model computes at context c:
-- conditional at obs, interventional at do0 and do1.  Certain c
-- says that probability is 1.  It holds at obs and fails at do1.
-- ------------------------------------------------------------
probability : IObj → Weight
probability obs = Half.condProb
probability do0 = 𝔼 (do-joint false Half.bc) indYtrue
probability do1 = 𝔼 (do-joint true Half.bc) indYtrue

Certain : IObj → Type
Certain c = probability c ≡ w1

certain-obs : Certain obs
certain-obs = Half.condProb≡w1

not-certain-do1 : ¬ (Certain do1)
not-certain-do1 p = do≢see-half (p ∙ sym certain-obs)

ExactCertainty : Nat {C = Iv} 𝟙 Ω → Type
ExactCertainty α = (c : IObj) →
  ((_⊩_ {C = Iv} c (fst α c tt)) → Certain c) × (Certain c → (_⊩_ {C = Iv} c (fst α c tt)))

no-natural-certainty : (α : Nat {C = Iv} 𝟙 Ω) → ¬ (ExactCertainty α)
no-natural-certainty α exact = not-certain-do1
  (fst (exact do1)
    (subst (λ S → _⊩_ {C = Iv} do1 S) (sym (snd α do1 obs e1 tt))
      (obs-forces-e1 (fst α obs tt) (snd (exact obs) certain-obs))))

Difference : hProp ℓ-zero
Difference = (¬ (probability do1 ≡ probability obs)) , isProp¬ _

-- ------------------------------------------------------------
-- THE INEQUALITY.  The do-versus-see inequality is one
-- proposition, the same at every context.  Its constant sieve is
-- natural, and the checked naturality proof is refl.
-- ------------------------------------------------------------
difference-name : Nat {C = Iv} 𝟙 Ω
difference-name = (λ c _ → prop→sieve {C = Iv} c Difference) ,
  (λ x y f a → Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → refl))

difference-forced : (c : IObj) → _⊩_ {C = Iv} c (fst difference-name c tt)
difference-forced c = do≢see-half

difference-maximal : (c : IObj) → fst difference-name c tt ≡ maximal {C = Iv} c
difference-maximal c = prop→sieve-true {C = Iv} c Difference do≢see-half
