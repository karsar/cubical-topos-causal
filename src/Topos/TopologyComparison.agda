{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.TopologyComparison -- the two concrete topologies, on
-- the intervention site, compared.
--
-- An earlier version of the paper claimed that the double
-- negation topology is dense and the intervention coverage is
-- not, and concluded that the two are of different kinds.  That
-- contrast is false.  This module records the correction.
--
-- Density does not separate them.  The intervention coverage
-- sends the empty sieve to the empty sieve, so it is dense too.
--
-- The two also agree on the verdicts the coverage section runs
-- on.  Double negation collapses the sieve that holds under both
-- interventions and leaves the sieve that holds under one of
-- them short of maximal.  Those are the analogues of
-- j-both-collapses and j-one-survives in Topos.InterventionModality.
--
-- We do not prove the two operators equal.  We have not checked
-- that.  What these results establish is narrower: the
-- discrimination the coverage section reports comes from the
-- base, which carries a non-trivial refinement, and not from a
-- second operator beyond double negation.
--
-- Results:
--   j-int-dense         the intervention coverage is dense
--   nn-both-collapses   double negation collapses the both-sieve
--   nn-one-survives     double negation leaves the one-sieve short
-- ============================================================

module Topos.TopologyComparison where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isProp×)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; ⊥*)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.DoubleNegation
open import Topos.InterventionSite
open import Topos.InterventionModality using (jS; ci-one; ci-both)
open import Topos.InterventionLT using (jopI)

open Precategory Iv

-- (A) The INTERVENTION topology is itself DENSE: j(⊥) = ⊥.
--     Density is the property the paper uses to set ¬¬ apart from it.
j-int-dense : jopI obs (⊥S {C = Iv} obs) ≡ ⊥S {C = Iv} obs
j-int-dense = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ f → go d f)
  where
    go : (d : IObj) (f : IHom d obs)
       → fst (jopI obs (⊥S {C = Iv} obs)) d f ≡ fst (⊥S {C = Iv} obs) d f
    go obs idₒ = ⇔toPath fst (λ x → E.rec* x)
    go do0 e0  = refl
    go do1 e1  = refl

-- (B) ¬¬ lifts ci-both to contain the identity -- the same verdict
--     the paper displays as  j (ci-both) ≡ ⊤.
nn-both-has-id : fst (fst (¬¬S {C = Iv} {c = obs} ci-both) obs idₒ)
nn-both-has-id obs idₒ h = h do0 e0  tt*
nn-both-has-id do0 e0  h = h do0 id₀ tt*
nn-both-has-id do1 e1  h = h do1 id₁ tt*

-- (C) ¬¬ does NOT lift ci-one to contain the identity -- the same
--     verdict the paper displays as  ¬ (j (ci-one) ≡ ⊤).
neg-at-e1 : (e : IObj) (g : IHom e do1) → fst (fst ci-one e (g ⋆I e1)) → ⊥* {ℓ-zero}
neg-at-e1 obs ()
neg-at-e1 do0 ()
neg-at-e1 do1 id₁ x = E.rec x

nn-one-misses-id : ¬ (fst (fst (¬¬S {C = Iv} {c = obs} ci-one) obs idₒ))
nn-one-misses-id p = E.rec* (p do1 e1 neg-at-e1)

-- (D) The SHARP form: ¬¬ collapses ci-both to the maximal sieve,
--     which is exactly the paper's `j-both-collapses` for jopI.
nn-both-all : (d : IObj) (f : IHom d obs)
            → fst (fst (¬¬S {C = Iv} {c = obs} ci-both) d f)
nn-both-all obs idₒ obs idₒ h = h do0 e0  tt*
nn-both-all obs idₒ do0 e0  h = h do0 id₀ tt*
nn-both-all obs idₒ do1 e1  h = h do1 id₁ tt*
nn-both-all do0 e0  do0 id₀ h = h do0 id₀ tt*
nn-both-all do1 e1  do1 id₁ h = h do1 id₁ tt*

nn-both-collapses : ¬¬S {C = Iv} {c = obs} ci-both ≡ maximal {C = Iv} obs
nn-both-collapses = Sieve≡ {C = Iv} _ _
  (funExt λ d → funExt λ f → ⇔toPath (λ _ → tt*) (λ _ → nn-both-all d f))

-- (E) ¬¬ does NOT collapse ci-one -- exactly `j-one-survives` for jopI.
nn-one-survives : ¬ (¬¬S {C = Iv} {c = obs} ci-one ≡ maximal {C = Iv} obs)
nn-one-survives p = nn-one-misses-id
  (transport (λ i → fst (fst (p (~ i)) obs idₒ)) tt*)
