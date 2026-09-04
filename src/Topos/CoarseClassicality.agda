{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.CoarseClassicality — internal versus stagewise validity
-- on the coarse site Cv (cDo → cObs).
--
-- The internal-vs-stagewise gap of Topos.Classicality is also
-- present on the coarse site, with a different witness.  The
-- fine witness uses two incomparable refinements of obs.  Here
-- cObs has a single refinement, so the witness instead
-- separates intervention from observation.
--
-- The module proves three facts on the coarse base:
--  (1) SOUND.  Internal validity implies stagewise validity.
--  (2) STRICT.  The converse fails.  The witness is em-C.
--  (3) TRANSFER.  Stagewise validity equals forcing of the
--      closure, by definition.  jC closes em-C up to ⊤.
--
-- Topos.MergeAbstraction pulls this gap back to the fine site.
-- ============================================================

module Topos.CoarseClassicality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Data.Empty as E using (⊥; ⊥*; isProp⊥; isProp⊥*)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Logic using (_⊔_; inl; inr; ⊔-elim; ⇔toPath)

open import Topos.Cat
open import Topos.Omega
open import Topos.DoubleNegation using (¬S)
open import Topos.Forcing using (_∨S_; _⊩_)
open import Topos.CoarseSite

private
  ⊥*hp : hProp ℓ-zero
  ⊥*hp = ⊥* , isProp⊥*

-- ------------------------------------------------------------
-- Stagewise validity: the claim holds under the merged
-- intervention.  This is the membership of jC S at the identity
-- of cObs, by definition of the closure.
-- ------------------------------------------------------------
stagewiseC : Sieve {C = Cv} cObs → Type
stagewiseC S = fst (fst S cDo ce)

-- (3a) Stagewise validity is internal validity of the closure.
stagewiseC→⊩j : (S : Sieve {C = Cv} cObs) → stagewiseC S → _⊩_ {C = Cv} cObs (jC S)
stagewiseC→⊩j S p = p

⊩j→stagewiseC : (S : Sieve {C = Cv} cObs) → _⊩_ {C = Cv} cObs (jC S) → stagewiseC S
⊩j→stagewiseC S p = p

-- (1) SOUND.  Internal validity implies stagewise validity.
⊩→stagewiseC : (S : Sieve {C = Cv} cObs) → _⊩_ {C = Cv} cObs S → stagewiseC S
⊩→stagewiseC S p = snd S cObs cDo ce idc p

-- ------------------------------------------------------------
-- (2) STRICT.  The witness is excluded middle for ci-c.
--
-- The witness has a different shape than in Topos.Classicality.
-- There, ¬ ci-one held at do1 and contributed to the
-- disjunction.  Here ¬ ci-c holds nowhere, because restriction
-- along ce always lands in ci-c.  Only the left disjunct
-- contributes.
-- ------------------------------------------------------------
em-C : Sieve {C = Cv} cObs
em-C = _∨S_ {C = Cv} {c = cObs} ci-c (¬S {C = Cv} {c = cObs} ci-c)

-- The left disjunct holds at ce, so the disjunction holds
-- there too.
em-C-at-cDo : fst (fst em-C cDo ce)
em-C-at-cDo = inl tt*

-- Excluded middle for ci-c is stagewise valid.
em-C-stagewise : stagewiseC em-C
em-C-stagewise = em-C-at-cDo

-- The disjunction is not forced at cObs.  ci-c omits the
-- identity.  ¬ ci-c fails at the identity: its restriction
-- along ce lands in ci-c.
em-C-not-forced : ¬ (_⊩_ {C = Cv} cObs em-C)
em-C-not-forced x = E.rec* (⊔-elim (fst ci-c cObs idc)
                                   (fst (¬S {C = Cv} {c = cObs} ci-c) cObs idc)
                                   (λ _ → ⊥*hp)
                                   (λ p  → E.rec p)
                                   (λ nc → nc cDo ce tt*)
                                   x)

-- The theorem: on the coarse site, internal validity is
-- strictly stronger than validity over the covering family.
internalC-strictly-stronger
  : Σ[ S ∈ Sieve {C = Cv} cObs ] (stagewiseC S × (¬ (_⊩_ {C = Cv} cObs S)))
internalC-strictly-stronger = em-C , em-C-stagewise , em-C-not-forced

-- ------------------------------------------------------------
-- (3b) The closure repairs exactly this gap.
-- ------------------------------------------------------------
em-C-covered : jC em-C ≡ maximal {C = Cv} cObs
em-C-covered = Sieve≡ {C = Cv} (jC em-C) (maximal {C = Cv} cObs)
  (funExt λ d → funExt λ f → go d f)
  where
    go : (d : CObj) (f : CHom d cObs)
       → fst (jC em-C) d f ≡ fst (maximal {C = Cv} cObs) d f
    go cObs idc = ⇔toPath (λ _ → tt*) (λ _ → em-C-at-cDo)
    go cDo ce   = ⇔toPath (λ _ → tt*) (λ _ → em-C-at-cDo)
