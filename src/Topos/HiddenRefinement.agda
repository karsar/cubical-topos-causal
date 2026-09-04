{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.HiddenRefinement — the observational restriction, and
-- what hiding a refinement does to the internal logic.
--
-- Pt is the one-context site.  obsOnly : Pt → Cv keeps cObs and
-- discards the interventional refinement cDo.  This is the
-- abstraction that looks at the observational context alone.
--
-- obsOnly fails BackCond: the refinement ce has no lift
-- (back-fails).  Both Tier-1 conclusions fail with it:
--
--  (1) NOT INJECTIVE.  ci-c and ⊥ have the same preimage
--      (hidden-collapse).  The claim "holds under the
--      intervention only" becomes indistinguishable from the
--      claim that holds nowhere.
--
--  (2) NEGATION BREAKS.  ¬ ci-c holds nowhere on Cv.  But on
--      the restricted site the preimage of ci-c is empty, so
--      its negation is internally TRUE (neg-broken).  Hiding
--      the refinement that refutes ¬ ci-c manufactures internal
--      certainty of it.
--
-- Together with Topos.MergeAbstraction (Reflect fails, φ not
-- surjective) this shows the two conditions of
-- Topos.AbstractionTiers are each needed.
-- ============================================================

module Topos.HiddenRefinement where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Prelude using (isProp→isSet)
open import Cubical.Data.Unit using (Unit; tt; isPropUnit)
open import Cubical.Data.Empty as E using (⊥; ⊥*; isProp⊥)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Data.Unit using (tt*)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.Omega
open import Topos.DoubleNegation using (¬S; ⊥S)
open import Topos.BaseChange
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Topos.AbstractionTiers using (BackCond; BackCond∥)
open import Topos.CoarseSite

-- ------------------------------------------------------------
-- The one-context site.
-- ------------------------------------------------------------
Pt : Precategory ℓ-zero ℓ-zero
Pt = record
  { Ob = Unit ; Hom = λ _ _ → Unit ; idn = tt ; _⋆_ = λ _ _ → tt
  ; ⋆-idL = λ _ → refl ; ⋆-idR = λ _ → refl ; ⋆-assoc = λ _ _ _ → refl
  ; isSetHom = isProp→isSet isPropUnit }

-- The observational restriction: keep cObs, discard cDo.
obsOnly : BaseFunctor Pt Cv
obsOnly = record
  { App₀ = λ _ → cObs ; App₁ = λ _ → idc
  ; App-id = λ _ → refl ; App-⋆ = λ _ _ → refl }

-- ------------------------------------------------------------
-- obsOnly fails the back condition: ce has no lift.
-- ------------------------------------------------------------
cObs≢cDo : ¬ (cObs ≡ cDo)
cObs≢cDo q = transport (cong code q) tt
  where
  code : CObj → Type
  code cObs = Unit
  code cDo  = ⊥

back-fails : ¬ BackCond obsOnly
back-fails b = cObs≢cDo (snd (snd (b tt cDo ce)))

-- The mere form fails too, so Topos.TiersConverse applies: φB
-- at obsOnly can be neither injective nor a Heyting morphism.
back∥-fails : ¬ BackCond∥ obsOnly
back∥-fails b = PT.rec isProp⊥ (λ l → cObs≢cDo (snd (snd l))) (b tt cDo ce)

-- ------------------------------------------------------------
-- (1) NOT INJECTIVE.  ci-c and ⊥ have the same preimage, and
-- they differ.
-- ------------------------------------------------------------
collapse : φB obsOnly tt ci-c ≡ φB obsOnly tt (⊥S {C = Cv} cObs)
collapse = Sieve≡ {C = Pt} _ _
  (funExt λ d → funExt λ f →
    ⇔toPath (λ m → E.rec m) (λ m → E.rec* m))

ci-c≢⊥ : ¬ (ci-c ≡ ⊥S {C = Cv} cObs)
ci-c≢⊥ p = E.rec* (transport (λ i → fst (fst (p i) cDo ce)) tt*)

hidden-collapse
  : (φB obsOnly tt ci-c ≡ φB obsOnly tt (⊥S {C = Cv} cObs))
  × (¬ (ci-c ≡ ⊥S {C = Cv} cObs))
hidden-collapse = collapse , ci-c≢⊥

-- ------------------------------------------------------------
-- (2) NEGATION BREAKS.  On the restricted site, the negation of
-- the preimage of ci-c is internally true: nothing visible
-- refutes it.  But the preimage of ¬ ci-c is empty, because on
-- Cv the restriction along ce refutes ¬ ci-c.
-- ------------------------------------------------------------
neg-of-pull : fst (fst (¬S {C = Pt} {c = tt} (φB obsOnly tt ci-c)) tt tt)
neg-of-pull e g m = E.rec m

pull-of-neg-empty : ¬ fst (fst (φB obsOnly tt (¬S {C = Cv} {c = cObs} ci-c)) tt tt)
pull-of-neg-empty nc = E.rec* (nc cDo ce tt*)

neg-broken : ¬ (φB obsOnly tt (¬S {C = Cv} {c = cObs} ci-c)
             ≡ ¬S {C = Pt} {c = tt} (φB obsOnly tt ci-c))
neg-broken p =
  pull-of-neg-empty (transport (λ i → fst (fst (p (~ i)) tt tt)) neg-of-pull)
