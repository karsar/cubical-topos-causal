{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.InterventionModality — Gate 1 payload.  On the intervention
-- site Iv (do0 → obs ← do1) with the genuine coverage "obs is
-- covered by {do0, do1}", the closure operator j is NON-TRIVIAL:
--   * a CI that holds under BOTH interventions ({e0,e1}) closes up
--     to the maximal sieve (⊤) — real modal work;
--   * a CI that holds under only ONE intervention ({e0}) SURVIVES
--     closure (j {e0} ≠ maximal).
-- So the ⊤-collapse of the discrete two-regime site is a
-- coverage/site DEGENERACY, not an invertibility obstruction: on a
-- genuine intervention coverage the modality is non-degenerate.
-- ============================================================

module Topos.InterventionModality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp×; hProp)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty as E using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.InterventionSite
open import Topos.Omega

-- Truth values.
⊤hp : hProp ℓ-zero
⊤hp = Unit* , isPropUnit*
⊥hp : hProp ℓ-zero
⊥hp = ⊥ , isProp⊥

-- ------------------------------------------------------------
-- Two contingent CIs on `obs`, as sieves.
-- ------------------------------------------------------------
-- ci-both = {e0, e1} : holds under both interventions.
ci-both : Sieve {C = Iv} obs
ci-both = mem , clo
  where
    mem : (d : IObj) → IHom d obs → hProp ℓ-zero
    mem obs idₒ = ⊥hp
    mem do0 e0  = ⊤hp
    mem do1 e1  = ⊤hp
    clo : Closure {C = Iv} obs mem
    clo do0 do0 id₀ e0  pf = tt*
    clo do1 do1 id₁ e1  pf = tt*
    clo obs obs idₒ idₒ pf = E.rec pf
    clo obs do0 e0  idₒ pf = E.rec pf
    clo obs do1 e1  idₒ pf = E.rec pf

-- ci-one = {e0} : holds under do(X:=0) only.
ci-one : Sieve {C = Iv} obs
ci-one = mem , clo
  where
    mem : (d : IObj) → IHom d obs → hProp ℓ-zero
    mem obs idₒ = ⊥hp
    mem do0 e0  = ⊤hp
    mem do1 e1  = ⊥hp
    clo : Closure {C = Iv} obs mem
    clo do0 do0 id₀ e0  pf = tt*
    clo do1 do1 id₁ e1  pf = E.rec pf
    clo obs obs idₒ idₒ pf = E.rec pf
    clo obs do0 e0  idₒ pf = E.rec pf
    clo obs do1 e1  idₒ pf = E.rec pf

-- ------------------------------------------------------------
-- The closure operator j on sieves over `obs`, induced by the
-- coverage.  j S ∋ e_i iff e_i ∈ S; j S ∋ idₒ iff e0,e1 ∈ S.
-- ------------------------------------------------------------
jS : Sieve {C = Iv} obs → Sieve {C = Iv} obs
jS S = mem , clo
  where
    e0∈ = fst S do0 e0
    e1∈ = fst S do1 e1
    mem : (d : IObj) → IHom d obs → hProp ℓ-zero
    mem obs idₒ = (fst e0∈ × fst e1∈) , isProp× (snd e0∈) (snd e1∈)
    mem do0 e0  = e0∈
    mem do1 e1  = e1∈
    clo : Closure {C = Iv} obs mem
    clo obs obs idₒ idₒ pf = pf
    clo obs do0 e0  idₒ pf = fst pf
    clo obs do1 e1  idₒ pf = snd pf
    clo do0 do0 id₀ e0  pf = pf
    clo do1 do1 id₁ e1  pf = pf

-- ------------------------------------------------------------
-- Gate 1 facts.
-- ------------------------------------------------------------
-- (1) The CI holding under BOTH interventions closes up to ⊤.
j-both-collapses : jS ci-both ≡ maximal {C = Iv} obs
j-both-collapses = Sieve≡ {C = Iv} (jS ci-both) (maximal {C = Iv} obs)
  (funExt λ d → funExt λ f → go d f)
  where
    go : (d : IObj) (f : IHom d obs)
       → fst (jS ci-both) d f ≡ fst (maximal {C = Iv} obs) d f
    go obs idₒ = ⇔toPath (λ _ → tt*) (λ _ → (tt* , tt*))
    go do0 e0  = ⇔toPath (λ _ → tt*) (λ _ → tt*)
    go do1 e1  = ⇔toPath (λ _ → tt*) (λ _ → tt*)

-- (2) The CI holding under only ONE intervention SURVIVES: j {e0}
-- is not the maximal sieve (they differ at idₒ: ⊥ vs ⊤).
j-one-survives : ¬ (jS ci-one ≡ maximal {C = Iv} obs)
j-one-survives p = E.rec (snd bad)
  where
    -- membership at (obs, idₒ): (Unit* × ⊥) on the left, Unit* on the right
    mempath : fst (jS ci-one) obs idₒ ≡ fst (maximal {C = Iv} obs) obs idₒ
    mempath i = fst (fst (p i) obs idₒ) , snd (fst (p i) obs idₒ)
    bad : Unit* × ⊥
    bad = transport (sym (cong fst mempath)) tt*
