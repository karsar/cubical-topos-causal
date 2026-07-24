{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportSoundness — step 3 (re-scoped): soundness.
--
-- TransportModal proved one direction: transportable ⟹ invariant
-- (forced at the global context ⟹ j-closed for every topology).  This
-- module proves the SOUNDNESS direction — invariant ⟹ transportable.
--
--   soundness : for ANY topology J in which the environment is J-DENSE
--     (a counterfactual holding along ι forces the identity of g into
--     the closure jop J g S), a J-stable counterfactual that holds in
--     the environment holds globally — it transports.
--
--   ¬¬≡⊤ : for the double-negation topology, a counterfactual holding
--     along ι has double-negation closure ⊤ (its negation ¬S S is
--     empty, so ¬¬S S is ⊤).  This is exactly ¬¬-density, discharging
--     the `dense` hypothesis of `soundness` at J = ¬¬LT.
--
-- Together with TransportModal (transportable ⟹ j-stable) this gives,
-- on the regime cover, the EQUIVALENCE
--     counterfactual transports  ⟺  it is j-stable (invariant) :
-- the invariance modality is transportability.
--
-- MECHANIZATION NOTE.  `soundness` (general) and `¬¬≡⊤` (density) are
-- both proved here, so the result is mathematically complete.  The
-- single closed term `soundness ¬¬LT ¬¬-dense` — and equally a direct
-- cover-topology instance — additionally needs the sieve-CLOSURE
-- machinery (the meet ∧S, or a sieve's downward closure `snd S`) to
-- reduce over the CONCRETE regime category.  Cubical Agda leaves the
-- category's composition operator unresolved there (a metavariable
-- `_C._⋆_`), independent of the category's laws — we tried both a thin
-- (propositional-law) and a data (refl-law) presentation, and each
-- stalls the closure machinery for the opposite reason.  This is an
-- elaboration limitation of the toy base, not a mathematical gap; the
-- abstract `soundness` above sidesteps it entirely (it touches no
-- sieve closure, only one subst along an opaque path).
--
-- STILL OPEN: equivalence with the Bareinboim-Pearl s-hedge criterion
-- (completeness), cited as the remaining open problem.
-- ============================================================

module Transport.TransportSoundness where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty using (⊥*; isProp⊥*) renaming (rec* to ⊥*-rec)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Forcing
open import Topos.LawvereTierney
open LawvereTierney
open import Topos.DoubleNegation

open import Transport.CounterfactualForcing using (Obj; g; e; ι; Hom₀; idn₀; C)

-- ----------------------------------------------------------
-- SOUNDNESS, abstractly: for ANY topology in which the environment is
-- j-dense, j-stability + local truth ⟹ global truth.  The subst is
-- along the opaque j-closedness path, so no closure data is touched.
-- ----------------------------------------------------------
soundness :
    (J : LawvereTierney {C = C})
  → ((S : Sieve {C = C} g) → fst (fst S e ι)
       → fst (fst (jop J g S) g (idn₀ {g})))     -- ι is J-dense in g
  → (S : Sieve {C = C} g)
  → is-j-closed J g S
  → fst (fst S e ι)
  → _⊩_ {C = C} g S
soundness J dense S closed ιinS =
  subst (λ T → fst (fst T g (idn₀ {g}))) closed (dense S ιinS)

-- ----------------------------------------------------------
-- ¬¬-density: if the counterfactual holds along ι, its negation is
-- empty (every arrow into g restricts back onto ι, where it holds), so
-- its double negation is ⊤.
-- ----------------------------------------------------------
¬S-empty : (S : Sieve {C = C} g) → fst (fst S e ι) → ¬S {C = C} {g} S ≡ ⊥S {C = C} g
¬S-empty S ιinS =
  Sieve≡ {C = C} (¬S {C = C} {g} S) (⊥S {C = C} g)
    (funExt λ d → funExt λ f → memEq d f)
  where
    memEq : (d : Obj) (f : Hom₀ d g)
          → fst (¬S {C = C} {g} S) d f ≡ fst (⊥S {C = C} g) d f
    memEq g f = ⇔toPath (λ w → w e ι ιinS) (λ x → ⊥*-rec x)
    memEq e f = ⇔toPath (λ w → w e (idn₀ {e}) ιinS) (λ x → ⊥*-rec x)

¬S-⊥≡⊤ : ¬S {C = C} {g} (⊥S {C = C} g) ≡ maximal {C = C} g
¬S-⊥≡⊤ =
  Sieve≡ {C = C} (¬S {C = C} {g} (⊥S {C = C} g)) (maximal {C = C} g)
    (funExt λ d → funExt λ f → ⇔toPath (λ _ → tt*) (λ _ e g' x → x))

¬¬≡⊤ : (S : Sieve {C = C} g) → fst (fst S e ι) → ¬¬S {C = C} {g} S ≡ maximal {C = C} g
¬¬≡⊤ S ιinS = cong (¬S {C = C} {g}) (¬S-empty S ιinS) ∙ ¬S-⊥≡⊤
