{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportSoundness — step 3 (re-scoped): soundness.
--
-- TransportModal proves one direction: transportable gives
-- invariant, that is, forced at the global context gives j-closed
-- for every topology.  This module proves the SOUNDNESS direction:
-- invariant gives transportable.
--
--   soundness : take ANY topology J for which the environment is
--     J-DENSE.  J-dense means that a counterfactual holding along ι
--     forces the identity of g into the closure jop J g S.  Then a
--     J-stable counterfactual that holds in the environment holds
--     globally, so it transports.
--
--   ¬¬≡⊤ : for the double-negation topology, a counterfactual
--     holding along ι has double-negation closure ⊤, because its
--     negation ¬S S is empty and so ¬¬S S is ⊤.  This is
--     ¬¬-density, and it discharges the `dense` hypothesis of
--     `soundness` at J = ¬¬LT.
--
-- Together with TransportModal, which gives transportable ⟹
-- j-stable, this yields on the regime cover the EQUIVALENCE
--     counterfactual transports  ⟺  it is j-stable (invariant) :
-- the invariance modality is transportability.
--
-- MECHANIZATION NOTE.  soundness is proved for an arbitrary
-- topology J that satisfies the density hypothesis.  The
-- hypothesis is discharged at the double-negation topology
-- below: ¬¬-dense routes through ¬¬≡⊤ to the maximal sieve,
-- then applies maximal→mem, so no sieve-closure computation
-- is needed.  composed-soundness is the closed term.
-- A direct instance at a cover topology is not built here.

-- ============================================================

module Transport.TransportSoundness where

open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Empty using (⊥*; isProp⊥*) renaming (rec* to ⊥*-rec)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Classifier using (maximal→mem)
open import Topos.Forcing
open import Topos.LawvereTierney
open LawvereTierney
open import Topos.DoubleNegation

open import Transport.CounterfactualForcing using (Obj; g; e; ι; Hom₀; idn₀; C)

-- ----------------------------------------------------------
-- SOUNDNESS in the abstract form.  For ANY topology in which the
-- environment is j-dense, j-stability together with local truth
-- gives global truth.  The subst runs along the opaque j-closedness
-- path, so it touches no closure data.
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
-- ¬¬-density.  Suppose the counterfactual holds along ι.  Every
-- arrow into g restricts back onto ι, where the counterfactual
-- holds, so its negation is empty and its double negation is ⊤.
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

-- ----------------------------------------------------------
-- The composed statement.  Density is discharged at the
-- double-negation topology, so soundness holds over this base
-- with no density hypothesis left to supply.
-- ----------------------------------------------------------
¬¬-dense : (S : Sieve {C = C} g) → fst (fst S e ι)
         → fst (fst (LawvereTierney.jop (¬¬LT {C = C}) g S) g (idn₀ {g}))
¬¬-dense S ιinS =
  maximal→mem {C = C} (¬¬S {C = C} {g} S) (¬¬≡⊤ S ιinS) g (idn₀ {g})

composed-soundness
  : (S : Sieve {C = C} g)
  → is-j-closed (¬¬LT {C = C}) g S
  → fst (fst S e ι)
  → _⊩_ {C = C} g S
composed-soundness = soundness (¬¬LT {C = C}) ¬¬-dense
