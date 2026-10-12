{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportSoundness: the converse direction:
-- closedness and local truth give global truth.
--
-- Transport.TransportModal proves that a counterfactual forced at
-- the global context g is j-closed for every topology.  This
-- module proves the converse on the two-regime base, with one
-- more premise: the counterfactual must hold in the environment.
--
--   soundness : take ANY topology J for which the environment is
--     J-DENSE.  J-dense means that a counterfactual holding along ι
--     forces the identity of g into the closure jop J g S.  Then a
--     J-closed counterfactual that holds in the environment holds
--     globally.
--
--   ¬¬≡⊤ : for the double-negation topology, a counterfactual
--     holding along ι has double-negation closure ⊤.  Its negation
--     is empty, so its double negation is ⊤.  This is ¬¬-density,
--     and it discharges the density premise at J = ¬¬LT.
--
-- Together with TransportModal this gives an equivalence on this
-- base: forced at g  ⟺  ¬¬-closed AND true in the environment.
-- The empty sieve is ¬¬-closed and is not forced, so the second
-- conjunct cannot be dropped.
--
-- "Invariant" in older theorem names means j-closed.  It does not
-- mean that a causal effect takes the same value in every regime.
--
-- Results:
--   soundness                  J-dense and J-closed and local ⇒ global.
--   ¬¬-dense                   density holds at the double negation.
--   composed-soundness         the closed term at J = ¬¬LT.
--   global→closed-and-local    global ⇒ ¬¬-closed and local.
--   closed-and-local→global    the converse.
--   bottom-closed              the empty sieve is ¬¬-closed.
--   bottom-not-forced          the empty sieve is not forced at g.
-- ============================================================

module Transport.TransportSoundness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
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
open import Transport.TransportDescent using (forced→closed)

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

-- ------------------------------------------------------------
-- THE EQUIVALENCE.  Local truth is stated as a premise.  Density
-- is already proved at the double negation.
-- ------------------------------------------------------------
global→closed-and-local : (S : Sieve {C = C} g) → _⊩_ {C = C} g S
  → is-j-closed (¬¬LT {C = C}) g S × fst (fst S e ι)
global→closed-and-local S h =
  forced→closed (¬¬LT {C = C}) g S h ,
  maximal→mem {C = C} S (Topos.Classifier.idn∈→maximal {C = C} S h) e ι

closed-and-local→global : (S : Sieve {C = C} g)
  → is-j-closed (¬¬LT {C = C}) g S × fst (fst S e ι) → _⊩_ {C = C} g S
closed-and-local→global S (closed , local) = composed-soundness S closed local

-- ------------------------------------------------------------
-- Local truth cannot be dropped.  The empty sieve is ¬¬-closed,
-- and it is not forced at g.
-- ------------------------------------------------------------
bottom-closed : is-j-closed (¬¬LT {C = C}) g (⊥S {C = C} g)
bottom-closed = Sieve≡ {C = C} _ _
  (funExt λ d → funExt λ f → ⇔toPath
    (λ nn → nn d (idn₀ {d}) (λ e h x → x))
    (λ x e h n → x))

bottom-not-forced : _⊩_ {C = C} g (⊥S {C = C} g) → ⊥*
bottom-not-forced x = x
