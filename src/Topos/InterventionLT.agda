{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.InterventionLT — the intervention coverage as a
-- Lawvere-Tierney topology on Ω.
--
-- Topos.InterventionModality computes a closure operator `jS` at
-- the single object `obs` of the intervention poset, and shows
-- that `jS` separates truth values there.  That is not enough to
-- reach the modal theorems.  `do-j-stable`, `modal-rule1` to
-- `modal-rule3`, the reflector of Topos.Modality and the
-- transport results are all quantified over `J : LawvereTierney`.
-- `jS` is an endofunction on the sieves over one object, so it is
-- not yet a map Ω ⇒ Ω.  Before this module the record had two
-- inhabitants: `trivialLT`, which is vacuous, and `¬¬LT`, the
-- Boolean localisation.  Neither of them is the intervention
-- coverage, so the general theory did not apply to it.
--
-- This module supplies the missing instance.  The closure extends
-- to the whole poset by taking the identity at `do0` and `do1`.
-- The only arrow into each of those is the identity.  The four
-- requirements then hold.  Naturality and idempotence are refl.
-- Truth-preservation and meet-preservation each need one
-- reshuffle of the components at `obs`.
--
-- With `interventionLT` available, every modal theorem
-- instantiates at the intervention coverage.
-- ============================================================

module Topos.InterventionLT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isProp×)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Functions.Logic using (⇔toPath)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney
open import Topos.DoubleNegation using (_⇒S_)
open import Topos.InterventionSite
open import Topos.InterventionModality using (jS)

open Precategory Iv
open LawvereTierney

-- ------------------------------------------------------------
-- The closure, at every object.  At obs it is the coverage
-- closure.  At each intervention it is the identity.  The only
-- arrow into an intervention is the identity, so nothing there is
-- covered by a smaller family.
-- ------------------------------------------------------------
jopI : (c : IObj) → Sieve {C = Iv} c → Sieve {C = Iv} c
jopI obs S = jS S
jopI do0 S = S
jopI do1 S = S

-- ------------------------------------------------------------
-- Naturality.  jopI commutes with restriction, so it is a map of
-- presheaves Ω ⇒ Ω rather than a family of separate operations.
-- ------------------------------------------------------------
jnatI : IsNat {C = Iv} (Ω {C = Iv}) (Ω {C = Iv}) jopI
jnatI obs obs idₒ S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → goO d g)
  where
    goO : (d : IObj) (g : IHom d obs)
        → fst (jopI obs (pull {C = Iv} idₒ S)) d g
        ≡ fst (pull {C = Iv} idₒ (jopI obs S)) d g
    goO obs idₒ = refl
    goO do0 e0  = refl
    goO do1 e1  = refl
jnatI do0 obs e0 S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go0 d g)
  where
    go0 : (d : IObj) (g : IHom d do0)
        → fst (jopI do0 (pull {C = Iv} e0 S)) d g
        ≡ fst (pull {C = Iv} e0 (jopI obs S)) d g
    go0 do0 id₀ = refl
jnatI do1 obs e1 S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go1 d g)
  where
    go1 : (d : IObj) (g : IHom d do1)
        → fst (jopI do1 (pull {C = Iv} e1 S)) d g
        ≡ fst (pull {C = Iv} e1 (jopI obs S)) d g
    go1 do1 id₁ = refl
jnatI do0 do0 id₀ S = refl
jnatI do1 do1 id₁ S = refl

-- ------------------------------------------------------------
-- Truth is covered.
-- ------------------------------------------------------------
j-⊤I : (c : IObj) → jopI c (maximal {C = Iv} c) ≡ maximal {C = Iv} c
j-⊤I obs = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs (maximal {C = Iv} obs)) d g
       ≡ fst (maximal {C = Iv} obs) d g
    go obs idₒ = ⇔toPath (λ _ → tt*) (λ _ → tt* , tt*)
    go do0 e0  = refl
    go do1 e1  = refl
j-⊤I do0 = refl
j-⊤I do1 = refl

-- ------------------------------------------------------------
-- Idempotence.  Closing twice at obs asks for the same two
-- memberships, so the two sides are already equal as terms.
-- ------------------------------------------------------------
j-idemI : (c : IObj) (S : Sieve {C = Iv} c) → jopI c (jopI c S) ≡ jopI c S
j-idemI obs S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs (jopI obs S)) d g ≡ fst (jopI obs S) d g
    go obs idₒ = refl
    go do0 e0  = refl
    go do1 e1  = refl
j-idemI do0 S = refl
j-idemI do1 S = refl

-- ------------------------------------------------------------
-- Meets.  At obs both sides ask for the same four memberships,
-- in a different order.
-- ------------------------------------------------------------
j-∧I : (c : IObj) (S T : Sieve {C = Iv} c)
     → jopI c (_∧S_ {C = Iv} S T) ≡ _∧S_ {C = Iv} (jopI c S) (jopI c T)
j-∧I obs S T = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs (_∧S_ {C = Iv} S T)) d g
       ≡ fst (_∧S_ {C = Iv} (jopI obs S) (jopI obs T)) d g
    go obs idₒ = ⇔toPath (λ p → (fst (fst p) , fst (snd p)) , (snd (fst p) , snd (snd p)))
                         (λ q → (fst (fst q) , fst (snd q)) , (snd (fst q) , snd (snd q)))
    go do0 e0  = refl
    go do1 e1  = refl
j-∧I do0 S T = refl
j-∧I do1 S T = refl

-- ------------------------------------------------------------
-- The LawvereTierney instance.
-- ------------------------------------------------------------
interventionLT : LawvereTierney {C = Iv}
interventionLT = record
  { jop    = jopI
  ; jnat   = jnatI
  ; j-⊤    = j-⊤I
  ; j-idem = j-idemI
  ; j-∧    = j-∧I
  }

-- ------------------------------------------------------------
-- The instance is not vacuous, and it separates truth values.
--
-- `trivialLT` fixes every truth value.  `¬¬LT` is the identity on
-- the two-regime site of Topos.ContingentCI.  So neither of them
-- moves a truth value for a causal reason.  `interventionLT`
-- fixes the claim that holds under one intervention, and sends
-- the claim that holds under both up to ⊤.
-- ------------------------------------------------------------
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥)
open import Topos.InterventionModality
  using (ci-one; ci-both; j-both-collapses; j-one-survives)

-- ------------------------------------------------------------
-- Which truth values the modality fixes.
--
-- The two facts above are instances of one characterisation.  It
-- is the descent condition for the two-chart cover.  A truth
-- value at obs is j-closed exactly when holding under both
-- interventions forces it to hold observationally.  The converse
-- implication is downward closure of the sieve, so it holds for
-- every sieve, and all the content sits in the stated direction.
--
-- Causal reading.  The modality fixes exactly the claims that
-- already descend along the cover.  It moves exactly the claims
-- that hold under every intervention but not observationally, and
-- it sends those to ⊤.
-- ------------------------------------------------------------

-- "holding under both interventions forces holding observationally"
Descends : Sieve {C = Iv} obs → Type
Descends S = fst (fst S do0 e0) × fst (fst S do1 e1) → fst (fst S obs idₒ)

closed→descends : (S : Sieve {C = Iv} obs)
                → is-j-closed {C = Iv} interventionLT obs S → Descends S
closed→descends S p pq = transport (λ i → fst (fst (p i) obs idₒ)) pq

descends→closed : (S : Sieve {C = Iv} obs)
                → Descends S → is-j-closed {C = Iv} interventionLT obs S
descends→closed S h = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ g → go d g)
  where
    -- The reverse implication is downward closure.  A sieve that
    -- holds at the identity holds along every arrow into obs.
    go : (d : IObj) (g : IHom d obs)
       → fst (jopI obs S) d g ≡ fst S d g
    go obs idₒ = ⇔toPath h (λ r → snd S obs do0 e0 idₒ r , snd S obs do1 e1 idₒ r)
    go do0 e0  = refl
    go do1 e1  = refl

-- Both facts below are instances of the characterisation above.

-- A claim holding under only one intervention descends
-- vacuously, because its second conjunct is empty.
ci-one-descends : Descends ci-one
ci-one-descends pq = snd pq

ci-one-closed : is-j-closed {C = Iv} interventionLT obs ci-one
ci-one-closed = descends→closed ci-one ci-one-descends

-- A claim holding under both does not descend.  It holds at each
-- intervention and fails observationally.
ci-both-not-descends : ¬ (Descends ci-both)
ci-both-not-descends h = h (tt* , tt*)

ci-both-not-closed : ¬ (is-j-closed {C = Iv} interventionLT obs ci-both)
ci-both-not-closed p = ci-both-not-descends (closed→descends ci-both p)

-- ------------------------------------------------------------
-- The modality is OPEN.
--
-- The proofs above verify the Lawvere-Tierney axioms one at a
-- time.  Naming the topology explains them better.  It is the
-- OPEN modality of a subterminal.  An open modality is the
-- Heyting implication out of a fixed subterminal object.
--
-- On a poset, the subterminals of the presheaf topos are the
-- down-closed sets of objects.  Take the subterminal that picks
-- out the interventional contexts: `ci-both` at `obs`, and
-- everything at each intervention, both of these being minimal.
-- The Heyting implication out of it is the closure computed
-- above.
--
-- Two consequences.  The four axioms become instances of the
-- standard facts about open modalities, so they need not be four
-- separate computations.  And an open subtopos has a
-- complementary CLOSED one, here supported on the single object
-- `obs`, so the site splits into an interventional part and an
-- observational part.  ¬¬ is dense, so it admits no such
-- splitting.
-- ------------------------------------------------------------

-- the subterminal picking out the interventional contexts
uInt : (c : IObj) → Sieve {C = Iv} c
uInt obs = ci-both
uInt do0 = maximal {C = Iv} do0
uInt do1 = maximal {C = Iv} do1

-- the open modality it induces
jopen : (c : IObj) → Sieve {C = Iv} c → Sieve {C = Iv} c
jopen c S = _⇒S_ {C = Iv} {c = c} (uInt c) S

open-is-intervention : (c : IObj) (S : Sieve {C = Iv} c)
                     → jopen c S ≡ jopI c S
open-is-intervention obs S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ f → go d f)
  where
    back : fst (fst S do0 e0) → fst (fst S do1 e1)
         → (e : IObj) (g : IHom e obs)
         → fst (fst (uInt obs) e (g ⋆I idₒ)) → fst (fst S e (g ⋆I idₒ))
    back p q obs idₒ w = E.rec w
    back p q do0 e0  _ = p
    back p q do1 e1  _ = q

    back0 : fst (fst S do0 e0)
          → (e : IObj) (g : IHom e do0)
          → fst (fst (uInt obs) e (g ⋆I e0)) → fst (fst S e (g ⋆I e0))
    back0 p do0 id₀ _ = p

    back1 : fst (fst S do1 e1)
          → (e : IObj) (g : IHom e do1)
          → fst (fst (uInt obs) e (g ⋆I e1)) → fst (fst S e (g ⋆I e1))
    back1 q do1 id₁ _ = q

    go : (d : IObj) (f : IHom d obs)
       → fst (jopen obs S) d f ≡ fst (jopI obs S) d f
    go obs idₒ = ⇔toPath (λ h → h do0 e0 tt* , h do1 e1 tt*)
                         (λ p → back (fst p) (snd p))
    go do0 e0  = ⇔toPath (λ h → h do0 id₀ tt*) back0
    go do1 e1  = ⇔toPath (λ h → h do1 id₁ tt*) back1
open-is-intervention do0 S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ f → go d f)
  where
    back : fst (fst S do0 id₀)
         → (e : IObj) (g : IHom e do0)
         → fst (fst (uInt do0) e (g ⋆I id₀)) → fst (fst S e (g ⋆I id₀))
    back s do0 id₀ _ = s

    go : (d : IObj) (f : IHom d do0)
       → fst (jopen do0 S) d f ≡ fst (jopI do0 S) d f
    go do0 id₀ = ⇔toPath (λ h → h do0 id₀ tt*) back
open-is-intervention do1 S = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ f → go d f)
  where
    back : fst (fst S do1 id₁)
         → (e : IObj) (g : IHom e do1)
         → fst (fst (uInt do1) e (g ⋆I id₁)) → fst (fst S e (g ⋆I id₁))
    back s do1 id₁ _ = s

    go : (d : IObj) (f : IHom d do1)
       → fst (jopen do1 S) d f ≡ fst (jopI do1 S) d f
    go do1 id₁ = ⇔toPath (λ h → h do1 id₁ tt*) back

-- ------------------------------------------------------------
-- What a j-stable truth value is.
--
-- Openness determines the sheaves as well as the criterion.  The
-- open subtopos here is carried by the two interventions, and
-- they are discrete.  So a j-closed truth value at `obs` should
-- amount to a pair of truth values, one per intervention.  It
-- does.  The observational membership of a closed sieve is forced
-- to be the conjunction of the two interventional ones, and every
-- pair arises this way.
--
-- Causal reading.  This is the strongest statement the site
-- supports.  A j-stable claim has no observational content beyond
-- what its behaviour under the two interventions says, and
-- `Descends` is the criterion for having no more.
-- ------------------------------------------------------------

-- the closed sieve determined by a pair of interventional verdicts
fromPair : hProp ℓ-zero → hProp ℓ-zero → Sieve {C = Iv} obs
fromPair P Q = mem , clo
  where
    mem : (d : IObj) → IHom d obs → hProp ℓ-zero
    mem obs idₒ = (fst P × fst Q) , isProp× (snd P) (snd Q)
    mem do0 e0  = P
    mem do1 e1  = Q
    clo : Closure {C = Iv} obs mem
    clo obs obs idₒ idₒ pf = pf
    clo obs do0 e0  idₒ pf = fst pf
    clo obs do1 e1  idₒ pf = snd pf
    clo do0 do0 id₀ e0  pf = pf
    clo do1 do1 id₁ e1  pf = pf

fromPair-closed : (P Q : hProp ℓ-zero)
                → is-j-closed {C = Iv} interventionLT obs (fromPair P Q)
fromPair-closed P Q = descends→closed (fromPair P Q) (λ pq → pq)

-- reading the pair back off
toPair : Sieve {C = Iv} obs → hProp ℓ-zero × hProp ℓ-zero
toPair S = fst S do0 e0 , fst S do1 e1

-- every pair is realised; the proof is refl
toPair-fromPair : (P Q : hProp ℓ-zero) → toPair (fromPair P Q) ≡ (P , Q)
toPair-fromPair P Q = refl

-- A closed sieve is recovered from its pair.  Its observational
-- membership is not independent data.
fromPair-toPair : (S : Sieve {C = Iv} obs)
                → is-j-closed {C = Iv} interventionLT obs S
                → fromPair (fst S do0 e0) (fst S do1 e1) ≡ S
fromPair-toPair S cl = Sieve≡ {C = Iv} _ _ (funExt λ d → funExt λ f → go d f)
  where
    go : (d : IObj) (f : IHom d obs)
       → fst (fromPair (fst S do0 e0) (fst S do1 e1)) d f ≡ fst S d f
    go obs idₒ = ⇔toPath (closed→descends S cl)
                         (λ r → snd S obs do0 e0 idₒ r , snd S obs do1 e1 idₒ r)
    go do0 e0  = refl
    go do1 e1  = refl
