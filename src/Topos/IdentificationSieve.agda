{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.IdentificationSieve: the identification predicate as a
-- morphism 𝟙 ⇒ Ω over the intervention site.
--
-- The predicate at a context c is semantic identifiability,
-- Topos.Identification's Identified, for the data available at c.
-- Topos.IdentificationModels fixes the two models, the query and
-- the data.  It proves the predicate true at do0 and do1, false
-- at obs, and closed under restriction.
--
-- The general classifier of Topos.Classifier then gives a unique
-- natural χ-ident : 𝟙 ⇒ Ω whose ⊤-fibre is exactly the
-- identifiable contexts.  Its sieve on obs is {e0, e1}, the same
-- non-maximal sieve that carries the internal-versus-stagewise
-- gap.  All verdicts hold relative to the declared two-model
-- class.
--
-- Results:
--   χ-ident, χ-ident-nat      the classifying map and naturality.
--   ident-classified          identifiable ⇒ the sieve is ⊤.
--   ident-reflected           the sieve is ⊤ ⇒ identifiable.
--   ident-not-classified-obs  the sieve at obs is not ⊤.
--   ident-mem-e0/e1           e0 and e1 are members at obs,
--   ident-not-mem-idₒ         and the identity is not.
--   StrategiesP               correct strategies form a presheaf.
-- ============================================================

module Topos.IdentificationSieve where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InterventionSite
open import Topos.IdentificationModels
import Topos.Classifier as Classifier

IdentPred : IObj → hProp ℓ-zero
IdentPred c = Identified c , Q.At.identified-prop (Data c) (observe c)

IdentPred-closed : (c d : IObj) → IHom d c → fst (IdentPred c) → fst (IdentPred d)
IdentPred-closed c d f = identified-restrict f

private
  P : (c : IObj) → PSh.F₀ (𝟙 {C = Iv}) c → hProp ℓ-zero
  P c _ = IdentPred c
  closed : (c d : IObj) (f : IHom d c) (b : PSh.F₀ (𝟙 {C = Iv}) c)
         → fst (P c b) → fst (P d (PSh.F₁ (𝟙 {C = Iv}) f b))
  closed c d f b = identified-restrict f

χ-ident : Nat {C = Iv} 𝟙 Ω
χ-ident = Classifier.χ (𝟙 {C = Iv}) P closed

χ-ident-sieve : (c : IObj) → Sieve {C = Iv} c
χ-ident-sieve c = Classifier.χ-sieve (𝟙 {C = Iv}) P closed c tt

-- The naturality proof bundled in χ-ident, under its own name.
χ-ident-nat : (x y : IObj) (f : IHom x y) (b : Unit)
            → χ-ident-sieve x ≡ pull {C = Iv} f (χ-ident-sieve y)
χ-ident-nat x y f b = snd χ-ident x y f tt

ident-classified : (c : IObj) → Identified c → χ-ident-sieve c ≡ maximal {C = Iv} c
ident-classified c = Classifier.classifies-fwd (𝟙 {C = Iv}) P closed c tt

ident-reflected : (c : IObj) → χ-ident-sieve c ≡ maximal {C = Iv} c → Identified c
ident-reflected c = Classifier.classifies-bwd (𝟙 {C = Iv}) P closed c tt

ident-classified-do0 : χ-ident-sieve do0 ≡ maximal {C = Iv} do0
ident-classified-do0 = ident-classified do0 identified-do0

ident-classified-do1 : χ-ident-sieve do1 ≡ maximal {C = Iv} do1
ident-classified-do1 = ident-classified do1 identified-do1

ident-not-classified-obs : ¬ (χ-ident-sieve obs ≡ maximal {C = Iv} obs)
ident-not-classified-obs p = not-identified-obs (ident-reflected obs p)

ident-mem-e0 : fst (fst (χ-ident-sieve obs) do0 e0)
ident-mem-e0 = identified-do0

ident-mem-e1 : fst (fst (χ-ident-sieve obs) do1 e1)
ident-mem-e1 = identified-do1

ident-not-mem-idₒ : ¬ fst (fst (χ-ident-sieve obs) obs idₒ)
ident-not-mem-idₒ = not-identified-obs

-- The untruncated strategies form a presheaf.  A strategy type is
-- a proposition, so the functor laws hold by uniqueness.  The
-- restriction maps come from Topos.IdentificationModels.
StrategiesP : PSh Iv ℓ-zero
StrategiesP = record
  { F₀ = Strategy
  ; F₁ = strategy-restrict
  ; F-id = λ s → Q.At.strategy-prop _ _ _ s
  ; F-comp = λ f g s → Q.At.strategy-prop _ _ _ _
  ; isSetF₀ = λ c → isProp→isSet (Q.At.strategy-prop (Data c) (observe c)) }
