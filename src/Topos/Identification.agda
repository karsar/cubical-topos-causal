{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Identification: identification as a property of models
-- and data.
--
-- Fix a type of models, a set Target of answers, and a query
-- q : Model → Target.  A data interface is an observation map
-- observe : Model → Data.  It says which data are available.
--
-- A model need not produce every element of Data.  RealData
-- keeps the data that some model produces.  A STRATEGY is a
-- function RealData → Target that returns q m for every model m
-- that produces the data.
--
-- IDENTIFIED is the usual semantic condition: two models with the
-- same data agree on the query.  We prove that a strategy exists
-- exactly when the query is identified.  The proof uses no
-- acyclicity, no decidability and no choice.
--
-- Results:
--   strategy-prop              two strategies on one interface are
--                              equal.
--   strategy≃identified        Strategy ≃ Identified.
--   mere-strategy≃identified   ∥ Strategy ∥₁ ≃ Identified.
--   identified-refines,        identification persists when new
--   strategy-refines           data recover the old data.
--   strategies-set             over a SET of interface names, all
--                              strategies form an h-set.
--   strategies≃valid-footprints  strategies are equivalent to
--                              the valid names.
--
-- The names must form a set.  A set of input types is not
-- enough: the universe of h-sets has non-trivial automorphisms,
-- such as negation on Bool, so it is not itself a set.
-- ============================================================

module Topos.Identification where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd; Σ≡Prop)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁; ∣_∣₁; squash₁)

module Query {ℓ} (Model Target : Type ℓ) (target-set : isSet Target)
             (query : Model → Target) where

  module At (Data : Type ℓ) (observe : Model → Data) where

    RealData : Type ℓ
    RealData = Σ[ d ∈ Data ] ∥ Σ[ m ∈ Model ] (observe m ≡ d) ∥₁

    Correct : (RealData → Target) → Type ℓ
    Correct f = (d : RealData) (m : Model)
              → observe m ≡ fst d → f d ≡ query m

    correct-prop : (f : RealData → Target) → isProp (Correct f)
    correct-prop f = isPropΠ λ d → isPropΠ λ m → isPropΠ λ _ → target-set _ _

    Strategy : Type ℓ
    Strategy = Σ[ f ∈ (RealData → Target) ] Correct f

    -- Two strategies agree on each realisable input.  Correctness
    -- gives this from the model that realises the input.
    strategy-prop : isProp Strategy
    strategy-prop (f , pf) (g , pg) = Σ≡Prop correct-prop
      (funExt λ d → PT.rec (target-set _ _)
        (λ { (m , p) → pf d m p ∙ sym (pg d m p) }) (snd d))

    Identified : Type ℓ
    Identified = (m n : Model) → observe m ≡ observe n → query m ≡ query n

    identified-prop : isProp Identified
    identified-prop = isPropΠ λ m → isPropΠ λ n → isPropΠ λ _ → target-set _ _

    strategy→identified : Strategy → Identified
    strategy→identified (f , correct) m n eq =
      sym (correct d m refl) ∙ correct d n (sym eq)
      where
      d : RealData
      d = observe m , ∣ m , refl ∣₁

    -- A realising model exists only under truncation.  But the type
    -- of answers compatible with the data is a proposition, so the
    -- truncation eliminates into it.  No choice is needed.
    identified→strategy : Identified → Strategy
    identified→strategy compatible = (λ d → fst (answer d)) ,
      (λ d m p → snd (answer d) m p)
      where
      Answer : RealData → Type ℓ
      Answer d = Σ[ t ∈ Target ] ((m : Model) → observe m ≡ fst d → t ≡ query m)

      answer-prop : (d : RealData) → isProp (Answer d)
      answer-prop d (t , pt) (u , pu) =
        Σ≡Prop (λ _ → isPropΠ λ m → isPropΠ λ _ → target-set _ _)
          (PT.rec (target-set _ _)
            (λ { (m , p) → pt m p ∙ sym (pu m p) }) (snd d))

      answer : (d : RealData) → Answer d
      answer d = PT.rec (answer-prop d)
        (λ { (m , p) → query m , λ n q → compatible m n (p ∙ sym q) }) (snd d)

    strategy≃identified : Strategy ≃ Identified
    strategy≃identified = isoToEquiv
      (iso strategy→identified identified→strategy
        (λ p → identified-prop _ p) (λ s → strategy-prop _ s))

    -- Pearl's identifiable-or-not proposition.  We prove it equal to
    -- the truncation of strategies.  We do not define it that way.
    mere-strategy→identified : ∥ Strategy ∥₁ → Identified
    mere-strategy→identified = PT.rec identified-prop strategy→identified

    identified→mere-strategy : Identified → ∥ Strategy ∥₁
    identified→mere-strategy p = ∣ identified→strategy p ∣₁

    mere-strategy≃identified : ∥ Strategy ∥₁ ≃ Identified
    mere-strategy≃identified = isoToEquiv
      (iso mere-strategy→identified identified→mere-strategy
        (λ p → identified-prop _ p) (λ s → squash₁ _ s))

  -- REFINEMENT.  forget recovers the old data from the new data,
  -- for every model.  Identification then carries over.
  module Refinement (D E : Type ℓ) (old : Model → D) (new : Model → E)
                    (forget : E → D)
                    (recovers : (m : Model) → forget (new m) ≡ old m) where

    identified-refines : At.Identified D old → At.Identified E new
    identified-refines identified m n eq =
      identified m n (sym (recovers m) ∙ cong forget eq ∙ recovers n)

    strategy-refines : At.Strategy D old → At.Strategy E new
    strategy-refines s = At.identified→strategy E new
      (identified-refines (At.strategy→identified D old s))

  module Footprints (Footprint : Type ℓ) (footprint-set : isSet Footprint)
                    (Data : Footprint → Type ℓ)
                    (observe : (a : Footprint) → Model → Data a) where

    Strategies : Type ℓ
    Strategies = Σ[ a ∈ Footprint ] At.Strategy (Data a) (observe a)

    ValidFootprints : Type ℓ
    ValidFootprints = Σ[ a ∈ Footprint ] At.Identified (Data a) (observe a)

    strategies-set : isSet Strategies
    strategies-set = isSetΣ footprint-set
      (λ a → isProp→isSet (At.strategy-prop (Data a) (observe a)))

    strategies≃valid-footprints : Strategies ≃ ValidFootprints
    strategies≃valid-footprints = isoToEquiv
      (iso
        (λ { (a , s) → a , At.strategy→identified (Data a) (observe a) s })
        (λ { (a , p) → a , At.identified→strategy (Data a) (observe a) p })
        (λ _ → Σ≡Prop (λ a → At.identified-prop (Data a) (observe a)) refl)
        (λ _ → Σ≡Prop (λ a → At.strategy-prop (Data a) (observe a)) refl))
