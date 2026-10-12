{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.IdentificationModels: two causal models that the
-- observational data cannot tell apart.
--
-- Both models have a fair latent coin U and X = U.
--   model false :  Y = U     (U confounds X and Y)
--   model true  :  Y = X     (X causes Y)
-- The observational joints are equal.  The query is
-- Pr(Y = true | do(X = true)).  It is 1/2 in model false and 1 in
-- model true, so observation does not identify it.
--
-- Under either intervention the models differ, so each
-- interventional dataset identifies the query.  Every claim here
-- is relative to THIS two-model class.  We claim nothing about
-- arbitrary SCMs or experimental designs.
--
-- Results:
--   query-distinct         the two query values differ.
--   same-observations      the observational joints are equal.
--   not-identified-obs     so obs does not identify the query.
--   identified-do0/do1     each intervention does.
--   strategy-do0/do1       the corresponding strategies.
--   identified-restrict    the predicate is closed under restriction.
--   strategies-distinct    two interface names give two strategies,
--   truncation-loses-information   with equal truncations.
-- ============================================================

module Topos.IdentificationModels where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)

open import FDist-Convex using (FDist; pure; mix; _>>=_; 𝔼; 𝔼-bind; trunc;
  mix-w; mix-w-right-w0; mix-w-idem)
open import WeightQ
open import Topos.Identification
open import Topos.InterventionSite

Model = Bool

prior : FDist Bool
prior = mix wHalf (pure true) (pure false)

outcome : Model → Bool → Bool → Bool
outcome false u x = u
outcome true  u x = x

observational : Model → FDist (Bool × Bool)
observational m = prior >>= λ u → pure (u , outcome m u u)

interventional : Bool → Model → FDist Bool
interventional x m = prior >>= λ u → pure (outcome m u x)

indicator : Bool → Weight
indicator true = w1
indicator false = w0

query : Model → Weight
query m = 𝔼 (interventional true m) indicator

readout : mix-w wHalf w1 w0 ≡ wHalf
readout = mix-w-right-w0 wHalf w1 ∙ *w-1 wHalf

query-confounded : query false ≡ wHalf
query-confounded = 𝔼-bind prior (λ u → pure u) indicator ∙ readout

query-direct : query true ≡ w1
query-direct = 𝔼-bind prior (λ _ → pure true) indicator ∙ mix-w-idem wHalf w1

query-distinct : ¬ (query false ≡ query true)
query-distinct p = wHalf≢w1 (sym query-confounded ∙ p ∙ query-direct)

same-observations : observational false ≡ observational true
same-observations = refl

Data : IObj → Type
Data obs = FDist (Bool × Bool)
Data do0 = FDist Bool
Data do1 = FDist Bool

observe : (c : IObj) → Model → Data c
observe obs = observational
observe do0 = interventional false
observe do1 = interventional true

module Q = Query Model Weight isSetWeight query

Strategy : IObj → Type
Strategy c = Q.At.Strategy (Data c) (observe c)

Identified : IObj → Type
Identified c = Q.At.Identified (Data c) (observe c)

not-identified-obs : ¬ (Identified obs)
not-identified-obs identified = query-distinct (identified false true same-observations)

identified-do1 : Identified do1
identified-do1 m n p = cong (λ d → 𝔼 d indicator) p

-- The do(X = false) data also distinguish the models.
-- The outcome rates are 1/2 and 0.
zero-confounded : 𝔼 (interventional false false) indicator ≡ wHalf
zero-confounded = query-confounded

zero-direct : 𝔼 (interventional false true) indicator ≡ w0
zero-direct = 𝔼-bind prior (λ _ → pure false) indicator ∙ mix-w-idem wHalf w0

zero-distinct : ¬ (interventional false false ≡ interventional false true)
zero-distinct p = ¬Pos-w0
  (subst Pos (sym zero-confounded ∙ cong (λ d → 𝔼 d indicator) p ∙ zero-direct) Pos-wHalf)

identified-do0 : Identified do0
identified-do0 false false p = refl
identified-do0 true true p = refl
identified-do0 false true p = E.rec (zero-distinct p)
identified-do0 true false p = E.rec (zero-distinct (sym p))

strategy-do0 : Strategy do0
strategy-do0 = Q.At.identified→strategy (Data do0) (observe do0) identified-do0

strategy-do1 : Strategy do1
strategy-do1 = Q.At.identified→strategy (Data do1) (observe do1) identified-do1

no-strategy-obs : ¬ (Strategy obs)
no-strategy-obs s = not-identified-obs (Q.At.strategy→identified (Data obs) (observe obs) s)

-- Restriction maps.  At obs there is no strategy, by the proof
-- above, so the arrows e0 and e1 have an empty source.
strategy-restrict : {c d : IObj} → IHom d c → Strategy c → Strategy d
strategy-restrict idₒ s = s
strategy-restrict id₀ s = s
strategy-restrict id₁ s = s
strategy-restrict e0 s = E.rec (no-strategy-obs s)
strategy-restrict e1 s = E.rec (no-strategy-obs s)

identified-restrict : {c d : IObj} → IHom d c → Identified c → Identified d
identified-restrict idₒ p = p
identified-restrict id₀ p = p
identified-restrict id₁ p = p
identified-restrict e0 p = E.rec (not-identified-obs p)
identified-restrict e1 p = E.rec (not-identified-obs p)

-- Two named data interfaces, one per intervention.  Both carry a
-- correct strategy.  They are experimental datasets.  They are not
-- graphical adjustment sets.
data Footprint : Type where
  zero-data one-data : Footprint

which : Footprint → IObj
which zero-data = do0
which one-data = do1

-- The names form a set because they are a retract of Bool.
code : Footprint → Bool
code zero-data = false
code one-data = true

decode : Bool → Footprint
decode false = zero-data
decode true = one-data

decode-code : (a : Footprint) → decode (code a) ≡ a
decode-code zero-data = refl
decode-code one-data = refl

open import Cubical.Data.Bool using (isSetBool; false≢true)
open import Cubical.Foundations.HLevels using (isSetRetract)

footprint-set : isSet Footprint
footprint-set = isSetRetract code decode decode-code isSetBool

module Named = Q.Footprints Footprint footprint-set
  (λ a → Data (which a)) (λ a → observe (which a))

zero-strategy one-strategy : Named.Strategies
zero-strategy = zero-data , strategy-do0
one-strategy = one-data , strategy-do1

strategies-distinct : ¬ (zero-strategy ≡ one-strategy)
strategies-distinct p = false≢true (cong (λ s → code (fst s)) p)

truncation-loses-information :
  (¬ (zero-strategy ≡ one-strategy)) ×
  (Path ∥ Named.Strategies ∥₁ ∣ zero-strategy ∣₁ ∣ one-strategy ∣₁)
truncation-loses-information = strategies-distinct , squash₁ _ _
