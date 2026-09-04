{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.MechanismSeparation — Ω does separate surgery from
-- observation, once it is pointed at mechanisms.
--
-- Topos.MechanismObject builds the classifier χ-do on the
-- mechanism object.  A classifier is only worth having if it
-- discriminates, so this module exhibits the two mechanisms the
-- paper's Section on the do-operator compares, and shows the
-- classifier tells them apart.
--
-- The base is a single context, which is the sharpest setting
-- for the question: no refinement is available, so nothing here
-- is an artefact of the site.
--
--   const-mech   the mechanism do(X := x₀) installs.  It ignores
--                its parents and returns the point mass at x₀.
--   copy-mech    the mechanism that reads its parent.  This is
--                the confounded mechanism of the do-vs-see
--                theorem, where observing X = x₀ leaves the
--                parent free.
--
-- Results:
--   const-admissible    χ-do classifies const-mech as true.
--   copy-not-admissible copy-mech is not admissible.
--   χ-do-separates      the two classifying sieves differ.
--
-- So the route the paper leaves open closes, and it closes in
-- the affirmative: the obstruction was the choice of object, not
-- the classifier.  The value-fixing subobject cannot separate
-- the two operations; the mechanism object can.
-- ============================================================

module Topos.MechanismSeparation where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit; tt; isPropUnit; isSetUnit)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥)

open import FDist-Convex using (FDist; pure; trunc; 𝔼)
open import WeightQ using (Weight; w0; w1; w0≢w1)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.Exponential
open import Topos.MechanismObject

-- ------------------------------------------------------------
-- The one-context base.
-- ------------------------------------------------------------
Pt : Precategory ℓ-zero ℓ-zero
Pt = record
  { Ob = Unit ; Hom = λ _ _ → Unit ; idn = tt ; _⋆_ = λ _ _ → tt
  ; ⋆-idL = λ _ → refl ; ⋆-idR = λ _ → refl ; ⋆-assoc = λ _ _ _ → refl
  ; isSetHom = isProp→isSet isPropUnit }

-- Parents and values are both Bool at the single context.
BoolP : PSh Pt ℓ-zero
BoolP = record
  { F₀ = λ _ → Bool ; F₁ = λ _ b → b
  ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → isSetBool }

-- The fixed value: true.
x₀ : Section {C = Pt} BoolP
x₀ = (λ _ _ → true) , (λ _ _ _ _ → refl)

-- ------------------------------------------------------------
-- The two mechanisms.
-- ------------------------------------------------------------
-- do(X := true): ignore the parent, return the point mass at true.
const-mech : PSh.F₀ (Mech BoolP BoolP x₀) tt
const-mech = (λ _ _ _ → pure true) , (λ _ _ _ _ _ → refl)

-- The confounded mechanism: read the parent.
copy-mech : PSh.F₀ (Mech BoolP BoolP x₀) tt
copy-mech = (λ _ _ p → pure p) , (λ _ _ _ _ _ → refl)

-- ------------------------------------------------------------
-- The classifier discriminates.
-- ------------------------------------------------------------
const-admissible : fst (Adm BoolP BoolP x₀ tt const-mech)
const-admissible _ _ _ = refl

-- copy-mech fails admissibility, witnessed at the parent value
-- false: it returns the point mass at false, not at true.
-- The indicator of true, used to read the two point masses apart
-- in the weight algebra, as the do-vs-see theorem does.
indTrue : Bool → Weight
indTrue true  = w1
indTrue false = w0

copy-not-admissible : ¬ (fst (Adm BoolP BoolP x₀ tt copy-mech))
copy-not-admissible adm = w0≢w1 (cong (λ d → 𝔼 d indTrue) (adm tt tt false))

-- The two classifying sieves are different, so the classifier
-- separates the intervention from the mechanism that reads its
-- parent.
χ-do-separates : ¬ (χ-do-sieve BoolP BoolP x₀ tt const-mech
                  ≡ χ-do-sieve BoolP BoolP x₀ tt copy-mech)
χ-do-separates p =
  copy-not-admissible
    (snd (χ-do-classifies BoolP BoolP x₀ tt copy-mech)
      (sym p ∙ fst (χ-do-classifies BoolP BoolP x₀ tt const-mech) const-admissible))
