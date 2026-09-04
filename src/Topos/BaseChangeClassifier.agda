{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.BaseChangeClassifier — classification commutes with
-- base change.
--
-- Fix a base functor F : C → D, a coarse value presheaf Y on D,
-- and a coarse intervened value y₀ : Section Y.  Pull both back
-- along F: the fine world is basePull F Y, and the fine
-- intervened value is pullSect.  Two classifiers are then in
-- play.  The coarse classifier χ_D of (Y, y₀) can be pulled
-- back and composed with the comparison map φB.  The fine
-- classifier χ_C of the pulled-back pair can be built directly.
--
-- THEOREM (χ-pull, χ-pull-Nat): the two agree, for EVERY base
-- functor, with no side condition.  Pointwise the proof is
-- refl: each component of the fine classifier unfolds to the
-- corresponding coarse component.
--
-- COROLLARY (pulled-target-classified): the value the coarse
-- intervention forces, read on the fine site through φB, is
-- classified true.  Abstraction and classification of the
-- intervention target commute.
--
-- Contrast with Topos.MergeAbstraction: Ω itself does NOT
-- transfer along every F.  The classifier of a named target
-- does.  Targets are stable under abstraction; the full space
-- of truth values is not.
-- ============================================================

module Topos.BaseChangeClassifier where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_,_; fst; snd)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.BaseChange
open import Topos.DoClassifier using (χ-sieve; χ; pt; do-classified)

module _ {ℓ} {C : Precategory ℓ ℓ} {D : Precategory ℓ ℓ}
         (F : BaseFunctor C D) (Y : PSh D ℓ) (y₀ : Section {C = D} Y) where
  private
    module Cc = Precategory C
    module Dc = Precategory D
  open BaseFunctor F
  open PSh

  -- ----------------------------------------------------------
  -- The pulled-back intervened value.  Its point at c is the
  -- coarse point at App₀ c, and its naturality is the coarse
  -- naturality at the image arrows.
  -- ----------------------------------------------------------
  pullSect : Section {C = C} (basePull F Y)
  pullSect = (λ c a → fst y₀ (App₀ c) a)
           , (λ x y f a → snd y₀ (App₀ x) (App₀ y) (App₁ f) a)

  -- ----------------------------------------------------------
  -- THEOREM, sieve level.  The preimage of the coarse
  -- classifying sieve is the fine classifying sieve.
  -- ----------------------------------------------------------
  χ-pull : (c : Cc.Ob) (b : F₀ Y (App₀ c))
         → φB F c (χ-sieve Y y₀ (App₀ c) b)
         ≡ χ-sieve (basePull F Y) pullSect c b
  χ-pull c b = Sieve≡ {C = C} _ _ (funExt λ d → funExt λ f → refl)

  -- ----------------------------------------------------------
  -- THEOREM, morphism level.  As maps of presheaves:
  -- φNat ∘ basePull(χ_D) = χ_C.  This is the display form the
  -- paper quotes.
  -- ----------------------------------------------------------
  private
    compNat : ∀ {ℓa ℓb ℓc} {A : PSh C ℓa} {B : PSh C ℓb} {Z : PSh C ℓc}
            → Nat {C = C} A B → Nat {C = C} B Z → Nat {C = C} A Z
    compNat (α , αn) (β , βn) =
      (λ c a → β c (α c a))
      , (λ x y f a → cong (β x) (αn x y f a) ∙ βn x y f (α y a))

  χ-pull-Nat : compNat {A = basePull F Y} {B = basePull F (Ω {C = D})}
                       {Z = Ω {C = C}}
                       (basePullNat F {Y = Y} {Z = Ω {C = D}} (χ Y y₀))
                       (φNat F)
             ≡ χ (basePull F Y) pullSect
  χ-pull-Nat = Nat≡ {X = basePull F Y} {Y = Ω {C = C}} _ _
                    (λ c b → χ-pull c b)

  -- ----------------------------------------------------------
  -- COROLLARY.  The coarse intervention's forced value, seen on
  -- the fine site, is classified true.
  -- ----------------------------------------------------------
  pulled-target-classified : (c : Cc.Ob)
    → φB F c (χ-sieve Y y₀ (App₀ c) (pt Y y₀ (App₀ c)))
    ≡ maximal {C = C} c
  pulled-target-classified c =
    χ-pull c (pt Y y₀ (App₀ c)) ∙ do-classified (basePull F Y) pullSect c
