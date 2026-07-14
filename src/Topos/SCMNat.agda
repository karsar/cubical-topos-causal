{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.SCMNat — NATURAL internal SCMs, closing the gap left by
-- Topos.Rule1.rule1-E-nat.
--
-- A natural internal SCM carries, beyond the regime-wise data,
-- the coherence with restriction:
--   * the prior is a section of Dist_E X   (pX-nat),
--   * the kernel is a natural transformation X ⇒ Dist_E Y (kY-nat).
-- From these we DERIVE that the internal Y-marginal is natural
-- (marg-nat) — so it is a genuine internal global element
-- (marginalSection), with no naturality taken as hypothesis.
--
-- Intervention is by a SECTION x₀ : 𝟙 ⇒ X (a regime-coherent
-- value); the intervened SCM is again natural.  Internal Rule 1
-- then holds as an equality of internal morphisms 𝟙 ⇒ Dist_E Y,
-- fully derived.
-- ============================================================

module Topos.SCMNat where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; snd; fst)
open import Cubical.Data.Unit using (tt)

open import FDist-Convex using (FDist; pure; _>>=_; mapF)
open import RuleDoCalc   using (SCM₂; joint-of; do-X; Y-indep-X;
                                marginal-Y-fuse; rule1-marginal)

open import Topos.Cat
open import Topos.PSh
open import Topos.InternalDist
open import Topos.SCM

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- a natural internal SCM
  record SCM-E-nat {ℓ ℓ'} (X : PSh C ℓ) (Y : PSh C ℓ')
         : Type (ℓ-max (ℓ-max ℓo ℓh) (ℓ-max ℓ ℓ')) where
    field
      pXs    : (c : Ob) → FDist (F₀ X c)
      kYs    : (c : Ob) → F₀ X c → FDist (F₀ Y c)
      pX-nat : (x y : Ob) (f : Hom x y) → pXs x ≡ mapF (F₁ X f) (pXs y)
      kY-nat : (x y : Ob) (f : Hom x y) (a : F₀ X y)
             → kYs x (F₁ X f a) ≡ mapF (F₁ Y f) (kYs y a)

  module _ {ℓ ℓ'} {X : PSh C ℓ} {Y : PSh C ℓ'} where
    open SCM-E-nat

    -- underlying regime-wise family
    toFam : SCM-E-nat X Y → SCM-E {C = C} X Y
    toFam M c = record { pX = pXs M c ; kY = kYs M c }

    -- structural independence, on the underlying family
    Indep-E-nat : SCM-E-nat X Y → Type (ℓ-max ℓo (ℓ-max ℓ ℓ'))
    Indep-E-nat M = (c : Ob) → Y-indep-X (toFam M c)

    -- DERIVED: the internal Y-marginal is natural
    marg-nat : (M : SCM-E-nat X Y) (x y : Ob) (f : Hom x y)
             → mapF snd (joint-of (toFam M x))
               ≡ mapF (F₁ Y f) (mapF snd (joint-of (toFam M y)))
    marg-nat M x y f =
        marginal-Y-fuse (toFam M x)
      ∙ cong (_>>= kYs M x) (pX-nat M x y f)
      ∙ mapF-bindL (F₁ X f) (pXs M y) (kYs M x)
      ∙ cong (pXs M y >>=_) (funExt (λ a → kY-nat M x y f a))
      ∙ sym (mapF-bindR (F₁ Y f) (pXs M y) (kYs M y))
      ∙ cong (mapF (F₁ Y f)) (sym (marginal-Y-fuse (toFam M y)))

    -- the internal Y-marginal as a genuine internal global element
    marginalSection : SCM-E-nat X Y → Section {C = C} (Dist_E Y)
    marginalSection M =
      (λ c _ → mapF snd (joint-of (toFam M c))) ,
      (λ x y f _ → marg-nat M x y f)

    -- internal intervention by a regime-coherent value x₀ : 𝟙 ⇒ X
    do-XE-nat : Section {C = C} X → SCM-E-nat X Y → SCM-E-nat X Y
    do-XE-nat x₀ M = record
      { pXs    = λ c → pure (fst x₀ c tt)
      ; kYs    = kYs M
      ; pX-nat = λ x y f → cong pure (snd x₀ x y f tt)
      ; kY-nat = kY-nat M
      }

    -- THE GAP CLOSED: internal Rule 1 as an equality of internal
    -- morphisms 𝟙 ⇒ Dist_E Y, with marginal naturality DERIVED.
    rule1-E-section : (M : SCM-E-nat X Y) (ind : Indep-E-nat M) (x₀ : Section {C = C} X)
                    → marginalSection (do-XE-nat x₀ M) ≡ marginalSection M
    rule1-E-section M ind x₀ =
      Nat≡ {X = 𝟙} {Y = Dist_E Y} _ _
        (λ c _ → rule1-marginal (toFam M c) (ind c) (fst x₀ c tt))
