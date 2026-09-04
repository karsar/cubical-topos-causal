{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Rule3 — internal Pearl Rule 3 (insertion/deletion of
-- actions) on the chain model, lifting RuleDoCalc.rule3-* .
--
-- The chain model has a prior pX and two kernels, kY from X and
-- kZ from Y.  Rule 3 needs no independence hypothesis.  An
-- intervention on the downstream Z leaves an upstream marginal
-- unchanged, because that marginal never binds kZ.
--
-- We lift the X-marginal and the (X,Y)-marginal forms at each
-- regime.  The X-marginal also holds at the level of internal
-- morphisms.  That case is short, because marginal-X-fuse says
-- the X-marginal is the prior itself.  Invariance under do(Z)
-- and naturality then follow from naturality of the prior.
-- ============================================================

module Topos.Rule3 where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (tt)

open import FDist-Convex using (FDist; pure; mapF)
open import RuleDoCalc using
  ( SCM₃ ; do-Z₃ ; marginal-X ; marginal-XY ; marginal-X-fuse
  ; rule3-X-marginal ; rule3-XY-marginal )

open import Topos.Cat
open import Topos.PSh
open import Topos.InternalDist

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- An internal chain SCM: one SCM₃ per regime, with no
  -- naturality condition.
  SCM₃-E : ∀ {ℓ ℓ' ℓ''} → PSh C ℓ → PSh C ℓ' → PSh C ℓ'' → Type _
  SCM₃-E X Y Z = (c : Ob) → SCM₃ (F₀ X c) (F₀ Y c) (F₀ Z c)

  module _ {ℓ ℓ' ℓ''} {X : PSh C ℓ} {Y : PSh C ℓ'} {Z : PSh C ℓ''} where

    -- The internal intervention do(Z := z₀), applied at each regime.
    do-ZE : ((c : Ob) → F₀ Z c) → SCM₃-E X Y Z → SCM₃-E X Y Z
    do-ZE z₀ m = λ c → do-Z₃ (z₀ c) (m c)

    -- Internal Rule 3 in both forms, one regime at a time, lifting
    -- the core theorems.
    rule3-X-E : (m : SCM₃-E X Y Z) (z₀ : (c : Ob) → F₀ Z c) (c : Ob)
              → marginal-X (do-Z₃ (z₀ c) (m c)) ≡ marginal-X (m c)
    rule3-X-E m z₀ c = rule3-X-marginal (m c) (z₀ c)

    rule3-XY-E : (m : SCM₃-E X Y Z) (z₀ : (c : Ob) → F₀ Z c) (c : Ob)
               → marginal-XY (do-Z₃ (z₀ c) (m c)) ≡ marginal-XY (m c)
    rule3-XY-E m z₀ c = rule3-XY-marginal (m c) (z₀ c)

  -- A natural internal chain SCM.  The prior and both kernels
  -- commute with regime restriction.
  record SCM₃-E-nat {ℓ ℓ' ℓ''} (X : PSh C ℓ) (Y : PSh C ℓ') (Z : PSh C ℓ'')
         : Type (ℓ-max (ℓ-max ℓo ℓh) (ℓ-max ℓ (ℓ-max ℓ' ℓ''))) where
    field
      pXs    : (c : Ob) → FDist (F₀ X c)
      kYs    : (c : Ob) → F₀ X c → FDist (F₀ Y c)
      kZs    : (c : Ob) → F₀ Y c → FDist (F₀ Z c)
      pX-nat : (x y : Ob) (f : Hom x y) → pXs x ≡ mapF (F₁ X f) (pXs y)
      kY-nat : (x y : Ob) (f : Hom x y) (a : F₀ X y)
             → kYs x (F₁ X f a) ≡ mapF (F₁ Y f) (kYs y a)
      kZ-nat : (x y : Ob) (f : Hom x y) (b : F₀ Y y)
             → kZs x (F₁ Y f b) ≡ mapF (F₁ Z f) (kZs y b)

  module _ {ℓ ℓ' ℓ''} {X : PSh C ℓ} {Y : PSh C ℓ'} {Z : PSh C ℓ''} where
    open SCM₃-E-nat

    toFam₃ : SCM₃-E-nat X Y Z → SCM₃-E X Y Z
    toFam₃ M c = record { pX = pXs M c ; kY = kYs M c ; kZ = kZs M c }

    -- Derived: the X-marginal is natural, because it is the prior.
    margX-nat : (M : SCM₃-E-nat X Y Z) (x y : Ob) (f : Hom x y)
              → marginal-X (toFam₃ M x) ≡ mapF (F₁ X f) (marginal-X (toFam₃ M y))
    margX-nat M x y f =
        marginal-X-fuse (toFam₃ M x)
      ∙ pX-nat M x y f
      ∙ cong (mapF (F₁ X f)) (sym (marginal-X-fuse (toFam₃ M y)))

    -- The X-marginal as an internal global element of Dist_E X.
    marginalXSection : SCM₃-E-nat X Y Z → Section {C = C} (Dist_E X)
    marginalXSection M =
      (λ c _ → marginal-X (toFam₃ M c)) ,
      (λ x y f _ → margX-nat M x y f)

    -- Internal do(Z := z₀) for a regime-coherent value z₀ : 𝟙 ⇒ Z.
    do-ZE-nat : Section {C = C} Z → SCM₃-E-nat X Y Z → SCM₃-E-nat X Y Z
    do-ZE-nat z₀ M = record
      { pXs    = pXs M
      ; kYs    = kYs M
      ; kZs    = λ c _ → pure (fst z₀ c tt)
      ; pX-nat = pX-nat M
      ; kY-nat = kY-nat M
      ; kZ-nat = λ x y f b → cong pure (snd z₀ x y f tt)
      }

    -- Internal Rule 3 for the X-marginal, as an equality of
    -- internal morphisms 𝟙 ⇒ Dist_E X.  It carries no hypothesis,
    -- and the naturality is derived.
    rule3-X-section : (M : SCM₃-E-nat X Y Z) (z₀ : Section {C = C} Z)
                    → marginalXSection (do-ZE-nat z₀ M) ≡ marginalXSection M
    rule3-X-section M z₀ =
      Nat≡ {X = 𝟙} {Y = Dist_E X} _ _
        (λ c _ → rule3-X-marginal (toFam₃ M c) (fst z₀ c tt))
