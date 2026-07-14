{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Rule3 — internal Pearl Rule 3 (insertion/deletion of
-- actions) on the chain model, lifting RuleDoCalc.rule3-* .
--
-- Rule 3 is UNCONDITIONAL: intervening on the downstream Z leaves
-- an upstream marginal unchanged, because that marginal does not
-- bind kZ at all.  We lift both the X- and (X,Y)-marginal forms
-- pointwise, and give the X-marginal at the level of internal
-- morphisms — which is especially clean, since the X-marginal IS
-- the prior section (marginal-X-fuse), so do(Z)-invariance and
-- naturality are immediate from the prior's naturality.
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

  -- internal chain SCM (bare regime-indexed family)
  SCM₃-E : ∀ {ℓ ℓ' ℓ''} → PSh C ℓ → PSh C ℓ' → PSh C ℓ'' → Type _
  SCM₃-E X Y Z = (c : Ob) → SCM₃ (F₀ X c) (F₀ Y c) (F₀ Z c)

  module _ {ℓ ℓ' ℓ''} {X : PSh C ℓ} {Y : PSh C ℓ'} {Z : PSh C ℓ''} where

    -- internal intervention do(Z := z₀), regime-wise
    do-ZE : ((c : Ob) → F₀ Z c) → SCM₃-E X Y Z → SCM₃-E X Y Z
    do-ZE z₀ m = λ c → do-Z₃ (z₀ c) (m c)

    -- pointwise internal Rule 3 (both forms), lifting the core
    rule3-X-E : (m : SCM₃-E X Y Z) (z₀ : (c : Ob) → F₀ Z c) (c : Ob)
              → marginal-X (do-Z₃ (z₀ c) (m c)) ≡ marginal-X (m c)
    rule3-X-E m z₀ c = rule3-X-marginal (m c) (z₀ c)

    rule3-XY-E : (m : SCM₃-E X Y Z) (z₀ : (c : Ob) → F₀ Z c) (c : Ob)
               → marginal-XY (do-Z₃ (z₀ c) (m c)) ≡ marginal-XY (m c)
    rule3-XY-E m z₀ c = rule3-XY-marginal (m c) (z₀ c)

  -- natural internal chain SCM
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

    -- DERIVED: the X-marginal is natural — it is the prior section
    margX-nat : (M : SCM₃-E-nat X Y Z) (x y : Ob) (f : Hom x y)
              → marginal-X (toFam₃ M x) ≡ mapF (F₁ X f) (marginal-X (toFam₃ M y))
    margX-nat M x y f =
        marginal-X-fuse (toFam₃ M x)
      ∙ pX-nat M x y f
      ∙ cong (mapF (F₁ X f)) (sym (marginal-X-fuse (toFam₃ M y)))

    -- the X-marginal as an internal global element of Dist_E X
    marginalXSection : SCM₃-E-nat X Y Z → Section {C = C} (Dist_E X)
    marginalXSection M =
      (λ c _ → marginal-X (toFam₃ M c)) ,
      (λ x y f _ → margX-nat M x y f)

    -- internal do(Z := z₀) by a regime-coherent value z₀ : 𝟙 ⇒ Z
    do-ZE-nat : Section {C = C} Z → SCM₃-E-nat X Y Z → SCM₃-E-nat X Y Z
    do-ZE-nat z₀ M = record
      { pXs    = pXs M
      ; kYs    = kYs M
      ; kZs    = λ c _ → pure (fst z₀ c tt)
      ; pX-nat = pX-nat M
      ; kY-nat = kY-nat M
      ; kZ-nat = λ x y f b → cong pure (snd z₀ x y f tt)
      }

    -- THE DELIVERABLE: internal Rule 3 (X-marginal) as an equality of
    -- internal morphisms 𝟙 ⇒ Dist_E X — unconditional, naturality derived.
    rule3-X-section : (M : SCM₃-E-nat X Y Z) (z₀ : Section {C = C} Z)
                    → marginalXSection (do-ZE-nat z₀ M) ≡ marginalXSection M
    rule3-X-section M z₀ =
      Nat≡ {X = 𝟙} {Y = Dist_E X} _ _
        (λ c _ → rule3-X-marginal (toFam₃ M c) (fst z₀ c tt))
