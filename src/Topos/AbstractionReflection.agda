{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.AbstractionReflection: local order-reflection is weaker
-- than global order-reflection.
--
-- The second tier of Topos.AbstractionTiers uses ReflectAt c: an
-- arrow F x → F y lifts to x → y when x and y both map to c.
-- Reflect asks the same for every x and y.
--
-- The collapse of a discrete two-object category to a point
-- shows the difference.  It has the back condition (BackCond∥:
-- each object over an image is itself an image).  It also has
-- ReflectAt at each object.  It fails Reflect: an identity joins
-- the two images, and no arrow joins the two objects.
--
-- When C has a greatest context, every object maps to it, and
-- ReflectAt at that context gives Reflect.
--
-- Results:
--   anchored-at-top→global   ReflectAt top ⇒ Reflect.
--   collapse-back            the collapse has the back condition,
--   collapse-anchored        and ReflectAt at each object,
--   collapse-not-global      but not Reflect.
-- ============================================================

module Topos.AbstractionReflection where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; false≢true)
open import Cubical.Data.Unit using (Unit; tt; isSetUnit; isPropUnit)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_)
open import Topos.Cat
open import Topos.BaseChange
open import Topos.AbstractionTiers
open import Topos.ContingentCI using (DiscreteCat)

module _ {ℓ} {C D : Precategory ℓ ℓ} (F : BaseFunctor C D)
         (top : Precategory.Ob C)
         (below-top : (x : Precategory.Ob C) → Precategory.Hom C x top) where

  anchored-at-top→global : ReflectAt F top → Reflect F
  anchored-at-top→global local {x} {y} h = local (below-top x) (below-top y) h

DiscreteTwo = DiscreteCat Bool isSetBool
Point = DiscreteCat Unit isSetUnit

collapse : BaseFunctor DiscreteTwo Point
collapse = record
  { App₀ = λ _ → tt ; App₁ = λ _ → refl
  ; App-id = λ _ → refl ; App-⋆ = λ _ _ → refl }

collapse-back : BackCond∥ collapse
collapse-back c d h = ∣ c , refl , isPropUnit tt d ∣₁

collapse-anchored : (c : Bool) → ReflectAt collapse c
collapse-anchored c gx gy h = gx ∙ sym gy

collapse-not-global : ¬ (Reflect collapse)
collapse-not-global reflect = false≢true (reflect {false} {true} refl)
