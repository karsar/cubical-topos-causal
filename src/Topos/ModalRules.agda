{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.ModalRules — Stage 2 (d): Pearl Rules 2 and 3 made modal.
--
-- Same pattern as Topos.ModalRule1: each rule's conclusion is an
-- equality of FDists (a proposition, since FDist is a set), so we
-- internalise it into Ω via prop→sieve and show the resulting
-- truth value is j-closed for every Lawvere–Tierney topology.
-- Hence Rules 2 and 3 — like Rule 1 — hold in the internal logic
-- of every sheaf subtopos (j-do-calculus), and in particular at
-- the non-trivial ¬¬ topology.
-- ============================================================

module Topos.ModalRules where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Sigma using (_,_)

open import FDist-Convex using (trunc)
open import Rule2      using (do-X-conf; cond-X-conf; marginal-Y)
open import RuleDoCalc using (do-Z₃; marginal-X)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney
open LawvereTierney
open import Topos.ModalRule1 using (prop→sieve; prop→sieve-true)
open import Topos.Rule2 using (SCM-conf-E; X-indep-Z-E; rule2-Y-E)
open import Topos.Rule3 using (SCM₃-E; rule3-X-E)

-- ----------------------------------------------------------
-- Rule 2 (intervention = conditioning, under X ⫫ Z) made modal.
-- ----------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} (X Z Y : PSh C ℓ)
         (m : SCM-conf-E {C = C} X Z Y)
         (ind : X-indep-Z-E {C = C} {X = X} {Z = Z} {Y = Y} m)
         (x₀ : (c : Precategory.Ob C) → PSh.F₀ X c) where
  open Precategory C

  rule2-prop : (c : Ob) → hProp ℓ
  rule2-prop c =
    ( marginal-Y (do-X-conf (x₀ c) (m c))
      ≡ marginal-Y (cond-X-conf (x₀ c) (m c) (ind c)) )
    , trunc _ _

  rule2-Ω : (c : Ob) → Sieve {C = C} c
  rule2-Ω c = prop→sieve {C = C} c (rule2-prop c)

  rule2-Ω-true : (c : Ob) → rule2-Ω c ≡ maximal {C = C} c
  rule2-Ω-true c =
    prop→sieve-true {C = C} c (rule2-prop c)
      (rule2-Y-E {C = C} {X = X} {Z = Z} {Y = Y} m ind x₀ c)

  modal-rule2 : (J : LawvereTierney {C = C}) (c : Ob)
              → is-j-closed J c (rule2-Ω c)
  modal-rule2 J c =
    cong (jop J c) e ∙ j-⊤ J c ∙ sym e
    where
      e : rule2-Ω c ≡ maximal {C = C} c
      e = rule2-Ω-true c

-- ----------------------------------------------------------
-- Rule 3 (deleting a downstream action leaves an upstream marginal
-- unchanged) made modal.
-- ----------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} (X Y Z : PSh C ℓ)
         (m : SCM₃-E {C = C} X Y Z)
         (z₀ : (c : Precategory.Ob C) → PSh.F₀ Z c) where
  open Precategory C

  rule3-prop : (c : Ob) → hProp ℓ
  rule3-prop c =
    ( marginal-X (do-Z₃ (z₀ c) (m c)) ≡ marginal-X (m c) )
    , trunc _ _

  rule3-Ω : (c : Ob) → Sieve {C = C} c
  rule3-Ω c = prop→sieve {C = C} c (rule3-prop c)

  rule3-Ω-true : (c : Ob) → rule3-Ω c ≡ maximal {C = C} c
  rule3-Ω-true c =
    prop→sieve-true {C = C} c (rule3-prop c)
      (rule3-X-E {C = C} {X = X} {Y = Y} {Z = Z} m z₀ c)

  modal-rule3 : (J : LawvereTierney {C = C}) (c : Ob)
              → is-j-closed J c (rule3-Ω c)
  modal-rule3 J c =
    cong (jop J c) e ∙ j-⊤ J c ∙ sym e
    where
      e : rule3-Ω c ≡ maximal {C = C} c
      e = rule3-Ω-true c
