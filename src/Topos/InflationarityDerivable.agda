{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.InflationarityDerivable
--
-- The inflationarity law  S ≤ j S  is DERIVABLE from naturality
-- (jnat) together with truth-preservation (j-⊤).  Hence the
-- `j-infl` field of `LawvereTierney` is redundant: a genuine
-- Lawvere–Tierney topology (a *natural* morphism j : Ω ⇒ Ω) is
-- automatically inflationary.
--
-- Argument: for f ∈ S, the pullback  S · f = ⊤  (sieves are
-- downward closed); by naturality  j S · f = j (S · f) = j ⊤ = ⊤,
-- and a sieve equal to ⊤ contains every arrow, so f ∈ j S.
-- ============================================================

module Topos.InflationarityDerivable where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_,_; fst; snd)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Classifier      -- idn∈→maximal , maximal→mem
open import Topos.LawvereTierney

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh
  open LawvereTierney

  j-infl-derivable :
      (J : LawvereTierney {C = C})
      (c : Ob) (S : Sieve {C = C} c) (d : Ob) (f : Hom d c)
    → fst (fst S d f)
    → fst (fst (jop J c S) d f)
  j-infl-derivable J c S d f hf =
    subst (λ g → fst (fst (jop J c S) d g)) (⋆-idL f)
      (maximal→mem {C = C} (pull {C = C} f (jop J c S)) pf-max d idn)
    where
      -- pull f S = ⊤  (f ∈ S, sieves closed under precomposition):
      -- every g ⋆ f lies in S, directly from S's own closure.
      pullS-max : pull {C = C} f S ≡ maximal {C = C} d
      pullS-max =
        Sieve≡ {C = C} (pull {C = C} f S) (maximal {C = C} d)
          (funExt λ e → funExt λ g →
            ⇔toPath {P = fst S e (g ⋆ f)} {Q = Unit* , isPropUnit*}
              (λ _ → tt*)
              (λ _ → snd S d e g f hf))
      -- pull f (j S) = j (pull f S) = j ⊤ = ⊤
      pf-max : pull {C = C} f (jop J c S) ≡ maximal {C = C} d
      pf-max =
        sym (jnat J d c f S)
        ∙ cong (jop J d) pullS-max
        ∙ j-⊤ J d
