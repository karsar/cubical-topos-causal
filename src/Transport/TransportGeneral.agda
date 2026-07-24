{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportGeneral — the general theorem.
--
-- Transport.Transportability proved the transport result over the
-- concrete two-regime base.  Here it is over an ARBITRARY base
-- category C of regimes and an ARBITRARY presheaf W of worlds, so the
-- result is not an artifact of the toy:
--
--   StablePred W   — a prop-valued predicate on worlds that is
--                    RESTRICTION-STABLE (holds at a world ⟹ holds at
--                    every restriction of it).  This is the causal
--                    condition: a counterfactual true of a situation
--                    is true of every refinement of it.
--
--   chi            — every StablePred is a genuine subobject
--                    χ : W ⇒ Ω, a real natural transformation.
--                    Naturality is proved (via F-comp); the sieve
--                    closure is exactly restriction-stability.
--
--   forced≡pred    — forcing χ at a regime IS the predicate holding
--                    there: the internal truth value computes the
--                    counterfactual.
--
--   transport-invariant — if the counterfactual is forced at a regime
--                    c, it is forced at every regime that restricts
--                    into c.  This is the Kripke locality (⊩-mono)
--                    transported along naturality: transportability is
--                    downward-closed for free.
--
-- This is the structural backbone: counterfactual = restriction-stable
-- predicate = subobject of the world presheaf, transport = forcing,
-- invariance = locality.  The two-regime module is one instance.
--
-- STILL OPEN (the real theorem): the equivalence of this internal
-- "transport = forcing" with the Bareinboim-Pearl s-hedge criterion,
-- and the probabilistic (FDist-kernel) case where restriction-stability
-- is Bayesian-conditioning invariance.  Those are the contribution; this
-- is the verified scaffold they would stand on.
-- ============================================================

module Transport.TransportGeneral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Forcing

module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C
  open PSh

  -- A restriction-stable, prop-valued predicate on a presheaf of worlds.
  record StablePred {ℓw} (W : PSh C ℓw) : Type (ℓ-max (ℓ-suc ℓ) ℓw) where
    field
      pred   : (c : Ob) → F₀ W c → hProp ℓ
      stable : {d c : Ob} (f : Hom d c) (a : F₀ W c)
             → fst (pred c a) → fst (pred d (F₁ W f a))

  module _ {ℓw} {W : PSh C ℓw} (P : StablePred W) where
    open StablePred P

    -- the counterfactual as a sieve at each (regime, world)
    chiSieve : (c : Ob) → F₀ W c → Sieve {C = C} c
    chiSieve c a =
      (λ d g → pred d (F₁ W g a)) ,
      (λ d e' k g pf →
        subst (λ w → fst (pred e' w)) (sym (F-comp W k g a))
              (stable k (F₁ W g a) pf))

    -- …packaged as a genuine subobject χ : W ⇒ Ω (naturality proved).
    chi : Nat W Ω
    chi =
      (λ c a → chiSieve c a) ,
      (λ x y f a →
        Sieve≡ {C = C} (chiSieve x (F₁ W f a)) (pull {C = C} f (chiSieve y a))
          (funExt λ d → funExt λ g → cong (pred d) (sym (F-comp W g f a))))

    -- forcing the subobject at a regime IS the predicate holding there
    forced≡pred : (c : Ob) (a : F₀ W c)
                → _⊩_ {C = C} c (chiSieve c a) ≡ fst (pred c a)
    forced≡pred c a = cong (λ w → fst (pred c w)) (F-id W a)

    -- transportability is downward-closed: forced at c ⟹ forced at every
    -- regime restricting into c.
    transport-invariant : {c : Ob} (a : F₀ W c)
      → _⊩_ {C = C} c (chiSieve c a)
      → {d : Ob} (f : Hom d c) → _⊩_ {C = C} d (chiSieve d (F₁ W f a))
    transport-invariant {c} a h {d} f =
      subst (λ S → _⊩_ {C = C} d S)
            (sym (snd chi d c f a))
            (⊩-mono {C = C} (chiSieve c a) h f)
