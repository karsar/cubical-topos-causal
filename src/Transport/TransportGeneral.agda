{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.TransportGeneral — the general theorem.
--
-- Transport.Transportability proves the transport result over one
-- concrete base with two regimes.  This module proves it over an
-- arbitrary base category C of regimes and an arbitrary presheaf W
-- of worlds.  The result then does not depend on the small example.
--
-- The pieces:
--
--   StablePred W   — a prop-valued predicate on worlds that is
--                    RESTRICTION-STABLE.  Restriction-stable means
--                    this: if the predicate holds at a world, it
--                    holds at every restriction of that world.  In
--                    causal terms, a counterfactual true of a
--                    situation stays true of every refinement of it.
--
--   chi            — each StablePred gives a subobject χ : W ⇒ Ω,
--                    a natural transformation.  Naturality is proved
--                    from F-comp.  The sieve closure condition is
--                    restriction-stability.
--
--   forced≡pred    — forcing χ at a regime equals the predicate
--                    holding at that regime.  The internal truth
--                    value computes the counterfactual.
--
--   transport-invariant — if the counterfactual is forced at a
--                    regime c, it is forced at every regime that
--                    restricts into c.  The proof transports Kripke
--                    locality (⊩-mono) along naturality, so
--                    transportability is downward-closed.
--
-- The structure, in one line each.  A counterfactual is a
-- restriction-stable predicate.  Such a predicate is a subobject of
-- the world presheaf.  Transport is forcing, and invariance is
-- locality.  The two-regime module is one instance of this.
--
-- STILL OPEN (the real theorem).  Two items.  First, the equivalence
-- of this internal "transport = forcing" with the Bareinboim-Pearl
-- s-hedge criterion.  Second, the probabilistic (FDist-kernel) case,
-- where restriction-stability becomes invariance under Bayesian
-- conditioning.  Those two are the contribution.  This module is the
-- verified scaffold they would stand on.
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

  -- A prop-valued predicate on worlds, stable under restriction.
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

    -- The same sieves, packaged as a subobject χ : W ⇒ Ω.
    -- Naturality is proved here.
    chi : Nat W Ω
    chi =
      (λ c a → chiSieve c a) ,
      (λ x y f a →
        Sieve≡ {C = C} (chiSieve x (F₁ W f a)) (pull {C = C} f (chiSieve y a))
          (funExt λ d → funExt λ g → cong (pred d) (sym (F-comp W g f a))))

    -- Forcing the subobject at a regime is the predicate holding
    -- at that regime.
    forced≡pred : (c : Ob) (a : F₀ W c)
                → _⊩_ {C = C} c (chiSieve c a) ≡ fst (pred c a)
    forced≡pred c a = cong (λ w → fst (pred c w)) (F-id W a)

    -- Transportability is downward-closed.  Forced at c gives forced
    -- at every regime restricting into c.
    transport-invariant : {c : Ob} (a : F₀ W c)
      → _⊩_ {C = C} c (chiSieve c a)
      → {d : Ob} (f : Hom d c) → _⊩_ {C = C} d (chiSieve d (F₁ W f a))
    transport-invariant {c} a h {d} f =
      subst (λ S → _⊩_ {C = C} d S)
            (sym (snd chi d c f a))
            (⊩-mono {C = C} (chiSieve c a) h f)
