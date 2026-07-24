{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.LawvereTierney — Stage 2.  A Lawvere–Tierney topology
-- j : Ω → Ω on the subobject classifier of the presheaf topos.
--
-- This is the internal counterpart of a Grothendieck topology /
-- a lex modality ◯ (Rijke–Shulman–Spitters): j picks out the
-- "covered" / j-dense sieves, and the j-closed subobjects form a
-- sub-(∞-)topos.  In the causal reading (translation.md:25,
-- outline.md:85), j is the modality of Mahadevan's j-do-calculus,
-- and "j-stable discovery" = ◯-modal structure.
--
-- We use MacLane–Moerdijk's three axioms (Sheaves in Geometry &
-- Logic, V.1):
--     j ∘ true  = true        (j preserves ⊤)
--     j ∘ j     = j           (idempotent)
--     j (S ∧ T) = j S ∧ j T   (preserves meets)
-- Monotonicity is derivable from meet-preservation, so we omit it.
--
-- Internal meet ∧ on Ω (pointwise sieve intersection) is built
-- first, since the third axiom needs it.
-- ============================================================

module Topos.LawvereTierney where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic using (_⊓_)
open import Cubical.Data.Sigma using (_,_; fst; snd; _×_)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- ----------------------------------------------------------
  -- Internal meet of sieves = pointwise conjunction of
  -- membership.  Closure under precomposition is componentwise.
  -- ----------------------------------------------------------
  _∧S_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _∧S_ {c} S T =
    (λ d f → fst S d f ⊓ fst T d f) ,
    (λ d e k f pf → (snd S d e k f (fst pf) , snd T d e k f (snd pf)))

  -- ----------------------------------------------------------
  -- A Lawvere–Tierney topology on Ω.
  -- ----------------------------------------------------------
  -- jop is the bare regime-wise operation; jnat makes it a genuine
  -- internal morphism Ω ⇒ Ω (it commutes with sieve pullback).
  record LawvereTierney : Type (ℓ-max ℓo (ℓ-suc ℓh)) where
    field
      jop    : (c : Ob) → Sieve {C = C} c → Sieve {C = C} c
      jnat   : IsNat (Ω {C = C}) (Ω {C = C}) jop
      -- j preserves truth: the maximal sieve is covered
      j-⊤    : (c : Ob) → jop c (maximal {C = C} c) ≡ maximal {C = C} c
      -- j is idempotent (a closure operator)
      j-idem : (c : Ob) (S : Sieve {C = C} c)
             → jop c (jop c S) ≡ jop c S
      -- j preserves binary meets
      j-∧    : (c : Ob) (S T : Sieve {C = C} c)
             → jop c (S ∧S T) ≡ (jop c S) ∧S (jop c T)
      -- NOTE: inflationarity (S ≤ j S, the unit S → ◯S) is NOT a
      -- field: it is DERIVABLE from jnat + j-⊤ — see
      -- Topos.InflationarityDerivable.j-infl-derivable.

  open LawvereTierney

  -- the internal morphism j : Ω ⇒ Ω underlying a topology
  j-mor : LawvereTierney → Nat (Ω {C = C}) (Ω {C = C})
  j-mor J = jop J , jnat J

  -- ----------------------------------------------------------
  -- The trivial (identity) topology j = id.  Every sieve is its
  -- own closure; the only j-dense sieve is the maximal one.  Its
  -- sheaves are all presheaves — the whole topos.
  -- ----------------------------------------------------------
  trivialLT : LawvereTierney
  trivialLT = record
    { jop = λ c S → S
    ; jnat = λ x y f S → refl
    ; j-⊤ = λ c → refl
    ; j-idem = λ c S → refl
    ; j-∧ = λ c S T → refl }

  -- ----------------------------------------------------------
  -- j-closed subobjects.  A sieve S is j-closed when it equals
  -- its own closure j S; these classify the subobjects that
  -- descend to the sub-topos of j-sheaves.
  -- ----------------------------------------------------------
  is-j-closed : (J : LawvereTierney) (c : Ob) → Sieve {C = C} c
              → Type (ℓ-max ℓo (ℓ-suc ℓh))
  is-j-closed J c S = jop J c S ≡ S

  -- the closure of any sieve is j-closed (idempotence)
  j-closure-closed : (J : LawvereTierney) (c : Ob) (S : Sieve {C = C} c)
                   → is-j-closed J c (jop J c S)
  j-closure-closed J c S = j-idem J c S

  -- ⊤ is j-closed for every topology (truth-preservation)
  ⊤-j-closed : (J : LawvereTierney) (c : Ob)
             → is-j-closed J c (maximal {C = C} c)
  ⊤-j-closed J c = j-⊤ J c
