{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.LawvereTierney — Stage 2.  A Lawvere–Tierney topology
-- j : Ω → Ω on the subobject classifier of the presheaf topos.
--
-- j is the internal counterpart of a Grothendieck topology.  It
-- also corresponds to a lex modality ◯ (Rijke–Shulman–Spitters).
-- j picks out the covered sieves, also called the j-dense ones,
-- and the j-closed subobjects form a sub-(∞-)topos.  In the
-- causal reading (translation.md:25, outline.md:85), j is the
-- modality of Mahadevan's j-do-calculus, and "j-stable discovery"
-- means ◯-modal structure.
--
-- The three axioms are MacLane–Moerdijk's (Sheaves in Geometry &
-- Logic, V.1):
--     j ∘ true  = true        (j preserves ⊤)
--     j ∘ j     = j           (idempotent)
--     j (S ∧ T) = j S ∧ j T   (preserves meets)
-- Monotonicity follows from meet-preservation, so it is omitted.
--
-- The internal meet ∧ on Ω is pointwise sieve intersection.  It
-- is built first, because the third axiom needs it.
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
  -- Internal meet of sieves.  Membership is the pointwise
  -- conjunction of the two memberships.  Closure under
  -- precomposition holds componentwise.
  -- ----------------------------------------------------------
  _∧S_ : {c : Ob} → Sieve {C = C} c → Sieve {C = C} c → Sieve {C = C} c
  _∧S_ {c} S T =
    (λ d f → fst S d f ⊓ fst T d f) ,
    (λ d e k f pf → (snd S d e k f (fst pf) , snd T d e k f (snd pf)))

  -- ----------------------------------------------------------
  -- A Lawvere–Tierney topology on Ω.
  -- ----------------------------------------------------------
  -- jop is the bare regime-wise operation.  jnat makes it an
  -- internal morphism Ω ⇒ Ω, since it says that jop commutes with
  -- sieve pullback.
  record LawvereTierney : Type (ℓ-max ℓo (ℓ-suc ℓh)) where
    field
      jop    : (c : Ob) → Sieve {C = C} c → Sieve {C = C} c
      jnat   : IsNat (Ω {C = C}) (Ω {C = C}) jop
      -- j preserves truth: the maximal sieve is covered.
      j-⊤    : (c : Ob) → jop c (maximal {C = C} c) ≡ maximal {C = C} c
      -- j is idempotent, so it is a closure operator.
      j-idem : (c : Ob) (S : Sieve {C = C} c)
             → jop c (jop c S) ≡ jop c S
      -- j preserves binary meets.
      j-∧    : (c : Ob) (S T : Sieve {C = C} c)
             → jop c (S ∧S T) ≡ (jop c S) ∧S (jop c T)
      -- NOTE: inflationarity is S ≤ j S, the unit S → ◯S.  It is
      -- not a field here, because jnat and j-⊤ already derive it.
      -- See Topos.InflationarityDerivable.j-infl-derivable.

  open LawvereTierney

  -- The internal morphism j : Ω ⇒ Ω underlying a topology.
  j-mor : LawvereTierney → Nat (Ω {C = C}) (Ω {C = C})
  j-mor J = jop J , jnat J

  -- ----------------------------------------------------------
  -- The trivial topology, j = id.  Every sieve is its own
  -- closure.  The only j-dense sieve is the maximal one.  Its
  -- sheaves are all presheaves, that is, the whole topos.
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
  -- its own closure j S.  These sieves classify the subobjects
  -- that descend to the sub-topos of j-sheaves.
  -- ----------------------------------------------------------
  is-j-closed : (J : LawvereTierney) (c : Ob) → Sieve {C = C} c
              → Type (ℓ-max ℓo (ℓ-suc ℓh))
  is-j-closed J c S = jop J c S ≡ S

  -- The closure of any sieve is j-closed, by idempotence.
  j-closure-closed : (J : LawvereTierney) (c : Ob) (S : Sieve {C = C} c)
                   → is-j-closed J c (jop J c S)
  j-closure-closed J c S = j-idem J c S

  -- ⊤ is j-closed for every topology, by truth-preservation.
  ⊤-j-closed : (J : LawvereTierney) (c : Ob)
             → is-j-closed J c (maximal {C = C} c)
  ⊤-j-closed J c = j-⊤ J c
