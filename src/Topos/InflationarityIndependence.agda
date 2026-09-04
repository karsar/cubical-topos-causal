{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.InflationarityIndependence — a counter-model showing that
-- the three Lawvere-Tierney equations, taken pointwise on an
-- arbitrary Heyting algebra, do not by themselves entail
-- inflationarity (S ≤ j S).
--
-- For a Lawvere-Tierney topology proper, that is for a natural
-- morphism j : Ω ⇒ Ω, inflationarity is derivable rather than
-- assumed.  Naturality together with j ⊤ = ⊤ force it
-- (Topos.InflationarityDerivable).  Naturality is the hypothesis
-- that does the work, and this module isolates it by dropping it.
--
-- The counter-model is the bare three-element Heyting chain
-- ⊥ < a < ⊤.  The operator j fixes ⊥ and ⊤ and sends a ↦ ⊥.  The
-- three equations
--     j ⊤ = ⊤                  (preserves truth)
--     j (x ∧ y) = j x ∧ j y    (preserves meets)
--     j (j x) = j x            (idempotent)
-- all hold.  Still j sends `a` strictly below itself, so j is not
-- inflationary and is not a closure operator.  The chain is a
-- Heyting algebra, but it is not a subobject classifier.  Without
-- the naturality that a topos Ω supplies, the three equations
-- leave inflationarity underdetermined.  The double-negation
-- topology in Topos.DoubleNegation is a topology proper, and it
-- is inflationary.
-- ============================================================

module Topos.InflationarityIndependence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Relation.Nullary using (¬_)

-- The three-element chain ⊥ < a < ⊤.
data Three : Type where
  ⊥₃ a₃ ⊤₃ : Three

-- Meet, the minimum on the chain.
_∧₃_ : Three → Three → Three
⊥₃ ∧₃ _  = ⊥₃
a₃ ∧₃ ⊥₃ = ⊥₃
a₃ ∧₃ a₃ = a₃
a₃ ∧₃ ⊤₃ = a₃
⊤₃ ∧₃ y  = y

-- Order induced by the meet:  x ≤ y  ⇔  x ∧ y = x.
_≤₃_ : Three → Three → Type
x ≤₃ y = (x ∧₃ y) ≡ x

-- The candidate "topology".  It fixes ⊥ and ⊤ and sends a to ⊥.
j₃ : Three → Three
j₃ ⊥₃ = ⊥₃
j₃ a₃ = ⊥₃
j₃ ⊤₃ = ⊤₃

-- ----------------------------------------------------------
-- j₃ satisfies the three standard Lawvere-Tierney equations.
-- ----------------------------------------------------------

-- (1) preserves truth.
j-⊤₃ : j₃ ⊤₃ ≡ ⊤₃
j-⊤₃ = refl

-- (2) preserves meets.  All nine constructor combinations
-- compute by refl.
j-∧₃ : (x y : Three) → j₃ (x ∧₃ y) ≡ (j₃ x ∧₃ j₃ y)
j-∧₃ ⊥₃ ⊥₃ = refl
j-∧₃ ⊥₃ a₃ = refl
j-∧₃ ⊥₃ ⊤₃ = refl
j-∧₃ a₃ ⊥₃ = refl
j-∧₃ a₃ a₃ = refl
j-∧₃ a₃ ⊤₃ = refl
j-∧₃ ⊤₃ ⊥₃ = refl
j-∧₃ ⊤₃ a₃ = refl
j-∧₃ ⊤₃ ⊤₃ = refl

-- (3) idempotent.
j-idem₃ : (x : Three) → j₃ (j₃ x) ≡ j₃ x
j-idem₃ ⊥₃ = refl
j-idem₃ a₃ = refl
j-idem₃ ⊤₃ = refl

-- ----------------------------------------------------------
-- j₃ is not inflationary.
-- ----------------------------------------------------------

-- a ≢ ⊥, by a Boolean separator.
sep : Three → Bool
sep ⊥₃ = false
sep a₃ = true
sep ⊤₃ = true

a₃≢⊥₃ : ¬ (a₃ ≡ ⊥₃)
a₃≢⊥₃ p = true≢false (cong sep p)

-- Inflationarity would force a ≤ j a, that is a ≤ ⊥.  That means
-- a ∧ ⊥ ≡ a, hence ⊥ ≡ a, which is false.
not-inflationary : ¬ ((x : Three) → x ≤₃ j₃ x)
not-inflationary infl = a₃≢⊥₃ (sym (infl a₃))

-- ----------------------------------------------------------
-- Conclusion: the three equations are satisfiable by an operator
-- that is not inflationary, so they do not entail inflationarity.
-- ----------------------------------------------------------
record SatisfiesThreeButNotInflationary : Type where
  field
    pres-⊤    : j₃ ⊤₃ ≡ ⊤₃
    pres-∧    : (x y : Three) → j₃ (x ∧₃ y) ≡ (j₃ x ∧₃ j₃ y)
    idem      : (x : Three) → j₃ (j₃ x) ≡ j₃ x
    not-infl  : ¬ ((x : Three) → x ≤₃ j₃ x)

inflationarity-independent : SatisfiesThreeButNotInflationary
inflationarity-independent = record
  { pres-⊤   = j-⊤₃
  ; pres-∧   = j-∧₃
  ; idem     = j-idem₃
  ; not-infl = not-inflationary
  }
