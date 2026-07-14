{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.InflationarityIndependence — a counter-model showing that
-- the three standard Lawvere-Tierney equations do NOT entail
-- inflationarity.
--
-- The modal layer (Topos.LawvereTierney) adds inflationarity
-- (S ≤ j S, the field `j-infl`) as a FOURTH axiom, on top of the
-- three usually given:
--     j ⊤ = ⊤            (preserves truth)
--     j (x ∧ y) = j x ∧ j y   (preserves meets)
--     j (j x) = j x      (idempotent).
-- The paper claims this fourth law is independent of the first
-- three.  Here we machine-check that claim with the minimal
-- counter-model: the three-element chain ⊥ < a < ⊤ with the
-- operator j that fixes ⊥ and ⊤ but sends a ↦ ⊥.  It satisfies all
-- three equations yet collapses `a` strictly below itself, so it is
-- not inflationary and not a closure operator.  Hence the three
-- equations are satisfiable without inflationarity: they do not
-- entail it.  (A genuine Lawvere-Tierney topology — e.g. ¬¬ in
-- Topos.DoubleNegation — does satisfy all four.)
-- ============================================================

module Topos.InflationarityIndependence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Relation.Nullary using (¬_)

-- The three-element chain ⊥ < a < ⊤.
data Three : Type where
  ⊥₃ a₃ ⊤₃ : Three

-- Meet (minimum on the chain).
_∧₃_ : Three → Three → Three
⊥₃ ∧₃ _  = ⊥₃
a₃ ∧₃ ⊥₃ = ⊥₃
a₃ ∧₃ a₃ = a₃
a₃ ∧₃ ⊤₃ = a₃
⊤₃ ∧₃ y  = y

-- Order induced by the meet:  x ≤ y  ⇔  x ∧ y = x.
_≤₃_ : Three → Three → Type
x ≤₃ y = (x ∧₃ y) ≡ x

-- The candidate "topology": fixes ⊥ and ⊤, collapses a to ⊥.
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

-- (2) preserves meets — all nine constructor combinations compute.
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
-- …yet j₃ is NOT inflationary.
-- ----------------------------------------------------------

-- a ≢ ⊥, by a Boolean separator.
sep : Three → Bool
sep ⊥₃ = false
sep a₃ = true
sep ⊤₃ = true

a₃≢⊥₃ : ¬ (a₃ ≡ ⊥₃)
a₃≢⊥₃ p = true≢false (cong sep p)

-- Inflationarity would force a ≤ j a = a ≤ ⊥, i.e. a ∧ ⊥ ≡ a,
-- i.e. ⊥ ≡ a — impossible.
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
