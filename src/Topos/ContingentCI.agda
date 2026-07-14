{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.ContingentCI — Stage 1 of the modal-layer repair.
--
-- The vacuity of the modal layer (Topos.ModalRule1, .ModalRules)
-- is that `rule1-Ω`, `rule2-Ω`, `rule3-Ω` are the CONCLUSIONS of
-- theorems: each is a proved equality of distributions, hence has
-- internal truth value ⊤, and `j ⊤ = ⊤` is a topology axiom.  The
-- modality never sees a causal claim; it sees ⊤.  So `modal-ruleᵢ`
-- would typecheck verbatim with the causal content deleted.
--
-- Mahadevan's `j` is meant to range over CONTINGENT causal claims,
-- whose truth value is a genuinely non-maximal sieve.  This module
-- exhibits one, and thereby kills the vacuity objection: it shows
-- the SAME proposition `modal-rule1` forces to ⊤ under the `Y ⫫ X`
-- hypothesis is CONTINGENT once that hypothesis is dropped.
--
-- Over two regimes (the discrete category on Bool), with values in
-- Fin 2 and rational kernels:
--   • at regime `false` the mechanism is the constant kernel
--     (Y ⫫ X), so do(X) leaves the Y-marginal fixed — the
--     marginal-invariance proposition holds, and `ci-Ω false = ⊤`;
--   • at regime `true` the mechanism is the copy kernel (Y := X),
--     so do(X := 1) shifts the Y-marginal from `pure 0` to `pure 1`
--     — the proposition FAILS, and `ci-Ω true ≠ ⊤`.
-- The failure is a genuine ℚ computation: the two marginals are the
-- distinct point masses `pure 1` and `pure 0`, separated by their
-- mass at `1` (`w1 ≠ w0` in the rational weight algebra).  No
-- postulate, no faithfulness theorem — one normalising witness.
--
-- `witness-non-maximal : Σ[ c ] ¬ (ci-Ω c ≡ maximal c)` is the
-- Stage-1 deliverable.
-- ============================================================

module Topos.ContingentCI where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc)
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Fin using (Fin; fzero; fsuc; toℕ; isSetFin)
open import Cubical.Data.Nat using (znots)
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd)

open import FDist-Convex using
  ( FDist; pure; mapF; trunc
  ; mass; δ-diag; δ-off; mass-pure
  ; Weight; w0; w1; w0≢w1 )
open import RuleDoCalc using
  ( SCM₂; joint-of; do-X )

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.SCM
open import Topos.Classifier using (maximal→mem)
open import Topos.ModalRule1 using (prop→sieve; prop→sieve-true)

-- ------------------------------------------------------------
-- Local base-category and constant-presheaf helpers (as in
-- Topos.Example): two regimes, and Fin-2-valued value presheaves.
-- ------------------------------------------------------------
DiscreteCat : ∀ {ℓ} (A : Type ℓ) → isSet A → Precategory ℓ ℓ
DiscreteCat A setA = record
  { Ob = A ; Hom = λ x y → x ≡ y
  ; idn = refl ; _⋆_ = λ p q → p ∙ q
  ; ⋆-idL = λ p → sym (lUnit p) ; ⋆-idR = λ p → sym (rUnit p)
  ; ⋆-assoc = λ f g h → sym (assoc f g h)
  ; isSetHom = isProp→isSet (setA _ _) }

constPSh : ∀ {ℓo ℓh ℓ} {C : Precategory ℓo ℓh} (A : Type ℓ) → isSet A → PSh C ℓ
constPSh A setA = record
  { F₀ = λ _ → A ; F₁ = λ _ a → a
  ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → setA }

-- ------------------------------------------------------------
-- The instance.
-- ------------------------------------------------------------
C : Precategory ℓ-zero ℓ-zero
C = DiscreteCat Bool isSetBool

X Y : PSh C ℓ-zero
X = constPSh (Fin 2) isSetFin
Y = constPSh (Fin 2) isSetFin

-- values 0, 1 : Fin 2
v0 v1 : Fin 2
v0 = fzero
v1 = fsuc fzero

-- the two mechanisms: constant (Y ⫫ X) at `false`, copy (Y := X) at `true`
m : SCM-E {C = C} X Y
m false = record { pX = pure v0 ; kY = λ _ → pure v0 }   -- Y ⫫ X
m true  = record { pX = pure v0 ; kY = λ a → pure a  }    -- Y depends on X

-- intervene do(X := 1) at every regime
x₀ : (c : Bool) → Fin 2
x₀ _ = v1

-- ------------------------------------------------------------
-- The contingent proposition: the Y-marginal is invariant under
-- do(X := 1).  This is EXACTLY the proposition `rule1-Ω` internalises
-- (Topos.ModalRule1.rule1-prop) — but here without assuming Y ⫫ X.
-- ------------------------------------------------------------
P : (c : Bool) → hProp ℓ-zero
P c = ( mapF snd (joint-of (do-X (x₀ c) (m c)))
      ≡ mapF snd (joint-of (m c)) )
    , trunc _ _

-- At regime `false` it holds: both marginals compute to `pure 0`
-- (the constant kernel makes do(X) irrelevant).
P-false : fst (P false)
P-false = refl

-- At regime `true` it FAILS: the marginals are `pure 1` (after
-- do(X := 1), Y copies the intervened value) and `pure 0` (before),
-- which are distinct point masses — their mass at 1 is w1 vs w0.
¬P-true : ¬ (fst (P true))
¬P-true eq = w0≢w1 (sym w1≡w0)
  where
    -- fst (P true) reduces to  (pure v1 ≡ pure v0)  in FDist (Fin 2)
    massEq : mass (pure v1) v1 ≡ mass (pure v0) v1
    massEq = cong (λ d → mass d v1) eq

    0≢1 : ¬ (v0 ≡ v1)
    0≢1 p = znots (cong toℕ p)

    lhs : mass (pure v1) v1 ≡ w1
    lhs = mass-pure v1 v1 ∙ δ-diag v1

    rhs : mass (pure v0) v1 ≡ w0
    rhs = mass-pure v0 v1 ∙ δ-off v0 v1 0≢1

    w1≡w0 : w1 ≡ w0
    w1≡w0 = sym lhs ∙ massEq ∙ rhs

-- ------------------------------------------------------------
-- ci-Ω: the contingent claim internalised as an element of Ω,
-- regime by regime (the constant-sieve embedding, as for rule1-Ω).
-- ------------------------------------------------------------
ci-Ω : (c : Bool) → Sieve {C = C} c
ci-Ω c = prop→sieve {C = C} c (P c)

-- it is ⊤ at regime `false` (the CI-analogue holds there)
ci-Ω-false-⊤ : ci-Ω false ≡ maximal {C = C} false
ci-Ω-false-⊤ = prop→sieve-true {C = C} false (P false) P-false

-- ------------------------------------------------------------
-- STAGE 1 DELIVERABLE: a non-maximal sieve.  Unlike rule1-Ω /
-- rule2-Ω / rule3-Ω — which are ⊤ at every regime — ci-Ω is ⊤ at
-- `false` and NOT ⊤ at `true`.  So the modality now has something
-- contingent to act on.
-- ------------------------------------------------------------
witness-non-maximal : Σ[ c ∈ Bool ] (¬ (ci-Ω c ≡ maximal {C = C} c))
witness-non-maximal = true , λ eq → ¬P-true (extract eq)
  where
    -- a maximal sieve contains every arrow; at (true , idn) its
    -- membership is `fst (P true)`, which ¬P-true refutes.
    extract : ci-Ω true ≡ maximal {C = C} true → fst (P true)
    extract eq = maximal→mem {C = C} (ci-Ω true) eq true (Precategory.idn C)
