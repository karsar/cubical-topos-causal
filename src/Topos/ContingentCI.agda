{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.ContingentCI — Stage 1 of the modal-layer repair.
--
-- A modal statement is vacuous when the modality is applied to ⊤.
-- The modal layer of Topos.ModalRule1 and Topos.ModalRules has
-- that shape.  `rule1-Ω`, `rule2-Ω` and `rule3-Ω` are the
-- CONCLUSIONS of theorems.  Each is a proved equality of
-- distributions, so each has internal truth value ⊤.  The
-- topology axiom `j ⊤ = ⊤` then gives the modal statement.  The
-- modality never receives a causal claim, so `modal-ruleᵢ` would
-- typecheck verbatim with the causal content deleted.
--
-- Mahadevan intends `j` to range over CONTINGENT causal claims.
-- The truth value of such a claim is a sieve that is not maximal.
-- This module builds one.  The same proposition that
-- `modal-rule1` forces to ⊤ under the `Y ⫫ X` hypothesis is
-- contingent once that hypothesis is dropped.
--
-- The base is the discrete category on Bool, so there are two
-- regimes.  Values lie in Fin 2 and the kernels are rational.
--   • At regime `false` the mechanism is the constant kernel
--     (Y ⫫ X).  Then do(X) leaves the Y-marginal fixed, the
--     marginal-invariance proposition holds, and
--     `ci-Ω false = ⊤`.
--   • At regime `true` the mechanism is the copy kernel (Y := X).
--     Then do(X := 1) shifts the Y-marginal from `pure 0` to
--     `pure 1`, the proposition FAILS, and `ci-Ω true ≠ ⊤`.
-- The failure is a ℚ computation.  The two marginals are the
-- point masses `pure 1` and `pure 0`.  They differ in their mass
-- at `1`, since `w1 ≠ w0` in the rational weight algebra.  The
-- proof uses one normalising witness.  It needs no postulate and
-- no faithfulness theorem.
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
-- Local helpers for the base category and for constant
-- presheaves, as in Topos.Example.  Two regimes, and value
-- presheaves with values in Fin 2.
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

-- The two mechanisms.  Constant (Y ⫫ X) at `false`, and copy
-- (Y := X) at `true`.
m : SCM-E {C = C} X Y
m false = record { pX = pure v0 ; kY = λ _ → pure v0 }   -- Y ⫫ X
m true  = record { pX = pure v0 ; kY = λ a → pure a  }    -- Y depends on X

-- Intervene with do(X := 1) at every regime.
x₀ : (c : Bool) → Fin 2
x₀ _ = v1

-- ------------------------------------------------------------
-- The contingent proposition.  The Y-marginal is invariant under
-- do(X := 1).  This is the proposition that `rule1-Ω`
-- internalises (Topos.ModalRule1.rule1-prop).  Here it is stated
-- without the assumption Y ⫫ X.
-- ------------------------------------------------------------
P : (c : Bool) → hProp ℓ-zero
P c = ( mapF snd (joint-of (do-X (x₀ c) (m c)))
      ≡ mapF snd (joint-of (m c)) )
    , trunc _ _

-- At regime `false` the proposition holds.  Both marginals
-- compute to `pure 0`, because the constant kernel ignores do(X).
P-false : fst (P false)
P-false = refl

-- At regime `true` the proposition FAILS.  After do(X := 1) the
-- copy kernel gives Y the intervened value, so the marginal is
-- `pure 1`.  Before the intervention it is `pure 0`.  These point
-- masses are distinct: their mass at 1 is w1 against w0.
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
-- ci-Ω internalises the contingent claim as an element of Ω,
-- regime by regime.  It uses the constant-sieve embedding, as
-- rule1-Ω does.
-- ------------------------------------------------------------
ci-Ω : (c : Bool) → Sieve {C = C} c
ci-Ω c = prop→sieve {C = C} c (P c)

-- At regime `false` it is ⊤, because the CI-analogue holds there.
ci-Ω-false-⊤ : ci-Ω false ≡ maximal {C = C} false
ci-Ω-false-⊤ = prop→sieve-true {C = C} false (P false) P-false

-- ------------------------------------------------------------
-- STAGE 1 DELIVERABLE: a sieve that is not maximal.  rule1-Ω,
-- rule2-Ω and rule3-Ω are ⊤ at every regime.  ci-Ω is ⊤ at
-- `false` and is NOT ⊤ at `true`.  The modality now has a
-- contingent input to act on.
-- ------------------------------------------------------------
witness-non-maximal : Σ[ c ∈ Bool ] (¬ (ci-Ω c ≡ maximal {C = C} c))
witness-non-maximal = true , λ eq → ¬P-true (extract eq)
  where
    -- A maximal sieve contains every arrow.  At (true , idn) its
    -- membership is `fst (P true)`, and ¬P-true refutes that.
    extract : ci-Ω true ≡ maximal {C = C} true → fst (P true)
    extract eq = maximal→mem {C = C} (ci-Ω true) eq true (Precategory.idn C)
