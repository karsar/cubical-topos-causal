{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Example — a concrete instance on which internal Rule 1
-- computes.
--
-- Base: two regimes, the discrete category on Bool.
-- Value presheaves X, Y: constant Bool.
-- Internal SCM m: at regime c the prior is the point mass on c,
--   so the two regimes differ.  The mechanism kY _ = pure true
--   makes Y deterministically true, so Y ⫫ X.
--
-- The intervention do(X := x₀) changes the joint, and in
-- particular its X-marginal.  Internal Rule 1
-- (Topos.Rule1.rule1-E) gives that the Y-marginal is unchanged.
-- Here the Y-marginal computes to `pure true` at every regime,
-- so refl proves the equation.
-- ============================================================

module Topos.Example where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Sigma using (snd; fst; _,_)

open import FDist-Convex using (FDist; pure; mapF)
open import RuleDoCalc   using (SCM₂; joint-of; do-X; Y-indep-X)

open import Topos.Cat
open import Topos.PSh
open import Topos.InternalDist
open import Topos.SCM
open import Topos.Rule1
open import Topos.SCMNat

-- The discrete category on a set.  Morphisms are paths,
-- identities are refl, and composition is path composition.
DiscreteCat : ∀ {ℓ} (A : Type ℓ) → isSet A → Precategory ℓ ℓ
DiscreteCat A setA = record
  { Ob       = A
  ; Hom      = λ x y → x ≡ y
  ; idn      = refl
  ; _⋆_      = λ p q → p ∙ q
  ; ⋆-idL    = λ p → sym (lUnit p)
  ; ⋆-idR    = λ p → sym (rUnit p)
  ; ⋆-assoc  = λ f g h → sym (assoc f g h)
  ; isSetHom = isProp→isSet (setA _ _)
  }

-- the constant presheaf on a set (all restrictions are the identity)
constPSh : ∀ {ℓo ℓh ℓ} {C : Precategory ℓo ℓh} (A : Type ℓ) → isSet A → PSh C ℓ
constPSh A setA = record
  { F₀ = λ _ → A ; F₁ = λ _ a → a
  ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → setA }

-- ---- the instance --------------------------------------------------

C : Precategory _ _
C = DiscreteCat Bool isSetBool          -- two regimes

X Y : PSh C _
X = constPSh Bool isSetBool
Y = constPSh Bool isSetBool

-- Internal SCM.  The prior is the point mass on the regime label,
-- and Y is true at every regime.
m : SCM-E {C = C} X Y
m c = record { pX = pure c ; kY = λ _ → pure true }

-- Y is independent of X, since the mechanism is the constant
-- kernel `pure true`
ind : Indep-E {C = C} {X = X} {Y = Y} m
ind c = record { k₀ = pure true ; const-witness = λ _ → refl }

-- intervention: set X to true in every regime
x₀ : (c : Bool) → Bool
x₀ c = true

-- Internal Rule 1 on this model: the Y-marginal is invariant
-- under do(X).
demo : (c : Bool)
     → mapF snd (joint-of (do-X (x₀ c) (m c))) ≡ mapF snd (joint-of (m c))
demo = rule1-E {C = C} {X = X} {Y = Y} m ind x₀

-- The marginals also compute.  The Y-marginal is `pure true` at
-- every regime, before and after the intervention.  The proofs
-- are refl, because the distributions are point masses.
marginal-before : (c : Bool) → marginalY-E {C = C} {X = X} {Y = Y} m c ≡ pure true
marginal-before c = refl

marginal-after : (c : Bool)
               → marginalY-E {C = C} {X = X} {Y = Y} (do-XE {C = C} {X = X} {Y = Y} x₀ m) c
                 ≡ pure true
marginal-after c = refl

-- ---- the Nat≡ upgrade, concretely --------------------------------
-- The internal Y-marginal is an internal global element, that is
-- a Section of Dist_E Y.  Naturality is refl here, because the
-- presheaves are constant and the marginal computes to
-- `pure true` at every regime.
ndo : IsNat {C = C} 𝟙 (Dist_E Y) (λ c _ → mapF snd (joint-of (do-X (x₀ c) (m c))))
ndo _ _ _ _ = refl

nm : IsNat {C = C} 𝟙 (Dist_E Y) (λ c _ → mapF snd (joint-of (m c)))
nm _ _ _ _ = refl

-- internal Rule 1 as an equality of internal morphisms
-- 𝟙 ⇒ Dist_E Y
demo-nat : _≡_ {A = Section {C = C} (Dist_E Y)}
             ((λ c _ → mapF snd (joint-of (do-X (x₀ c) (m c)))) , ndo)
             ((λ c _ → mapF snd (joint-of (m c))) , nm)
demo-nat = rule1-E-nat {C = C} {X = X} {Y = Y} m ind x₀ ndo nm

-- ---- fully-derived internal Rule 1 (no naturality hypotheses) ----
-- The same model as a natural internal SCM.  The prior coheres
-- along the regime path f by cong pure f, and the constant kernel
-- coheres by refl.
M-nat : SCM-E-nat {C = C} X Y
M-nat = record
  { pXs = λ c → pure c
  ; kYs = λ _ _ → pure true
  ; pX-nat = λ x y f → cong pure f
  ; kY-nat = λ x y f a → refl }

ind-nat : Indep-E-nat {C = C} {X = X} {Y = Y} M-nat
ind-nat c = record { k₀ = pure true ; const-witness = λ _ → refl }

-- intervention by a regime-coherent value, the constant `true`
-- section
x₀-sec : Section {C = C} X
x₀-sec = (λ c _ → true) , (λ x y f a → refl)

-- internal Rule 1 as an equality of internal morphisms, with
-- naturality derived
demo-section : marginalSection {C = C} {X = X} {Y = Y} (do-XE-nat {C = C} {X = X} {Y = Y} x₀-sec M-nat)
             ≡ marginalSection {C = C} {X = X} {Y = Y} M-nat
demo-section = rule1-E-section {C = C} {X = X} {Y = Y} M-nat ind-nat x₀-sec
