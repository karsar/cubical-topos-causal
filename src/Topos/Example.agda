{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Example — a concrete instance on which internal Rule 1
-- COMPUTES.
--
-- Base: two regimes (the discrete category on Bool).
-- Value presheaves X, Y: constant Bool.
-- Internal SCM m: at regime c the prior is the point mass on c
--   (so the two regimes genuinely differ), and the mechanism
--   kY _ = pure true makes Y deterministically true, hence Y ⫫ X.
--
-- Intervention do(X := x₀) changes the joint (the X-marginal),
-- but internal Rule 1 (Topos.Rule1.rule1-E) certifies the
-- Y-marginal is unchanged — and here it computes to `pure true`
-- at every regime, witnessed by refl.
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

-- the discrete category on a set: morphisms are paths, identities
-- are refl, composition is path composition
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

-- internal SCM: prior = point mass on the regime label; Y ≡ true always
m : SCM-E {C = C} X Y
m c = record { pX = pure c ; kY = λ _ → pure true }

-- Y is independent of X (mechanism is the constant kernel `pure true`)
ind : Indep-E {C = C} {X = X} {Y = Y} m
ind c = record { k₀ = pure true ; const-witness = λ _ → refl }

-- intervention: set X to true in every regime
x₀ : (c : Bool) → Bool
x₀ c = true

-- INTERNAL RULE 1 on this model: the Y-marginal is invariant under do(X)
demo : (c : Bool)
     → mapF snd (joint-of (do-X (x₀ c) (m c))) ≡ mapF snd (joint-of (m c))
demo = rule1-E {C = C} {X = X} {Y = Y} m ind x₀

-- …and it COMPUTES: the Y-marginal is `pure true` at every regime,
-- both before and after the intervention — by refl (point masses).
marginal-before : (c : Bool) → marginalY-E {C = C} {X = X} {Y = Y} m c ≡ pure true
marginal-before c = refl

marginal-after : (c : Bool)
               → marginalY-E {C = C} {X = X} {Y = Y} (do-XE {C = C} {X = X} {Y = Y} x₀ m) c
                 ≡ pure true
marginal-after c = refl

-- ---- the Nat≡ upgrade, concretely --------------------------------
-- The internal Y-marginal is a genuine internal global element
-- (Section of Dist_E Y).  Naturality is refl here: constant presheaves,
-- and the marginal computes to `pure true` at every regime.
ndo : IsNat {C = C} 𝟙 (Dist_E Y) (λ c _ → mapF snd (joint-of (do-X (x₀ c) (m c))))
ndo _ _ _ _ = refl

nm : IsNat {C = C} 𝟙 (Dist_E Y) (λ c _ → mapF snd (joint-of (m c)))
nm _ _ _ _ = refl

-- internal Rule 1 as an EQUALITY OF INTERNAL MORPHISMS 𝟙 ⇒ Dist_E Y
demo-nat : _≡_ {A = Section {C = C} (Dist_E Y)}
             ((λ c _ → mapF snd (joint-of (do-X (x₀ c) (m c)))) , ndo)
             ((λ c _ → mapF snd (joint-of (m c))) , nm)
demo-nat = rule1-E-nat {C = C} {X = X} {Y = Y} m ind x₀ ndo nm

-- ---- fully-derived internal Rule 1 (no naturality hypotheses) ----
-- the same model as a NATURAL internal SCM: the prior coheres via the
-- regime path f (cong pure f), the constant kernel coheres by refl.
M-nat : SCM-E-nat {C = C} X Y
M-nat = record
  { pXs = λ c → pure c
  ; kYs = λ _ _ → pure true
  ; pX-nat = λ x y f → cong pure f
  ; kY-nat = λ x y f a → refl }

ind-nat : Indep-E-nat {C = C} {X = X} {Y = Y} M-nat
ind-nat c = record { k₀ = pure true ; const-witness = λ _ → refl }

-- intervention by a regime-coherent value (the constant `true` section)
x₀-sec : Section {C = C} X
x₀-sec = (λ c _ → true) , (λ x y f a → refl)

-- internal Rule 1 as an equality of internal morphisms, naturality DERIVED
demo-section : marginalSection {C = C} {X = X} {Y = Y} (do-XE-nat {C = C} {X = X} {Y = Y} x₀-sec M-nat)
             ≡ marginalSection {C = C} {X = X} {Y = Y} M-nat
demo-section = rule1-E-section {C = C} {X = X} {Y = Y} M-nat ind-nat x₀-sec
