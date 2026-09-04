{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.BaseChange — base change along a functor of regime
-- categories, and its comparison map on truth values.
--
-- A BaseFunctor F : C → D is an abstraction of contexts.  It
-- induces two operations:
--   basePull : PSh D → PSh C, precomposition with F;
--   φB       : Sieve (App₀ c) → Sieve c, the preimage of a
--              coarse sieve.
-- φB is natural in c (φB-nat).  So it is the component form of
-- a map of presheaves basePull Ω_D ⇒ Ω_C (φNat).  This is the
-- canonical comparison map of the base change.
--
-- The module proves the facts that hold for EVERY base functor:
--  (1) φB preserves ⊤, ⊥, ∧, ∨.  Each proof is refl pointwise:
--      the memberships agree by definition.
--  (2) φB preserves and reflects forcing (φB-⊩, φB-⊩-reflect).
--
-- φB does not preserve ⇒ or ¬ for every F.  That needs a
-- condition on F, and the failure is the subject of the tier
-- analysis.  Topos.MergeAbstraction is the concrete instance:
-- its φ is φB at the merge functor.
-- ============================================================

module Topos.BaseChange where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Sigma using (_,_; fst; snd)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.LawvereTierney using (_∧S_)
open import Topos.Forcing using (_∨S_; _⊩_)
open import Topos.DoubleNegation using (⊥S)

-- ------------------------------------------------------------
-- A functor between regime categories.  App₀ acts on objects
-- and App₁ on morphisms.  The record is level-general.  The
-- derived operations below fix one level for both categories,
-- because Topos.Forcing does.
-- ------------------------------------------------------------
record BaseFunctor {ℓoC ℓoD ℓh}
       (C : Precategory ℓoC ℓh) (D : Precategory ℓoD ℓh)
       : Type (ℓ-max (ℓ-max ℓoC ℓoD) ℓh) where
  private
    module Cc = Precategory C
    module Dc = Precategory D
  field
    App₀   : Cc.Ob → Dc.Ob
    App₁   : ∀ {x y} → Cc.Hom x y → Dc.Hom (App₀ x) (App₀ y)
    App-id : (x : Cc.Ob) → App₁ (Cc.idn {x}) ≡ Dc.idn {App₀ x}
    App-⋆  : ∀ {x y z} (f : Cc.Hom x y) (g : Cc.Hom y z)
           → App₁ (f Cc.⋆ g) ≡ App₁ f Dc.⋆ App₁ g

module _ {ℓ}
         {C : Precategory ℓ ℓ} {D : Precategory ℓ ℓ}
         (F : BaseFunctor C D) where
  private
    module Cc = Precategory C
    module Dc = Precategory D
  open BaseFunctor F
  open PSh

  -- ----------------------------------------------------------
  -- Precomposition with F sends a presheaf on D to a presheaf
  -- on C.  This is the inverse image on causal worlds.
  -- ----------------------------------------------------------
  basePull : ∀ {ℓv} → PSh D ℓv → PSh C ℓv
  basePull Y = record
    { F₀      = λ c → F₀ Y (App₀ c)
    ; F₁      = λ f a → F₁ Y (App₁ f) a
    ; F-id    = λ {x} a → cong (λ h → F₁ Y h a) (App-id x) ∙ F-id Y a
    ; F-comp  = λ f g a → cong (λ h → F₁ Y h a) (App-⋆ f g)
                          ∙ F-comp Y (App₁ f) (App₁ g) a
    ; isSetF₀ = λ c → isSetF₀ Y (App₀ c)
    }

  -- ----------------------------------------------------------
  -- basePull acts on mechanisms too: a map of coarse worlds
  -- pulls back to a map of fine worlds.
  -- ----------------------------------------------------------
  basePullNat : ∀ {ℓv ℓw} {Y : PSh D ℓv} {Z : PSh D ℓw}
              → Nat {C = D} Y Z → Nat {C = C} (basePull Y) (basePull Z)
  basePullNat n =
    (λ c a → fst n (App₀ c) a)
    , (λ x y f a → snd n (App₀ x) (App₀ y) (App₁ f) a)

  -- ----------------------------------------------------------
  -- The comparison map: the preimage of a coarse sieve.
  -- A fine arrow f is a member iff its image App₁ f is.
  -- ----------------------------------------------------------
  φB : (c : Cc.Ob) → Sieve {C = D} (App₀ c) → Sieve {C = C} c
  φB c S = mem , clo
    where
      mem : (d : Cc.Ob) → Cc.Hom d c → hProp ℓ
      mem d f = fst S (App₀ d) (App₁ f)
      clo : Closure {C = C} c mem
      clo d e k f pf =
        subst (λ h → fst (fst S (App₀ e) h))
              (sym (App-⋆ k f))
              (snd S (App₀ d) (App₀ e) (App₁ k) (App₁ f) pf)

  -- ----------------------------------------------------------
  -- φB commutes with sieve pullback.  So the component family
  -- φB is a map of presheaves basePull Ω_D ⇒ Ω_C.
  -- ----------------------------------------------------------
  φB-nat : (c' c : Cc.Ob) (h : Cc.Hom c' c) (S : Sieve {C = D} (App₀ c))
         → pull {C = C} h (φB c S) ≡ φB c' (pull {C = D} (App₁ h) S)
  φB-nat c' c h S = Sieve≡ {C = C}
    (pull {C = C} h (φB c S)) (φB c' (pull {C = D} (App₁ h) S))
    (funExt λ d → funExt λ f → cong (fst S (App₀ d)) (App-⋆ f h))

  φNat : Nat {C = C} (basePull (Ω {C = D})) (Ω {C = C})
  φNat = (λ c S → φB c S) , (λ x y h S → sym (φB-nat x y h S))

  -- ----------------------------------------------------------
  -- (1) φB preserves ⊤, ⊥, ∧, ∨.  The memberships agree by
  -- definition, so each proof is refl pointwise.
  -- ----------------------------------------------------------
  φB-⊤ : (c : Cc.Ob) → φB c (maximal {C = D} (App₀ c)) ≡ maximal {C = C} c
  φB-⊤ c = Sieve≡ {C = C} _ _ (funExt λ d → funExt λ f → refl)

  φB-⊥ : (c : Cc.Ob) → φB c (⊥S {C = D} (App₀ c)) ≡ ⊥S {C = C} c
  φB-⊥ c = Sieve≡ {C = C} _ _ (funExt λ d → funExt λ f → refl)

  φB-∧ : (c : Cc.Ob) (S T : Sieve {C = D} (App₀ c))
       → φB c (_∧S_ {C = D} {c = App₀ c} S T)
       ≡ _∧S_ {C = C} {c = c} (φB c S) (φB c T)
  φB-∧ c S T = Sieve≡ {C = C} _ _ (funExt λ d → funExt λ f → refl)

  φB-∨ : (c : Cc.Ob) (S T : Sieve {C = D} (App₀ c))
       → φB c (_∨S_ {C = D} {c = App₀ c} S T)
       ≡ _∨S_ {C = C} {c = c} (φB c S) (φB c T)
  φB-∨ c S T = Sieve≡ {C = C} _ _ (funExt λ d → funExt λ f → refl)

  -- ----------------------------------------------------------
  -- (2) φB preserves and reflects forcing.  Forcing reads the
  -- membership at the identity, and App-id matches the two
  -- identities.
  -- ----------------------------------------------------------
  φB-⊩ : (c : Cc.Ob) (S : Sieve {C = D} (App₀ c))
       → _⊩_ {C = D} (App₀ c) S → _⊩_ {C = C} c (φB c S)
  φB-⊩ c S p = subst (λ h → fst (fst S (App₀ c) h)) (sym (App-id c)) p

  φB-⊩-reflect : (c : Cc.Ob) (S : Sieve {C = D} (App₀ c))
               → _⊩_ {C = C} c (φB c S) → _⊩_ {C = D} (App₀ c) S
  φB-⊩-reflect c S p = subst (λ h → fst (fst S (App₀ c) h)) (App-id c) p
