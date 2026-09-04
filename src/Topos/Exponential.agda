{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Exponential — the internal hom of presheaves.
--
-- A pointwise assignment c ↦ (F₀ A c → F₀ B c) is not a
-- presheaf.  Restriction along f : d → c would need a map
-- F₀ A d → F₀ A c, and a presheaf supplies the other direction.
--
-- The exponential fixes this.  An element of Exp A B at c is a
-- family indexed by arrows into c:
--     app d (g : Hom d c) : F₀ A d → F₀ B d,
-- natural in d.  Restriction along f precomposes g with f, which
-- needs no map on A at all.
--
-- This is the object the mechanism presheaf of
-- Topos.MechanismObject is built from.
-- ============================================================

module Topos.Exponential where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; ΣPathP)

open import Topos.Cat
open import Topos.PSh

module _ {ℓ} {C : Precategory ℓ ℓ} where
  open Precategory C
  open PSh

  -- ----------------------------------------------------------
  -- The naturality condition on a family.
  -- ----------------------------------------------------------
  ExpNat : (A B : PSh C ℓ) (c : Ob)
         → ((d : Ob) → Hom d c → F₀ A d → F₀ B d) → Type ℓ
  ExpNat A B c app =
    (e d : Ob) (k : Hom e d) (g : Hom d c) (a : F₀ A d)
    → app e (k ⋆ g) (F₁ A k a) ≡ F₁ B k (app d g a)

  isPropExpNat : (A B : PSh C ℓ) (c : Ob)
                 (app : (d : Ob) → Hom d c → F₀ A d → F₀ B d)
               → isProp (ExpNat A B c app)
  isPropExpNat A B c app =
    isPropΠ λ e → isPropΠ λ d → isPropΠ λ k → isPropΠ λ g → isPropΠ λ a →
    isSetF₀ B e _ _

  ExpEl : (A B : PSh C ℓ) (c : Ob) → Type ℓ
  ExpEl A B c =
    Σ[ app ∈ ((d : Ob) → Hom d c → F₀ A d → F₀ B d) ] ExpNat A B c app

  -- Two elements agree as soon as their families agree.
  ExpEl≡ : (A B : PSh C ℓ) (c : Ob) (u v : ExpEl A B c)
         → fst u ≡ fst v → u ≡ v
  ExpEl≡ A B c u v p =
    ΣPathP (p , isProp→PathP (λ i → isPropExpNat A B c (p i)) (snd u) (snd v))

  isSetExpEl : (A B : PSh C ℓ) (c : Ob) → isSet (ExpEl A B c)
  isSetExpEl A B c =
    isSetΣ (isSetΠ λ d → isSetΠ λ g → isSetΠ λ a → isSetF₀ B d)
           (λ app → isProp→isSet (isPropExpNat A B c app))

  -- ----------------------------------------------------------
  -- Restriction precomposes the index arrow.
  -- ----------------------------------------------------------
  expRestr : (A B : PSh C ℓ) {d c : Ob} → Hom d c → ExpEl A B c → ExpEl A B d
  expRestr A B {d} {c} f (app , nat) =
    (λ e g a → app e (g ⋆ f) a) ,
    (λ e d' k g a →
      subst (λ h → app e h (F₁ A k a) ≡ F₁ B k (app d' (g ⋆ f) a))
            (sym (⋆-assoc k g f))
            (nat e d' k (g ⋆ f) a))

  -- ----------------------------------------------------------
  -- The exponential presheaf.
  -- ----------------------------------------------------------
  Exp : PSh C ℓ → PSh C ℓ → PSh C ℓ
  Exp A B = record
    { F₀      = ExpEl A B
    ; F₁      = expRestr A B
    ; F-id    = λ {c} u → ExpEl≡ A B c _ u
                  (funExt λ e → funExt λ g → funExt λ a →
                    cong (λ h → fst u e h a) (⋆-idR g))
    ; F-comp  = λ {x} {y} {z} f g u → ExpEl≡ A B x _ _
                  (funExt λ e → funExt λ h → funExt λ a →
                    cong (λ w → fst u e w a) (sym (⋆-assoc h f g)))
    ; isSetF₀ = isSetExpEl A B
    }
