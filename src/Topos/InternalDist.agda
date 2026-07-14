{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.InternalDist — THE REUSE SEAM.
--
-- The internal distribution object of the presheaf topos Set^Cᵒᵖ
-- is the verified probability monad FDist applied regime-wise:
--
--     (Dist_E X)(c) = FDist (X c),   restriction = mapF (X-restriction).
--
-- Its presheaf functor laws reduce to functoriality of `mapF`,
-- which in turn is exactly the monad laws already proved in the
-- core (RuleDoCalc.>>=-unitR / >>=-assoc). Nothing about the
-- probability monad is re-proved here.
-- ============================================================

module Topos.InternalDist where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude

open import FDist-Convex using (FDist; pure; _>>=_; mapF; trunc)
open import RuleDoCalc  using (>>=-unitR; >>=-assoc)

open import Topos.Cat
open import Topos.PSh

-- functoriality of mapF — pure corollaries of the core monad laws
mapF-id : ∀ {ℓ} {A : Type ℓ} (d : FDist A) → mapF (λ a → a) d ≡ d
mapF-id d = >>=-unitR d

mapF-∘ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (g : B → C) (f : A → B) (d : FDist A)
       → mapF (λ a → g (f a)) d ≡ mapF g (mapF f d)
mapF-∘ g f d = sym (>>=-assoc d (λ a → pure (f a)) (λ b → pure (g b)))

-- mapF interacts with bind on both sides (from associativity)
mapF-bindL : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (h : A → B) (d : FDist A) (k : B → FDist C)
           → (mapF h d >>= k) ≡ (d >>= (λ a → k (h a)))
mapF-bindL h d k = >>=-assoc d (λ a → pure (h a)) k

mapF-bindR : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
             (g : B → C) (d : FDist A) (k : A → FDist B)
           → mapF g (d >>= k) ≡ (d >>= (λ a → mapF g (k a)))
mapF-bindR g d k = >>=-assoc d k (λ b → pure (g b))

-- the internal distribution monad as an endofunctor on presheaves
module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  Dist_E : ∀ {ℓ} → PSh C ℓ → PSh C ℓ
  Dist_E X = record
    { F₀      = λ c → FDist (F₀ X c)
    ; F₁      = λ f → mapF (F₁ X f)
    ; F-id    = λ {x} d →
        cong (λ h → mapF h d) (funExt (F-id X)) ∙ mapF-id d
    ; F-comp  = λ {x} {y} {z} f g d →
        cong (λ h → mapF h d) (funExt (F-comp X f g)) ∙ mapF-∘ (F₁ X f) (F₁ X g) d
    ; isSetF₀ = λ c → trunc
    }
