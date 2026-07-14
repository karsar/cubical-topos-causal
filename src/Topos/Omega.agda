{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Omega — the subobject classifier of the presheaf topos,
-- and interventions as characteristic maps into it.
--
-- Ω(c) = sieves on c (downward-closed families of morphisms into
-- c); restriction is sieve pullback.  The truth ⊤ : 𝟙 ⇒ Ω is the
-- maximal sieve.  A subpresheaf is classified by a characteristic
-- map χ : B ⇒ Ω, with b ∈ A iff χ(b) is the maximal sieve.
--
-- This realises Mahadevan's "intervention via the subobject
-- classifier" directed-topos-internally: do(X := x₀) is the
-- characteristic map of the value-fixing subobject.
-- ============================================================

module Topos.Omega where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma using (Σ-syntax; _,_; fst; snd; ΣPathP)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*)

open import Topos.Cat
open import Topos.PSh

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- membership of a sieve on c: a prop-valued predicate on morphisms into c
  SieveMem : Ob → Type (ℓ-max ℓo (ℓ-suc ℓh))
  SieveMem c = (d : Ob) → Hom d c → hProp ℓh

  -- closure under precomposition
  Closure : (c : Ob) → SieveMem c → Type (ℓ-max ℓo ℓh)
  Closure c mem = (d e : Ob) (k : Hom e d) (f : Hom d c)
                → fst (mem d f) → fst (mem e (k ⋆ f))

  Sieve : Ob → Type (ℓ-max ℓo (ℓ-suc ℓh))
  Sieve c = Σ[ mem ∈ SieveMem c ] Closure c mem

  isPropClosure : {c : Ob} (mem : SieveMem c) → isProp (Closure c mem)
  isPropClosure mem = isPropΠ λ d → isPropΠ λ e → isPropΠ λ k → isPropΠ λ f →
                      isPropΠ λ _ → snd (mem e (k ⋆ f))

  -- two sieves are equal as soon as their membership predicates agree
  Sieve≡ : {c : Ob} (S T : Sieve c) → fst S ≡ fst T → S ≡ T
  Sieve≡ S T p = ΣPathP (p , isProp→PathP (λ i → isPropClosure (p i)) (snd S) (snd T))

  isSetSieve : {c : Ob} → isSet (Sieve c)
  isSetSieve = isSetΣ (isSetΠ λ d → isSetΠ λ f → isSetHProp)
                      (λ mem → isProp→isSet (isPropClosure mem))

  -- pullback of a sieve along a morphism = the action of Ω on morphisms
  pull : {c' c : Ob} → Hom c' c → Sieve c → Sieve c'
  pull h S =
    (λ d f → fst S d (f ⋆ h)) ,
    (λ d e k f pf → subst (λ q → fst (fst S e q)) (sym (⋆-assoc k f h))
                          (snd S d e k (f ⋆ h) pf))

  -- the subobject classifier
  Ω : PSh C (ℓ-max ℓo (ℓ-suc ℓh))
  Ω = record
    { F₀ = Sieve
    ; F₁ = pull
    ; F-id = λ S → Sieve≡ (pull idn S) S
        (funExt λ d → funExt λ f → cong (fst S d) (⋆-idR f))
    ; F-comp = λ f g S → Sieve≡ (pull (f ⋆ g) S) (pull f (pull g S))
        (funExt λ d → funExt λ p → cong (fst S d) (sym (⋆-assoc p f g)))
    ; isSetF₀ = λ c → isSetSieve
    }

  -- truth: the maximal sieve (all morphisms), as an internal global element
  maximal : (c : Ob) → Sieve c
  maximal c = (λ d f → (Unit* , isPropUnit*)) , (λ d e k f _ → tt*)

  ⊤Ω : Section {C = C} Ω
  ⊤Ω = (λ c _ → maximal c) ,
       (λ x y f _ → Sieve≡ (maximal x) (pull f (maximal y)) refl)
