{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Classifier — Ω is the subobject classifier.
--
-- Topos.Omega builds Ω, the presheaf of sieves.
-- Topos.DoClassifier classifies one subobject, the value-fixing
-- {x₀} ↪ X.  This module proves the universal property in
-- general.
--
-- Take a presheaf B and a predicate P on B that is closed under
-- restriction.  Then P is classified by a characteristic map
-- χ : B ⇒ Ω whose ⊤-fibre is exactly P.  That map is unique:
-- any natural χ' : B ⇒ Ω with the same ⊤-fibre is equal to χ.
-- The intervention classifier of Topos.DoClassifier is the
-- instance  P c b = (b ≡ x₀ c).
--
-- Uniqueness rests on one fact about sieves.  A sieve that
-- contains the identity is maximal, because closure under
-- precomposition carries idn to every arrow.  So membership of
-- χ'_c(b) at f is forced to be "F₁ B f b ∈ P", which is χ_c(b)
-- by definition.
-- ============================================================

module Topos.Classifier where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic using (⇔toPath)
open import Cubical.Data.Sigma using (_,_; fst; snd; _×_)
open import Cubical.Data.Unit using (Unit*; tt*; isPropUnit*; tt)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega

-- ------------------------------------------------------------
-- A fact about sieves.  A sieve that contains the identity is
-- maximal.  A maximal sieve contains every arrow.
-- ------------------------------------------------------------
module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  idn∈→maximal : {c : Ob} (S : Sieve {C = C} c)
               → fst (fst S c idn) → S ≡ maximal {C = C} c
  idn∈→maximal {c} S pf =
    Sieve≡ {C = C} S (maximal {C = C} c)
      (funExt λ d → funExt λ f →
        ⇔toPath {P = fst S d f} {Q = (Unit* , isPropUnit*)}
          (λ _ → tt*)
          (λ _ → subst (λ g → fst (fst S d g)) (⋆-idR f)
                       (snd S c d f idn pf)))

  maximal→mem : {c : Ob} (S : Sieve {C = C} c) → S ≡ maximal {C = C} c
              → (d : Ob) (f : Hom d c) → fst (fst S d f)
  maximal→mem S eq d f = transport (λ i → fst (fst (eq (~ i)) d f)) tt*

-- ------------------------------------------------------------
-- The universal property of Ω.  Here P is any predicate on the
-- presheaf B that is closed under restriction.
-- ------------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} (B : PSh C ℓ)
         (P : (c : Precategory.Ob C) → PSh.F₀ B c → hProp ℓ)
         (P-closed : (d e : Precategory.Ob C) (k : Precategory.Hom C e d)
                     (b : PSh.F₀ B d)
                   → fst (P d b) → fst (P e (PSh.F₁ B k b)))
         where
  open Precategory C
  open PSh

  -- χ_c(b) is the sieve of the arrows along which b restricts
  -- into P.
  χ-mem : (c : Ob) → F₀ B c → SieveMem {C = C} c
  χ-mem c b d f = P d (F₁ B f b)

  χ-closed : (c : Ob) (b : F₀ B c) → Closure {C = C} c (χ-mem c b)
  χ-closed c b d e k f pf =
    subst (λ z → fst (P e z)) (sym (F-comp B k f b))
          (P-closed d e k (F₁ B f b) pf)

  χ-sieve : (c : Ob) → F₀ B c → Sieve {C = C} c
  χ-sieve c b = χ-mem c b , χ-closed c b

  χ-nat : IsNat B Ω (λ c b → χ-sieve c b)
  χ-nat x y f b =
    Sieve≡ {C = C} (χ-sieve x (F₁ B f b)) (pull {C = C} f (χ-sieve y b))
      (funExt λ d → funExt λ g → cong (P d) (sym (F-comp B g f b)))

  χ : Nat B Ω
  χ = (λ c b → χ-sieve c b) , χ-nat

  -- The ⊤-fibre of χ is exactly P.  We prove both directions.
  classifies-fwd : (c : Ob) (b : F₀ B c)
                 → fst (P c b) → χ-sieve c b ≡ maximal {C = C} c
  classifies-fwd c b hyp =
    Sieve≡ {C = C} (χ-sieve c b) (maximal {C = C} c)
      (funExt λ d → funExt λ f →
        ⇔toPath {P = P d (F₁ B f b)} {Q = (Unit* , isPropUnit*)}
          (λ _ → tt*)
          (λ _ → P-closed c d f b hyp))

  classifies-bwd : (c : Ob) (b : F₀ B c)
                 → χ-sieve c b ≡ maximal {C = C} c → fst (P c b)
  classifies-bwd c b eq =
    subst (λ z → fst (P c z)) (F-id B b)
          (maximal→mem {C = C} (χ-sieve c b) eq c idn)

  -- The property "α has ⊤-fibre P", and the uniqueness proof.
  Classifies : ((c : Ob) → F₀ B c → Sieve {C = C} c) → Type (ℓ-suc ℓ)
  Classifies α =
    (c : Ob) (b : F₀ B c)
    → (fst (P c b) → α c b ≡ maximal {C = C} c)
    × (α c b ≡ maximal {C = C} c → fst (P c b))

  χ-classifies : Classifies (λ c b → χ-sieve c b)
  χ-classifies c b = classifies-fwd c b , classifies-bwd c b

  unique : (χ' : Nat B Ω) → Classifies (fst χ') → χ' ≡ χ
  unique (α' , nat') cls =
    Nat≡ {X = B} {Y = Ω} (α' , nat') χ
      (λ c b → Sieve≡ {C = C} (α' c b) (χ-sieve c b)
        (funExt λ d → funExt λ f →
          ⇔toPath {P = fst (α' c b) d f} {Q = P d (F₁ B f b)}
            (λ pf → snd (cls d (F₁ B f b))
                      ( nat' d c f b
                      ∙ idn∈→maximal {C = C} (pull {C = C} f (α' c b))
                          (subst (λ g → fst (fst (α' c b) d g))
                                 (sym (⋆-idL f)) pf) ))
            (λ q → subst (λ g → fst (fst (α' c b) d g)) (⋆-idL f)
                     (maximal→mem {C = C} (pull {C = C} f (α' c b))
                       (sym (nat' d c f b) ∙ fst (cls d (F₁ B f b)) q)
                       d idn)) ))

-- ------------------------------------------------------------
-- The intervention classifier as an instance.  Take the
-- predicate P c b = (b ≡ x₀ c).  This is the subobject
-- {x₀} ↪ X of Topos.DoClassifier, now one case of the general
-- construction.  Here χ-mem computes to (F₁ X f b ≡ x₀ d),
-- which is DoClassifier.χ-mem definitionally.
-- ------------------------------------------------------------
module _ {ℓ} {C : Precategory ℓ ℓ} (X : PSh C ℓ) (x₀ : Section {C = C} X) where
  open Precategory C
  open PSh

  ptC : (c : Ob) → F₀ X c
  ptC c = fst x₀ c tt

  P-fix : (c : Ob) → F₀ X c → hProp ℓ
  P-fix c b = (b ≡ ptC c) , isSetF₀ X c b (ptC c)

  P-fix-closed : (d e : Ob) (k : Hom e d) (b : F₀ X d)
               → fst (P-fix d b) → fst (P-fix e (F₁ X k b))
  P-fix-closed d e k b hyp = cong (F₁ X k) hyp ∙ sym (snd x₀ e d k tt)

  -- The value-fixing classifier, with its universal property.
  do-classifier : Nat X Ω
  do-classifier = χ X P-fix P-fix-closed

  do-classifier-unique : (χ' : Nat X Ω)
                       → Classifies X P-fix P-fix-closed (fst χ')
                       → χ' ≡ do-classifier
  do-classifier-unique = unique X P-fix P-fix-closed
