{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Topos.Rule2 — internal Pearl Rule 2 (action/observation
-- exchange) on the confounded model, lifting RuleDoCalc/Rule2.
--
-- On a confounded internal SCM with a structural CI witness
-- (X ⫫ Z in the prior), the internal intervention do(X := x₀)
-- and the internal conditioning agree on the downstream
-- (Z,Y)- and Y-marginals, at every regime — by lifting the
-- verified core theorem Rule2.rule2-marginal-* pointwise.
--
-- Levels (each strictly stronger):
--  * pointwise rule2-{ZY,Y}-E (regime-wise);
--  * rule2-{Y,ZY}-section (internal-morphism, naturality hypothesised);
--  * SCM-conf-E-nat + margY-conf-nat: the Y-marginal of a NATURAL
--    confounded SCM is DERIVED natural (confounded analogue of
--    Topos.SCMNat.marg-nat), via the fuse marginal-Y ≡ pXZ >>= (kY ∘ ⟨fst,snd⟩);
--  * do-conf-nat: do-X-conf PRESERVES naturality;
--  * rule2-Y-section-derived: FULLY-DERIVED internal Rule 2 (no naturality
--    hypotheses) — LHS naturality from margY-conf-nat, RHS naturality
--    transported along the pointwise rule2, equality by Nat≡.
-- ============================================================

module Topos.Rule2 where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (tt)

open import FDist-Convex using (FDist; pure; _>>=_; mapF)
open import Rule2 using
  ( SCM-conf ; pXZ ; kY ; X-indep-Z ; do-X-conf ; cond-X-conf
  ; marginal-ZY ; marginal-Y ; rule2-marginal-ZY ; rule2-marginal-Y )

open import Topos.Cat
open import Topos.PSh
open import Topos.InternalDist

-- The Y-marginal of a confounded SCM fuses: the triple-nested joint
-- collapses (mapF-∘ then mapF-id) to a prior-kernel convolution.
margY-conf-fuse : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
  (m : SCM-conf X Z Y)
  → marginal-Y m ≡ (pXZ m >>= λ p → kY m (fst p) (snd p))
margY-conf-fuse m =
    mapF-bindR (λ p → snd (snd p)) (pXZ m)
      (λ p → mapF (λ y → (fst p , snd p , y)) (kY m (fst p) (snd p)))
  ∙ cong (pXZ m >>=_) (funExt λ p →
      sym (mapF-∘ (λ q → snd (snd q)) (λ y → (fst p , snd p , y)) (kY m (fst p) (snd p)))
      ∙ mapF-id (kY m (fst p) (snd p)))

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  -- internal confounded SCM (bare regime-indexed family)
  SCM-conf-E : ∀ {ℓX ℓZ ℓY} → PSh C ℓX → PSh C ℓZ → PSh C ℓY → Type _
  SCM-conf-E X Z Y = (c : Ob) → SCM-conf (F₀ X c) (F₀ Z c) (F₀ Y c)

  module _ {ℓX ℓZ ℓY} {X : PSh C ℓX} {Z : PSh C ℓZ} {Y : PSh C ℓY} where

    -- internal structural CI witness: regime-wise X ⫫ Z in the prior
    X-indep-Z-E : SCM-conf-E X Z Y → Type _
    X-indep-Z-E m = (c : Ob) → X-indep-Z (m c)

    -- internal intervention do(X := x₀), regime-wise kernel surgery
    do-X-conf-E : ((c : Ob) → F₀ X c) → SCM-conf-E X Z Y → SCM-conf-E X Z Y
    do-X-conf-E x₀ m = λ c → do-X-conf (x₀ c) (m c)

    -- pointwise internal Rule 2: intervention = conditioning on the
    -- (Z,Y)- and Y-marginals, under the structural CI witness
    rule2-ZY-E : (m : SCM-conf-E X Z Y) (ind : X-indep-Z-E m)
                 (x₀ : (c : Ob) → F₀ X c) (c : Ob)
               → marginal-ZY (do-X-conf (x₀ c) (m c))
                 ≡ marginal-ZY (cond-X-conf (x₀ c) (m c) (ind c))
    rule2-ZY-E m ind x₀ c = rule2-marginal-ZY (m c) (ind c) (x₀ c)

    rule2-Y-E : (m : SCM-conf-E X Z Y) (ind : X-indep-Z-E m)
                (x₀ : (c : Ob) → F₀ X c) (c : Ob)
              → marginal-Y (do-X-conf (x₀ c) (m c))
                ≡ marginal-Y (cond-X-conf (x₀ c) (m c) (ind c))
    rule2-Y-E m ind x₀ c = rule2-marginal-Y (m c) (ind c) (x₀ c)

    -- ------------------------------------------------------------
    -- Section upgrade (the rule1-E-nat-level form): given that the
    -- intervened and conditioned downstream marginals are natural
    -- (witnesses ndo, nm — the confounded-model analogue of
    -- Topos.SCMNat.marg-nat, derivable from natural pXZ/kY/witness),
    -- internal Rule 2 is an EQUALITY OF INTERNAL MORPHISMS, via Nat≡
    -- of the pointwise rule2.
    -- ------------------------------------------------------------
    rule2-Y-section :
        (m : SCM-conf-E X Z Y) (ind : X-indep-Z-E m) (x₀ : (c : Ob) → F₀ X c)
        (ndo : IsNat 𝟙 (Dist_E Y) (λ c _ → marginal-Y (do-X-conf (x₀ c) (m c))))
        (nm  : IsNat 𝟙 (Dist_E Y) (λ c _ → marginal-Y (cond-X-conf (x₀ c) (m c) (ind c))))
      → _≡_ {A = Section (Dist_E Y)}
          ((λ c _ → marginal-Y (do-X-conf (x₀ c) (m c))) , ndo)
          ((λ c _ → marginal-Y (cond-X-conf (x₀ c) (m c) (ind c))) , nm)
    rule2-Y-section m ind x₀ ndo nm =
      Nat≡ {X = 𝟙} {Y = Dist_E Y} _ _
        (λ c _ → rule2-marginal-Y (m c) (ind c) (x₀ c))

    rule2-ZY-section :
        (m : SCM-conf-E X Z Y) (ind : X-indep-Z-E m) (x₀ : (c : Ob) → F₀ X c)
        (ndo : IsNat 𝟙 (Dist_E (Z ×ᴾ Y)) (λ c _ → marginal-ZY (do-X-conf (x₀ c) (m c))))
        (nm  : IsNat 𝟙 (Dist_E (Z ×ᴾ Y)) (λ c _ → marginal-ZY (cond-X-conf (x₀ c) (m c) (ind c))))
      → _≡_ {A = Section (Dist_E (Z ×ᴾ Y))}
          ((λ c _ → marginal-ZY (do-X-conf (x₀ c) (m c))) , ndo)
          ((λ c _ → marginal-ZY (cond-X-conf (x₀ c) (m c) (ind c))) , nm)
    rule2-ZY-section m ind x₀ ndo nm =
      Nat≡ {X = 𝟙} {Y = Dist_E (Z ×ᴾ Y)} _ _
        (λ c _ → rule2-marginal-ZY (m c) (ind c) (x₀ c))

-- ============================================================
-- Natural confounded internal SCM, and the DERIVED Y-marginal
-- naturality (confounded analogue of Topos.SCMNat.marg-nat).
-- ============================================================

module _ {ℓo ℓh} {C : Precategory ℓo ℓh} where
  open Precategory C
  open PSh

  record SCM-conf-E-nat {ℓX ℓZ ℓY} (X : PSh C ℓX) (Z : PSh C ℓZ) (Y : PSh C ℓY)
         : Type (ℓ-max (ℓ-max ℓo ℓh) (ℓ-max ℓX (ℓ-max ℓZ ℓY))) where
    field
      pXZs    : (c : Ob) → FDist (F₀ X c × F₀ Z c)
      kYs     : (c : Ob) → F₀ X c → F₀ Z c → FDist (F₀ Y c)
      pXZ-nat : (x y : Ob) (f : Hom x y)
              → pXZs x ≡ mapF (λ p → (F₁ X f (fst p) , F₁ Z f (snd p))) (pXZs y)
      kY-nat  : (x y : Ob) (f : Hom x y) (a : F₀ X y) (b : F₀ Z y)
              → kYs x (F₁ X f a) (F₁ Z f b) ≡ mapF (F₁ Y f) (kYs y a b)

  module _ {ℓX ℓZ ℓY} {X : PSh C ℓX} {Z : PSh C ℓZ} {Y : PSh C ℓY} where
    open SCM-conf-E-nat

    toFamC : SCM-conf-E-nat X Z Y → (c : Ob) → SCM-conf (F₀ X c) (F₀ Z c) (F₀ Y c)
    toFamC M c = record { pXZ = pXZs M c ; kY = kYs M c }

    -- DERIVED: the confounded Y-marginal is natural
    margY-conf-nat : (M : SCM-conf-E-nat X Z Y) (x y : Ob) (f : Hom x y)
      → marginal-Y (toFamC M x) ≡ mapF (F₁ Y f) (marginal-Y (toFamC M y))
    margY-conf-nat M x y f =
        margY-conf-fuse (toFamC M x)
      ∙ cong (_>>= (λ p → kYs M x (fst p) (snd p))) (pXZ-nat M x y f)
      ∙ mapF-bindL (λ p → (F₁ X f (fst p) , F₁ Z f (snd p)))
                   (pXZs M y) (λ p → kYs M x (fst p) (snd p))
      ∙ cong (pXZs M y >>=_) (funExt λ p → kY-nat M x y f (fst p) (snd p))
      ∙ sym (mapF-bindR (F₁ Y f) (pXZs M y) (λ p → kYs M y (fst p) (snd p)))
      ∙ cong (mapF (F₁ Y f)) (sym (margY-conf-fuse (toFamC M y)))

    -- the confounded Y-marginal as a genuine internal global element
    marginalY-conf-Section : SCM-conf-E-nat X Z Y → Section {C = C} (Dist_E Y)
    marginalY-conf-Section M =
      (λ c _ → marginal-Y (toFamC M c)) ,
      (λ x y f _ → margY-conf-nat M x y f)

    -- do-X-conf PRESERVES naturality: intervening by a regime-coherent
    -- value x₀ : 𝟙 ⇒ X sends a natural confounded SCM to a natural one.
    -- The prior-naturality proof routes both sides through the common
    -- middle term  mapF (λ q → (x₀ x , F₁ Z f (snd q))) (pXZs M y)  via mapF-∘.
    do-conf-nat : Section {C = C} X → SCM-conf-E-nat X Z Y → SCM-conf-E-nat X Z Y
    do-conf-nat x₀ M = record
      { pXZs = λ c → mapF (fst x₀ c tt ,_) (mapF snd (pXZs M c))
      ; kYs  = kYs M
      ; pXZ-nat = λ x y f →
          ( sym (mapF-∘ (fst x₀ x tt ,_) snd (pXZs M x))
          ∙ cong (mapF (λ p → (fst x₀ x tt , snd p))) (pXZ-nat M x y f)
          ∙ sym (mapF-∘ (λ p → (fst x₀ x tt , snd p))
                        (λ p → (F₁ X f (fst p) , F₁ Z f (snd p))) (pXZs M y)) )
        ∙ sym
          ( sym (mapF-∘ (λ p → (F₁ X f (fst p) , F₁ Z f (snd p)))
                        (fst x₀ y tt ,_) (mapF snd (pXZs M y)))
          ∙ sym (mapF-∘ (λ z → (F₁ X f (fst x₀ y tt) , F₁ Z f z)) snd (pXZs M y))
          ∙ cong (λ w → mapF (λ q → (w , F₁ Z f (snd q))) (pXZs M y)) (sym (snd x₀ x y f tt)) )
      ; kY-nat = kY-nat M
      }

    -- FULLY-DERIVED internal Rule 2 (Y-marginal): NO naturality hypotheses.
    -- LHS naturality from margY-conf-nat (do-conf-nat is natural); RHS
    -- naturality transported along the pointwise rule2; equality by Nat≡.
    rule2-Y-section-derived :
        (M : SCM-conf-E-nat X Z Y)
        (ind : (c : Ob) → X-indep-Z (toFamC M c))
        (x₀ : Section {C = C} X)
      → _≡_ {A = Section {C = C} (Dist_E Y)}
          (marginalY-conf-Section (do-conf-nat x₀ M))
          ( (λ c _ → marginal-Y (cond-X-conf (fst x₀ c tt) (toFamC M c) (ind c)))
          , subst (IsNat 𝟙 (Dist_E Y))
                  (funExt (λ c → funExt (λ _ → rule2-marginal-Y (toFamC M c) (ind c) (fst x₀ c tt))))
                  (snd (marginalY-conf-Section (do-conf-nat x₀ M))) )
    rule2-Y-section-derived M ind x₀ =
      Nat≡ {X = 𝟙} {Y = Dist_E Y} _ _
        (λ c _ → rule2-marginal-Y (toFamC M c) (ind c) (fst x₀ c tt))
