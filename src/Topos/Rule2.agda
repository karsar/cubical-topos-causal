{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.Rule2 — internal Pearl Rule 2 (action/observation
-- exchange) on the confounded model, lifting RuleDoCalc/Rule2.
--
-- A confounded SCM has a joint prior pXZ on (X,Z) and a kernel
-- kY that depends on both X and Z.  A structural CI witness is a
-- proof that X ⫫ Z in that prior.  Given one, the internal
-- intervention do(X := x₀) and the internal conditioning agree
-- on the downstream (Z,Y)- and Y-marginals, at every regime.
-- The proof applies the verified core theorems
-- Rule2.rule2-marginal-ZY and rule2-marginal-Y at each regime.
--
-- Levels, each stronger than the one before it:
--  * rule2-{ZY,Y}-E: the pointwise form, one regime at a time;
--  * rule2-{Y,ZY}-section: an equality of internal morphisms,
--    with naturality assumed;
--  * SCM-conf-E-nat and margY-conf-nat: the Y-marginal of a
--    natural confounded SCM is itself natural.  This level proves
--    that; the level above assumes it.  It is the confounded
--    analogue of Topos.SCMNat.marg-nat.
--    The proof goes through the fusion
--    marginal-Y ≡ pXZ >>= (kY ∘ ⟨fst,snd⟩);
--  * do-conf-nat: do-X-conf preserves naturality;
--  * rule2-Y-section-derived: internal Rule 2 with no naturality
--    hypothesis.  Naturality of the left side comes from
--    margY-conf-nat.  Naturality of the right side is
--    transported along the pointwise rule2.  Nat≡ gives the
--    equality.
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

-- The Y-marginal of a confounded SCM has a shorter form.  The
-- triple-nested joint collapses to a bind of the prior with the
-- kernel, by mapF-∘ and then mapF-id.
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

  -- An internal confounded SCM: one SCM-conf per regime, with no
  -- naturality condition.
  SCM-conf-E : ∀ {ℓX ℓZ ℓY} → PSh C ℓX → PSh C ℓZ → PSh C ℓY → Type _
  SCM-conf-E X Z Y = (c : Ob) → SCM-conf (F₀ X c) (F₀ Z c) (F₀ Y c)

  module _ {ℓX ℓZ ℓY} {X : PSh C ℓX} {Z : PSh C ℓZ} {Y : PSh C ℓY} where

    -- The internal structural CI witness: X ⫫ Z in the prior, at
    -- every regime.
    X-indep-Z-E : SCM-conf-E X Z Y → Type _
    X-indep-Z-E m = (c : Ob) → X-indep-Z (m c)

    -- The internal intervention do(X := x₀), applied at each regime.
    do-X-conf-E : ((c : Ob) → F₀ X c) → SCM-conf-E X Z Y → SCM-conf-E X Z Y
    do-X-conf-E x₀ m = λ c → do-X-conf (x₀ c) (m c)

    -- Internal Rule 2, one regime at a time.  Under the structural
    -- CI witness, intervention agrees with conditioning on the
    -- (Z,Y)- and Y-marginals.
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
    -- The Section form, at the level of rule1-E-nat.  Assume the
    -- intervened and the conditioned downstream marginals are
    -- natural; the witnesses ndo and nm carry that assumption.
    -- They are the confounded analogue of Topos.SCMNat.marg-nat,
    -- and are derivable from a natural pXZ, a natural kY and the
    -- CI witness.  Under them, Nat≡ turns the pointwise rule2 into
    -- an equality of internal morphisms.
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
-- The natural confounded internal SCM, and the derived
-- naturality of its Y-marginal.  This is the confounded
-- analogue of Topos.SCMNat.marg-nat.
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

    -- Derived: the confounded Y-marginal is natural.
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

    -- The confounded Y-marginal as an internal global element.
    marginalY-conf-Section : SCM-conf-E-nat X Z Y → Section {C = C} (Dist_E Y)
    marginalY-conf-Section M =
      (λ c _ → marginal-Y (toFamC M c)) ,
      (λ x y f _ → margY-conf-nat M x y f)

    -- do-X-conf preserves naturality.  Intervening by a
    -- regime-coherent value x₀ : 𝟙 ⇒ X sends a natural confounded
    -- SCM to a natural one.  The proof of prior naturality takes
    -- both sides to the common middle term
    --   mapF (λ q → (x₀ x , F₁ Z f (snd q))) (pXZs M y)
    -- by mapF-∘.
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

    -- Internal Rule 2 for the Y-marginal, with no naturality
    -- hypothesis.  Naturality of the left side comes from
    -- margY-conf-nat, since do-conf-nat is natural.  Naturality of
    -- the right side is transported along the pointwise rule2.
    -- Nat≡ gives the equality.
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
