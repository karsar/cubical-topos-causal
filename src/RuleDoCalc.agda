{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- RuleDoCalc.agda
--
-- Pearl's do-calculus in kernel form, on small structural causal
-- models. Built directly on FDist-Convex.
--
-- Rules verified:
--   * Rule 1 (insertion/deletion of observations) on SCM₂ and
--     the SCM₃ chain — observing a variable that the outcome
--     does not depend on leaves the outcome's marginal unchanged.
--   * Rule 3 (insertion/deletion of actions) on SCM₃ chain —
--     intervening on a downstream variable leaves an upstream
--     marginal unchanged.
--
-- Rule 2 (action/observation exchange) is in a sibling file
-- once the substitution-conditioning agreement lemma is proved.
--
-- The proofs use only the monad laws (which we derive here from
-- the bind definition in FDist-Convex) and constBind (the
-- structural lemma asserting d >>= λ_ → e ≡ e). No new
-- postulates beyond what FDist-Convex provides.
-- ============================================================

module RuleDoCalc where

open import Cubical.Core.Primitives
open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (_∘_)

open import FDist-Convex

-- ============================================================
-- Section 1: Monad laws.
--
-- We derive >>=-unitR, >>=-assoc, and constBind on the
-- convex-framework FDist (which has mix-assoc-pos instead of
-- full mix-assoc; one extra path-constructor case compared to
-- the original FDist-base derivation).
-- ============================================================

-- Right unit: d >>= pure ≡ d
>>=-unitR : ∀ {ℓ} {A : Type ℓ} (d : FDist A) → (d >>= pure) ≡ d
>>=-unitR (pure a) = refl
>>=-unitR (mix p d₁ d₂) = cong₂ (mix p) (>>=-unitR d₁) (>>=-unitR d₂)
>>=-unitR (mix-idem p d i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (>>=-unitR d) (>>=-unitR d))
    (>>=-unitR d)
    (mix-idem p (d >>= pure))
    (mix-idem p d)
    i
>>=-unitR (mix-comm p d₁ d₂ i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (>>=-unitR d₁) (>>=-unitR d₂))
    (cong₂ (mix (1-w p)) (>>=-unitR d₂) (>>=-unitR d₁))
    (mix-comm p (d₁ >>= pure) (d₂ >>= pure))
    (mix-comm p d₁ d₂)
    i
>>=-unitR (mix-bdy0 d₁ d₂ i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix w0) (>>=-unitR d₁) (>>=-unitR d₂))
    (>>=-unitR d₂)
    (mix-bdy0 (d₁ >>= pure) (d₂ >>= pure))
    (mix-bdy0 d₁ d₂)
    i
>>=-unitR (mix-bdy1 d₁ d₂ i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix w1) (>>=-unitR d₁) (>>=-unitR d₂))
    (>>=-unitR d₁)
    (mix-bdy1 (d₁ >>= pure) (d₂ >>= pure))
    (mix-bdy1 d₁ d₂)
    i
>>=-unitR (mix-assoc-pos p q ps a b c i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (>>=-unitR a)
                    (cong₂ (mix q) (>>=-unitR b) (>>=-unitR c)))
    (cong₂ (mix (s-of p q))
           (cong₂ (mix (r-of p q ps)) (>>=-unitR a) (>>=-unitR b))
           (>>=-unitR c))
    (mix-assoc-pos p q ps (a >>= pure) (b >>= pure) (c >>= pure))
    (mix-assoc-pos p q ps a b c)
    i
>>=-unitR (mix-interchange p q a b c d i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p)
           (cong₂ (mix q) (>>=-unitR a) (>>=-unitR b))
           (cong₂ (mix q) (>>=-unitR c) (>>=-unitR d)))
    (cong₂ (mix q)
           (cong₂ (mix p) (>>=-unitR a) (>>=-unitR c))
           (cong₂ (mix p) (>>=-unitR b) (>>=-unitR d)))
    (mix-interchange p q (a >>= pure) (b >>= pure) (c >>= pure) (d >>= pure))
    (mix-interchange p q a b c d)
    i
>>=-unitR (mix-bayes-interchange p q₁ q₂ pM pM' a b c d i) =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p)
           (cong₂ (mix q₁) (>>=-unitR a) (>>=-unitR c))
           (cong₂ (mix q₂) (>>=-unitR b) (>>=-unitR d)))
    (cong₂ (mix (mix-w p q₁ q₂))
           (cong₂ (mix (bayesW p q₁ q₂ pM)) (>>=-unitR a) (>>=-unitR b))
           (cong₂ (mix (bayesW p (1-w q₁) (1-w q₂) pM')) (>>=-unitR c) (>>=-unitR d)))
    (mix-bayes-interchange p q₁ q₂ pM pM'
       (a >>= pure) (b >>= pure) (c >>= pure) (d >>= pure))
    (mix-bayes-interchange p q₁ q₂ pM pM' a b c d)
    i
>>=-unitR (trunc d₁ d₂ p q i j) =
  isSet→SquareP
    (λ i j → isOfHLevelSuc 1
      (trunc (trunc d₁ d₂ p q i j >>= pure)
             (trunc d₁ d₂ p q i j)))
    (cong >>=-unitR p)
    (cong >>=-unitR q)
    refl
    refl
    i j

-- Associativity: (d >>= k) >>= l ≡ d >>= (λ a → k a >>= l)
>>=-assoc : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
  (d : FDist A) (k : A → FDist B) (l : B → FDist C)
  → ((d >>= k) >>= l) ≡ (d >>= (λ a → k a >>= l))
>>=-assoc (pure a) k l = refl
>>=-assoc (mix p d₁ d₂) k l =
  cong₂ (mix p) (>>=-assoc d₁ k l) (>>=-assoc d₂ k l)
>>=-assoc (mix-idem p d i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (>>=-assoc d k l) (>>=-assoc d k l))
    (>>=-assoc d k l)
    (mix-idem p ((d >>= k) >>= l))
    (mix-idem p (d >>= (λ a → k a >>= l)))
    i
>>=-assoc (mix-comm p d₁ d₂ i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (>>=-assoc d₁ k l) (>>=-assoc d₂ k l))
    (cong₂ (mix (1-w p)) (>>=-assoc d₂ k l) (>>=-assoc d₁ k l))
    (mix-comm p ((d₁ >>= k) >>= l) ((d₂ >>= k) >>= l))
    (mix-comm p (d₁ >>= (λ a → k a >>= l)) (d₂ >>= (λ a → k a >>= l)))
    i
>>=-assoc (mix-bdy0 d₁ d₂ i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix w0) (>>=-assoc d₁ k l) (>>=-assoc d₂ k l))
    (>>=-assoc d₂ k l)
    (mix-bdy0 ((d₁ >>= k) >>= l) ((d₂ >>= k) >>= l))
    (mix-bdy0 (d₁ >>= (λ a → k a >>= l)) (d₂ >>= (λ a → k a >>= l)))
    i
>>=-assoc (mix-bdy1 d₁ d₂ i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix w1) (>>=-assoc d₁ k l) (>>=-assoc d₂ k l))
    (>>=-assoc d₁ k l)
    (mix-bdy1 ((d₁ >>= k) >>= l) ((d₂ >>= k) >>= l))
    (mix-bdy1 (d₁ >>= (λ a → k a >>= l)) (d₂ >>= (λ a → k a >>= l)))
    i
>>=-assoc (mix-assoc-pos p q ps a b c i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (>>=-assoc a k l)
                    (cong₂ (mix q) (>>=-assoc b k l) (>>=-assoc c k l)))
    (cong₂ (mix (s-of p q))
           (cong₂ (mix (r-of p q ps)) (>>=-assoc a k l) (>>=-assoc b k l))
           (>>=-assoc c k l))
    (mix-assoc-pos p q ps ((a >>= k) >>= l) ((b >>= k) >>= l) ((c >>= k) >>= l))
    (mix-assoc-pos p q ps (a >>= (λ x → k x >>= l)) (b >>= (λ x → k x >>= l))
                          (c >>= (λ x → k x >>= l)))
    i
>>=-assoc (mix-interchange p q a b c d i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p)
           (cong₂ (mix q) (>>=-assoc a k l) (>>=-assoc b k l))
           (cong₂ (mix q) (>>=-assoc c k l) (>>=-assoc d k l)))
    (cong₂ (mix q)
           (cong₂ (mix p) (>>=-assoc a k l) (>>=-assoc c k l))
           (cong₂ (mix p) (>>=-assoc b k l) (>>=-assoc d k l)))
    (mix-interchange p q ((a >>= k) >>= l) ((b >>= k) >>= l)
                         ((c >>= k) >>= l) ((d >>= k) >>= l))
    (mix-interchange p q (a >>= (λ x → k x >>= l)) (b >>= (λ x → k x >>= l))
                         (c >>= (λ x → k x >>= l)) (d >>= (λ x → k x >>= l)))
    i
>>=-assoc (mix-bayes-interchange p q₁ q₂ pM pM' a b c d i) k l =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p)
           (cong₂ (mix q₁) (>>=-assoc a k l) (>>=-assoc c k l))
           (cong₂ (mix q₂) (>>=-assoc b k l) (>>=-assoc d k l)))
    (cong₂ (mix (mix-w p q₁ q₂))
           (cong₂ (mix (bayesW p q₁ q₂ pM)) (>>=-assoc a k l) (>>=-assoc b k l))
           (cong₂ (mix (bayesW p (1-w q₁) (1-w q₂) pM')) (>>=-assoc c k l) (>>=-assoc d k l)))
    (mix-bayes-interchange p q₁ q₂ pM pM'
       ((a >>= k) >>= l) ((b >>= k) >>= l) ((c >>= k) >>= l) ((d >>= k) >>= l))
    (mix-bayes-interchange p q₁ q₂ pM pM'
       (a >>= (λ x → k x >>= l)) (b >>= (λ x → k x >>= l))
       (c >>= (λ x → k x >>= l)) (d >>= (λ x → k x >>= l)))
    i
>>=-assoc (trunc d₁ d₂ p q i j) k l =
  isSet→SquareP
    (λ i j → isOfHLevelSuc 1
      (trunc ((trunc d₁ d₂ p q i j >>= k) >>= l)
             (trunc d₁ d₂ p q i j >>= (λ a → k a >>= l))))
    (cong (λ d → >>=-assoc d k l) p)
    (cong (λ d → >>=-assoc d k l) q)
    refl
    refl
    i j

-- ============================================================
-- Section 2: constBind.
--
-- constBind d e ≡ e: binding d against a constant kernel
-- collapses to the constant value, regardless of d's structure.
-- This is the structural lemma underlying Rule 1 and Rule 3.
-- ============================================================

constBind : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
            (d : FDist A) (e : FDist B)
          → (d >>= λ _ → e) ≡ e
constBind (pure a) e = refl
constBind (mix p d₁ d₂) e =
  cong₂ (mix p) (constBind d₁ e) (constBind d₂ e) ∙ mix-idem p e
constBind (mix-idem p d i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (constBind d e) (constBind d e) ∙ mix-idem p e)
    (constBind d e)
    (mix-idem p (d >>= λ _ → e))
    refl
    i
constBind (mix-comm p d₁ d₂ i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (constBind d₁ e) (constBind d₂ e) ∙ mix-idem p e)
    (cong₂ (mix (1-w p)) (constBind d₂ e) (constBind d₁ e) ∙ mix-idem (1-w p) e)
    (mix-comm p (d₁ >>= λ _ → e) (d₂ >>= λ _ → e))
    refl
    i
constBind (mix-bdy0 d₁ d₂ i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix w0) (constBind d₁ e) (constBind d₂ e) ∙ mix-idem w0 e)
    (constBind d₂ e)
    (mix-bdy0 (d₁ >>= λ _ → e) (d₂ >>= λ _ → e))
    refl
    i
constBind (mix-bdy1 d₁ d₂ i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix w1) (constBind d₁ e) (constBind d₂ e) ∙ mix-idem w1 e)
    (constBind d₁ e)
    (mix-bdy1 (d₁ >>= λ _ → e) (d₂ >>= λ _ → e))
    refl
    i
constBind (mix-assoc-pos p q ps a b c i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p) (constBind a e)
                    (cong₂ (mix q) (constBind b e) (constBind c e) ∙ mix-idem q e)
     ∙ mix-idem p e)
    (cong₂ (mix (s-of p q))
           (cong₂ (mix (r-of p q ps)) (constBind a e) (constBind b e) ∙ mix-idem (r-of p q ps) e)
           (constBind c e)
     ∙ mix-idem (s-of p q) e)
    (mix-assoc-pos p q ps (a >>= λ _ → e) (b >>= λ _ → e) (c >>= λ _ → e))
    refl
    i
constBind (mix-interchange p q a b c d i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p)
           (cong₂ (mix q) (constBind a e) (constBind b e) ∙ mix-idem q e)
           (cong₂ (mix q) (constBind c e) (constBind d e) ∙ mix-idem q e)
     ∙ mix-idem p e)
    (cong₂ (mix q)
           (cong₂ (mix p) (constBind a e) (constBind c e) ∙ mix-idem p e)
           (cong₂ (mix p) (constBind b e) (constBind d e) ∙ mix-idem p e)
     ∙ mix-idem q e)
    (mix-interchange p q (a >>= λ _ → e) (b >>= λ _ → e)
                         (c >>= λ _ → e) (d >>= λ _ → e))
    refl
    i
constBind (mix-bayes-interchange p q₁ q₂ pM pM' a b c d i) e =
  isSet→SquareP (λ _ _ → trunc)
    (cong₂ (mix p)
           (cong₂ (mix q₁) (constBind a e) (constBind c e) ∙ mix-idem q₁ e)
           (cong₂ (mix q₂) (constBind b e) (constBind d e) ∙ mix-idem q₂ e)
     ∙ mix-idem p e)
    (cong₂ (mix (mix-w p q₁ q₂))
           (cong₂ (mix (bayesW p q₁ q₂ pM)) (constBind a e) (constBind b e) ∙ mix-idem (bayesW p q₁ q₂ pM) e)
           (cong₂ (mix (bayesW p (1-w q₁) (1-w q₂) pM')) (constBind c e) (constBind d e) ∙ mix-idem (bayesW p (1-w q₁) (1-w q₂) pM') e)
     ∙ mix-idem (mix-w p q₁ q₂) e)
    (mix-bayes-interchange p q₁ q₂ pM pM'
       (a >>= λ _ → e) (b >>= λ _ → e) (c >>= λ _ → e) (d >>= λ _ → e))
    refl
    i
constBind (trunc d₁ d₂ p q i j) e =
  isSet→SquareP
    (λ i j → isOfHLevelSuc 1
      (trunc (trunc d₁ d₂ p q i j >>= λ _ → e) e))
    (cong (λ d → constBind d e) p)
    (cong (λ d → constBind d e) q)
    refl
    refl
    i j

-- ============================================================
-- Section 3: Pair-projection helpers.
-- ============================================================

mapF-snd-pair : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
              → (x : X) (d : FDist Y)
              → mapF snd (mapF (x ,_) d) ≡ d
mapF-snd-pair {X = X} {Y = Y} x d =
  >>=-assoc d (λ y → pure (x , y)) (λ p → pure (snd p))
  ∙ >>=-unitR d

mapF-fst-pair : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
              → (x : X) (d : FDist Y)
              → mapF fst (mapF (x ,_) d) ≡ (d >>= λ _ → pure x)
mapF-fst-pair {X = X} {Y = Y} x d =
  >>=-assoc d (λ y → pure (x , y)) (λ p → pure (fst p))

-- ============================================================
-- Section 4: SCM₂ and Rule 1.
-- ============================================================

record SCM₂ {ℓ ℓ'} (X : Type ℓ) (Y : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    pX : FDist X
    kY : X → FDist Y

open SCM₂

joint-of : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → SCM₂ X Y → FDist (X × Y)
joint-of m = pX m >>= λ x → mapF (x ,_) (kY m x)

do-X : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → X → SCM₂ X Y → SCM₂ X Y
do-X x₀ m = record m { pX = pure x₀ }

record Y-indep-X {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (m : SCM₂ X Y)
       : Type (ℓ-max ℓ ℓ') where
  field
    k₀ : FDist Y
    const-witness : (x : X) → kY m x ≡ k₀

open Y-indep-X

marginal-Y-fuse : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} (m : SCM₂ X Y)
  → mapF snd (joint-of m) ≡ (pX m >>= kY m)
marginal-Y-fuse {X = X} {Y = Y} m =
  >>=-assoc (pX m)
    (λ x → mapF (x ,_) (kY m x))
    (λ p → pure (snd p))
  ∙ cong (pX m >>=_) (funExt λ x → mapF-snd-pair x (kY m x))

-- Pearl's Rule 1 for SCM₂: structural independence of Y from X
-- implies do-X-invariance of the Y-marginal.
rule1-marginal : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'}
  (m : SCM₂ X Y) (ind : Y-indep-X m) (x₀ : X)
  → mapF snd (joint-of (do-X x₀ m)) ≡ mapF snd (joint-of m)
rule1-marginal m ind x₀ =
    mapF-snd-pair x₀ (kY m x₀)
    ∙ const-witness ind x₀
    ∙ sym
        (marginal-Y-fuse m
        ∙ cong (pX m >>=_) (funExt (const-witness ind))
        ∙ constBind (pX m) (k₀ ind))

-- ============================================================
-- Section 5: SCM₃ chain X → Y → Z and Rule 1 (chain version).
-- ============================================================

record SCM₃ {ℓ ℓ' ℓ''} (X : Type ℓ) (Y : Type ℓ') (Z : Type ℓ'')
       : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    pX  : FDist X
    kY  : X → FDist Y
    kZ  : Y → FDist Z

open SCM₃

joint-of₃ : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
          → SCM₃ X Y Z → FDist (X × (Y × Z))
joint-of₃ m =
  pX m >>= λ x →
  kY m x >>= λ y →
  kZ m y >>= λ z →
  pure (x , (y , z))

do-X₃ : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
      → X → SCM₃ X Y Z → SCM₃ X Y Z
do-X₃ x₀ m = record m { pX = pure x₀ }

do-Z₃ : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
      → Z → SCM₃ X Y Z → SCM₃ X Y Z
do-Z₃ z₀ m = record m { kZ = λ _ → pure z₀ }

marginal-YZ : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
            → SCM₃ X Y Z → FDist (Y × Z)
marginal-YZ m = mapF snd (joint-of₃ m)

marginal-X : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
           → SCM₃ X Y Z → FDist X
marginal-X m = mapF fst (joint-of₃ m)

marginal-XY : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
            → SCM₃ X Y Z → FDist (X × Y)
marginal-XY m = mapF (λ p → (fst p , fst (snd p))) (joint-of₃ m)

record Y-indep-X₃ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
       (m : SCM₃ X Y Z) : Type (ℓ-max ℓ ℓ') where
  field
    kY₀         : FDist Y
    kY-const    : (x : X) → kY m x ≡ kY₀

open Y-indep-X₃

-- Helper: marginal-YZ fuses to drop the X coordinate.
marginal-YZ-fuse : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → (m : SCM₃ X Y Z)
  → marginal-YZ m
    ≡ (pX m >>= λ x →
       kY m x >>= λ y →
       mapF (y ,_) (kZ m y))
marginal-YZ-fuse {X = X} {Y = Y} {Z = Z} m =
  >>=-assoc (pX m)
    (λ x → kY m x >>= λ y → kZ m y >>= λ z → pure (x , (y , z)))
    (λ p → pure (snd p))
  ∙ cong (pX m >>=_) (funExt λ x →
      >>=-assoc (kY m x)
        (λ y → kZ m y >>= λ z → pure (x , (y , z)))
        (λ p → pure (snd p))
      ∙ cong (kY m x >>=_) (funExt λ y →
          >>=-assoc (kZ m y)
            (λ z → pure (x , (y , z)))
            (λ p → pure (snd p))))

-- Pearl's Rule 1 for the chain: structural independence of Y
-- from X implies do-X-invariance of the (Y, Z) marginal.
rule1-chain : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  (m : SCM₃ X Y Z) (ind : Y-indep-X₃ m) (x₀ : X)
  → marginal-YZ (do-X₃ x₀ m) ≡ marginal-YZ m
rule1-chain m ind x₀ =
    marginal-YZ-fuse (do-X₃ x₀ m)
    ∙ cong (λ d → d >>= λ y → mapF (y ,_) (kZ m y))
           (kY-const ind x₀)
    ∙ sym
        (marginal-YZ-fuse m
        ∙ cong (pX m >>=_) (funExt λ x →
            cong (λ d → d >>= λ y → mapF (y ,_) (kZ m y))
                 (kY-const ind x))
        ∙ constBind (pX m)
            (kY₀ ind >>= λ y → mapF (y ,_) (kZ m y)))

-- ============================================================
-- Section 6: Rule 3 (insertion/deletion of actions).
--
-- Rule 3 in kernel form: intervening on a downstream variable
-- leaves an upstream marginal unchanged. The structural reason
-- is that the upstream marginal does not bind kZ in its
-- definition, so substituting kZ with `λ _ → pure z₀` cannot
-- affect the result.
-- ============================================================

-- Helper: marginal-X fuses, dropping kY and kZ entirely.
-- The proof: marginal-X is mapF fst applied to the joint, and
-- by associativity this peels through the binds, producing
-- pX >>= kY >>= kZ >>= λ _ → pure x_outer; the inner pure-x
-- is constant in z, so constBind collapses the kZ-bind and
-- then constBind again collapses the kY-bind, leaving pX.
marginal-X-fuse : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → (m : SCM₃ X Y Z)
  → marginal-X m ≡ pX m
marginal-X-fuse {X = X} {Y = Y} {Z = Z} m =
    -- Step 1: peel off the outer mapF fst into the outer bind.
    >>=-assoc (pX m)
      (λ x → kY m x >>= λ y → kZ m y >>= λ z → pure (x , (y , z)))
      (λ p → pure (fst p))
    -- ≡ pX m >>= λ x → (kY m x >>= λ y → kZ m y >>= λ z → pure (x,(y,z))) >>= λ p → pure (fst p)
    ∙ cong (pX m >>=_) (funExt λ x →
        -- Step 2: peel through the kY-bind.
        >>=-assoc (kY m x)
          (λ y → kZ m y >>= λ z → pure (x , (y , z)))
          (λ p → pure (fst p))
        -- ≡ kY m x >>= λ y → (kZ m y >>= λ z → pure (x,(y,z))) >>= λ p → pure (fst p)
        ∙ cong (kY m x >>=_) (funExt λ y →
            -- Step 3: peel through the kZ-bind.
            >>=-assoc (kZ m y)
              (λ z → pure (x , (y , z)))
              (λ p → pure (fst p))
            -- Now the innermost body is: pure (x , (y , z)) >>= λ p → pure (fst p)
            -- which reduces by >>=-unitL to pure (fst (x , (y , z))) = pure x.
            -- So inner ≡ kZ m y >>= λ _ → pure x.
            ∙ constBind (kZ m y) (pure x))
        -- ≡ kY m x >>= λ _ → pure x  (by inner = constBind)
        ∙ constBind (kY m x) (pure x))
    -- ≡ pX m >>= λ x → pure x  (by outer = constBind on each fiber)
    ∙ >>=-unitR (pX m)

-- Pearl's Rule 3 for the chain: any intervention on Z
-- leaves the X-marginal unchanged.
-- The proof: both sides reduce to pX m via marginal-X-fuse,
-- which holds for every kZ (including pure z₀).
rule3-X-marginal : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  (m : SCM₃ X Y Z) (z₀ : Z)
  → marginal-X (do-Z₃ z₀ m) ≡ marginal-X m
rule3-X-marginal m z₀ =
    marginal-X-fuse (do-Z₃ z₀ m)
    ∙ sym (marginal-X-fuse m)

-- ============================================================
-- Rule 3 strengthened: any intervention on Z leaves the
-- (X, Y) joint marginal unchanged.
--
-- Same structural reason: the (X, Y) marginal does not bind
-- kZ in a way that affects the output, so substitution of kZ
-- is invisible to the marginal.
-- ============================================================

-- Helper: marginal-XY fuses to a chain that drops kZ.
marginal-XY-fuse : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → (m : SCM₃ X Y Z)
  → marginal-XY m
    ≡ (pX m >>= λ x →
       kY m x >>= λ y →
       kZ m y >>= λ _ → pure (x , y))
marginal-XY-fuse {X = X} {Y = Y} {Z = Z} m =
    >>=-assoc (pX m)
      (λ x → kY m x >>= λ y → kZ m y >>= λ z → pure (x , (y , z)))
      (λ p → pure (fst p , fst (snd p)))
    ∙ cong (pX m >>=_) (funExt λ x →
        >>=-assoc (kY m x)
          (λ y → kZ m y >>= λ z → pure (x , (y , z)))
          (λ p → pure (fst p , fst (snd p)))
        ∙ cong (kY m x >>=_) (funExt λ y →
            >>=-assoc (kZ m y)
              (λ z → pure (x , (y , z)))
              (λ p → pure (fst p , fst (snd p)))))

-- The (X, Y) marginal further reduces by collapsing the kZ-bind
-- via constBind, since the body pure (x , y) does not depend on z.
marginal-XY-collapse : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → (m : SCM₃ X Y Z)
  → marginal-XY m
    ≡ (pX m >>= λ x → mapF (x ,_) (kY m x))
marginal-XY-collapse {X = X} {Y = Y} {Z = Z} m =
    marginal-XY-fuse m
    ∙ cong (pX m >>=_) (funExt λ x →
        cong (kY m x >>=_) (funExt λ y →
          constBind (kZ m y) (pure (x , y))))

-- Pearl's Rule 3 for (X, Y): any intervention on Z leaves the
-- (X, Y) marginal unchanged. The collapsed form is independent
-- of kZ.
rule3-XY-marginal : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  (m : SCM₃ X Y Z) (z₀ : Z)
  → marginal-XY (do-Z₃ z₀ m) ≡ marginal-XY m
rule3-XY-marginal m z₀ =
    marginal-XY-collapse (do-Z₃ z₀ m)
    ∙ sym (marginal-XY-collapse m)

-- ============================================================
-- Honest framing notes
--
-- These theorems are "Pearl's do-calculus in kernel form" on
-- small fixed structural causal models, paralleling the original
-- Rule 1 verification in this paper. They are not the full
-- general do-calculus, which would require defining DAGs as
-- types in cubical Agda, defining d-separation on graphs, and
-- the graph-mutilation operations the rules' classical
-- statements reference; that is a separate development of
-- substantially larger scope.
--
-- The Rule 3 proofs above do not require any new postulates
-- beyond what FDist-Convex provides. They follow the same
-- pattern as Rule 1: derive the marginal-fuse lemma, then
-- collapse via constBind. The key structural feature being
-- exploited is that interventions on a variable that the
-- marginal in question does not depend on cannot affect
-- that marginal — exactly what Rule 3 in the classical
-- statement asserts under the appropriate graph-theoretic
-- side condition.
-- ============================================================
