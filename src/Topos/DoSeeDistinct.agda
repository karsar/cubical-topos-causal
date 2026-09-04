{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.DoSeeDistinct — intervening differs from conditioning.
--
-- DoClassifier gave χ : X ⇒ Ω, the characteristic map of the
-- value-fixing subobject {x₀} ↪ X.  At the level of Ω the event
-- {X = x₀} is the same object under intervention, do(X := x₀) by
-- graph surgery, and under observation, conditioning on X = x₀.
-- So χ does not separate the two.  The causal content of the
-- do-operator has to be a theorem about the kernels.  This
-- module proves that theorem, and χ names its subject inside Ω.
--
-- The model is a confounder  U → X , U → Y.  Here U is a common
-- cause and there is no direct X → Y edge.  The do-operator is
-- graph surgery: do(X := x₀) severs U → X and pins X to x₀, and
-- leaves U and the Y-mechanism untouched.  On a perfectly
-- correlating confounder the module proves:
--
--     P(Y = ⊤ ∣ do(X := ⊤))  =  p            (the prior on the common cause)
--     P(Y = ⊤ ∣      X = ⊤)  =  1            (observing X reveals U)
--
-- These differ for every interior strength p ≠ 1.  The interior
-- weight ½ (WeightQ.wHalf) inhabits the hypotheses, so the
-- theorem is not vacuous.  The observational conditional is the
-- Bayes ratio P(X=⊤,Y=⊤) / P(X=⊤), formed with the development's
-- own partial division.  That ratio is the definition of
-- conditional probability.
-- ============================================================

module Topos.DoSeeDistinct where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)

open import FDist-Convex
open import WeightQ
open import RuleDoCalc using (constBind; >>=-assoc; mapF-snd-pair)

-- ============================================================
-- The confounded model and its do-operator (model surgery).
-- ============================================================

record Confounded {ℓu ℓx ℓy} (U : Type ℓu) (X : Type ℓx) (Y : Type ℓy)
       : Type (ℓ-max ℓu (ℓ-max ℓx ℓy)) where
  field
    pU : FDist U
    kX : U → FDist X
    kY : U → FDist Y     -- Y depends on U and not on X: a confounder

open Confounded

module _ {ℓu ℓx ℓy} {U : Type ℓu} {X : Type ℓx} {Y : Type ℓy} where

  -- the observational joint P(X, Y)
  obs-joint : Confounded U X Y → FDist (X × Y)
  obs-joint m = pU m >>= λ u → kX m u >>= λ x → mapF (x ,_) (kY m u)

  -- do(X := x₀) severs U → X and fixes X to x₀.  U and kY are
  -- untouched.
  do-joint : X → Confounded U X Y → FDist (X × Y)
  do-joint x₀ m = pU m >>= λ u → mapF (x₀ ,_) (kY m u)

  -- The interventional Y-marginal.  It does not mention x₀.  Under
  -- the surgery Y is independent of the value forced on X, because
  -- there is no X → Y edge.  Observation has no such invariance.
  do-Y-marginal : X → Confounded U X Y → FDist Y
  do-Y-marginal x₀ m = pU m >>= kY m

  do-Y-marginal-invariant : (x₀ x₁ : X) (m : Confounded U X Y)
    → do-Y-marginal x₀ m ≡ do-Y-marginal x₁ m
  do-Y-marginal-invariant x₀ x₁ m = refl

  -- do-Y-marginal is the Y-marginal of the intervened joint.  By
  -- the monad laws, mapF snd of do-joint reduces to pU >>= kY.
  do-Y-marginal-is-joint : (x₀ : X) (m : Confounded U X Y)
    → mapF snd (do-joint x₀ m) ≡ do-Y-marginal x₀ m
  do-Y-marginal-is-joint x₀ m =
      >>=-assoc (pU m) (λ u → mapF (x₀ ,_) (kY m u)) (λ a → pure (snd a))
    ∙ cong (pU m >>=_) (funExt λ u → mapF-snd-pair x₀ (kY m u))

  -- So the Y-marginal of the intervened joint does not depend on
  -- x₀.  The invariance is now stated of the joint's marginal, and
  -- no longer of a standalone definition.
  do-joint-Y-invariant : (x₀ x₁ : X) (m : Confounded U X Y)
    → mapF snd (do-joint x₀ m) ≡ mapF snd (do-joint x₁ m)
  do-joint-Y-invariant x₀ x₁ m =
      do-Y-marginal-is-joint x₀ m
    ∙ do-Y-marginal-invariant x₀ x₁ m
    ∙ sym (do-Y-marginal-is-joint x₁ m)

  -- Bridge to the classifier.  Under do(X := x₀) the X-marginal is
  -- the point mass at x₀, which is the value that DoClassifier's χ
  -- classifies as ⊤.  So χ is the Ω-name of what the surgery
  -- forces.
  do-fixes-X : (x₀ : X) (m : Confounded U X Y)
    → mapF fst (do-joint x₀ m) ≡ pure x₀
  do-fixes-X x₀ m =
      >>=-assoc (pU m) (λ u → mapF (x₀ ,_) (kY m u)) (λ a → pure (fst a))
    ∙ cong (pU m >>=_) (funExt λ u →
          >>=-assoc (kY m u) (λ y → pure (x₀ , y)) (λ a → pure (fst a))
        ∙ constBind (kY m u) (pure x₀))
    ∙ constBind (pU m) (pure x₀)

-- ============================================================
-- Event indicators.  The probability of an event is the
-- expectation 𝔼 of its {0,1}-valued indicator.
-- ============================================================

ind11 : Bool × Bool → Weight        -- indicator of {X = ⊤ ∧ Y = ⊤}
ind11 (true , true) = w1
ind11 (true , false) = w0
ind11 (false , _)    = w0

indXtrue : Bool × Bool → Weight      -- indicator of {X = ⊤}
indXtrue (true  , _) = w1
indXtrue (false , _) = w0

indYtrue : Bool × Bool → Weight      -- indicator of {Y = ⊤}
indYtrue (_ , true)  = w1
indYtrue (_ , false) = w0

-- ============================================================
-- The perfectly correlating binary confounder, for an interior
-- prior p on the common cause, so 0 < p < 1.  Here U ~ (p : ⊤),
-- X = U and Y = U.
-- ============================================================

module DoSee (p : Weight) (pp : Pos p) (p≢1 : ¬ (p ≡ w1)) where

  bc : Confounded Bool Bool Bool
  bc = record { pU = mix p (pure true) (pure false)
              ; kX = pure ; kY = pure }

  -- read-out of a two-point expectation:  mix-w p w1 w0 ≡ p
  readout : mix-w p w1 w0 ≡ p
  readout = mix-w-right-w0 p w1 ∙ *w-1 p

  -- P(X = ⊤, Y = ⊤) = p
  Pr-XY : 𝔼 (obs-joint bc) ind11 ≡ p
  Pr-XY = 𝔼-bind (mix p (pure true) (pure false))
                 (λ u → pure u >>= λ x → mapF (x ,_) (pure u)) ind11
        ∙ readout

  -- P(X = ⊤) = p
  Pr-X : 𝔼 (obs-joint bc) indXtrue ≡ p
  Pr-X = 𝔼-bind (mix p (pure true) (pure false))
                (λ u → pure u >>= λ x → mapF (x ,_) (pure u)) indXtrue
       ∙ readout

  -- P(Y = ⊤ ∣ do(X := ⊤)) = p   (the interventional marginal)
  Pr-Y-do : 𝔼 (do-joint true bc) indYtrue ≡ p
  Pr-Y-do = 𝔼-bind (mix p (pure true) (pure false))
                   (λ u → mapF (true ,_) (pure u)) indYtrue
          ∙ readout

  -- ----------------------------------------------------------
  -- The observational conditional P(Y = ⊤ ∣ X = ⊤) as the Bayes
  -- ratio  P(X=⊤,Y=⊤) / P(X=⊤).
  -- ----------------------------------------------------------

  N D : Weight
  N = 𝔼 (obs-joint bc) ind11
  D = 𝔼 (obs-joint bc) indXtrue

  posD : Pos D
  posD = subst Pos (sym Pr-X) pp

  valN≡valD : val N ≡ val D
  valN≡valD = cong val (Pr-XY ∙ sym Pr-X)

  leND : val N ≤r val D
  leND = subst (λ w → val N ≤r w) valN≡valD (≤r-refl (val N))

  condProb : Weight
  condProb = N /wPf D ⟨ posD , leND ⟩

  -- Observing X = ⊤ forces Y = ⊤, so the conditional is 1.
  condProb≡w1 : condProb ≡ w1
  condProb≡w1 = WeightPath
    ( cong (_/r val D) valN≡valD
    ∙ cong (_/r val D) (sym (·r-IdL (val D)))
    ∙ ·r-/r-pos posD z1 )

  -- ----------------------------------------------------------
  -- The theorem.  Intervening differs from observing.  The do-side
  -- value is the prior p, the observational value is 1, and p ≠ 1.
  -- ----------------------------------------------------------

  do≢see : ¬ (𝔼 (do-joint true bc) indYtrue ≡ condProb)
  do≢see e = p≢1 (sym Pr-Y-do ∙ e ∙ condProb≡w1)

-- ============================================================
-- Non-vacuity.  The interior strength ½ inhabits the hypotheses,
-- so a confounded model with do ≠ see exists.
-- ============================================================

module Half = DoSee wHalf Pos-wHalf wHalf≢w1

do≢see-half : ¬ (𝔼 (do-joint true Half.bc) indYtrue ≡ Half.condProb)
do≢see-half = Half.do≢see
