{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Rule2.agda
--
-- Pearl's Rule 2 of do-calculus (action/observation exchange)
-- in kernel form, on a confounded 3-variable structural causal
-- model.  It is built on FDist-Convex.  The proofs use the
-- monad laws and one structural CI witness.
--
-- The model:
--   pXZ : FDist (X × Z)   -- joint prior; X and Z may be correlated
--   kY  : X → Z → FDist Y -- Y depends on (X, Z)
--
-- The intervention `do-X-conf x₀` removes the structure that
-- feeds into X.  It replaces pXZ with
-- `mapF (x₀ ,_) (mapF snd pXZ)`.  X is then fixed at x₀, and Z
-- keeps its marginal distribution.
--
-- The structural CI hypothesis `X-indep-Z m` records that pXZ
-- factors as `pX ⊗D pZ`, for some (pX : FDist X) and
-- (pZ : FDist Z).  Under this hypothesis the structural
-- conditional of Z given X = x₀ equals pZ, because independence
-- makes the conditional equal to the marginal.  So the
-- conditioning operation `cond-X-conf` gives the same
-- (Z, Y)-joint as `do-X-conf`.  That equality is Pearl's Rule 2
-- in kernel form.
--
-- The HIT-level conditioning operator below takes its
-- conditional kernel from the structural CI witness.  Under
-- independence the pZ-marginal field of the witness is the
-- conditional given X = x₀.  For finite types one could instead
-- build a genuine partial-conditioning operator from the
-- representation theorem of Representation-Convex.agda, and
-- recover the structural form as a corollary.  This module
-- proves only the structural form.
-- ============================================================

module Rule2 where

open import Cubical.Core.Primitives
open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Function using (_∘_)

open import FDist-Convex
open import RuleDoCalc using
  ( >>=-unitR ; >>=-assoc ; constBind
  ; mapF-snd-pair ; mapF-fst-pair )

-- Independent product (coupling) of two distributions, defined locally.
_⊗D_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
     → FDist A → FDist B → FDist (A × B)
da ⊗D db = da >>= λ a → mapF (a ,_) db
infixl 6 _⊗D_

-- ============================================================
-- Section 1: SCM-conf — the confounded 3-variable SCM.
-- ============================================================

record SCM-conf {ℓX ℓZ ℓY} (X : Type ℓX) (Z : Type ℓZ) (Y : Type ℓY)
       : Type (ℓ-max ℓX (ℓ-max ℓZ ℓY)) where
  field
    pXZ : FDist (X × Z)
    kY  : X → Z → FDist Y

open SCM-conf public

-- The joint distribution on (X × (Z × Y)).
-- We bind through pXZ first.  Then we sample Y from kY x z and
-- package the result as (x , (z , y)).
joint-of-conf : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
              → SCM-conf X Z Y → FDist (X × (Z × Y))
joint-of-conf m =
  pXZ m >>= λ p →
    mapF (λ y → (fst p , snd p , y)) (kY m (fst p) (snd p))

-- Marginals of the joint.
marginal-XZ : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
            → SCM-conf X Z Y → FDist (X × Z)
marginal-XZ m = mapF (λ p → (fst p , fst (snd p))) (joint-of-conf m)

marginal-Z : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
           → SCM-conf X Z Y → FDist Z
marginal-Z m = mapF (λ p → fst (snd p)) (joint-of-conf m)

marginal-Y : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
           → SCM-conf X Z Y → FDist Y
marginal-Y m = mapF (λ p → snd (snd p)) (joint-of-conf m)

marginal-ZY : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
            → SCM-conf X Z Y → FDist (Z × Y)
marginal-ZY m = mapF snd (joint-of-conf m)

-- ============================================================
-- Section 2: do-X-conf — kernel-substitution intervention.
--
-- do-X-conf x₀ removes the structure that feeds into X.  It
-- replaces the joint prior pXZ with one that fixes X = x₀ and
-- keeps the marginal distribution of Z:
--   new-pXZ = mapF (x₀ ,_) (mapF snd pXZ).
-- The kernel kY does not change.  The intervention acts on the
-- prior only.
-- ============================================================

-- The marginal Z-distribution implied by pXZ.
pZ-of : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
      → SCM-conf X Z Y → FDist Z
pZ-of m = mapF snd (pXZ m)

do-X-conf : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
          → X → SCM-conf X Z Y → SCM-conf X Z Y
do-X-conf x₀ m = record m { pXZ = mapF (x₀ ,_) (pZ-of m) }

-- ============================================================
-- Section 3: Structural CI witness — X ⊥⊥ Z in the prior.
--
-- The Rule 2 hypothesis: pXZ factors as a product of marginals
-- pX ⊗D pZ.  This is the kernel-form analogue of the classical
-- CI condition in Pearl's modified graph G_underline-X, the
-- graph with arrows out of X removed.  In this 3-variable
-- setting X is the treatment and Z is the confounder.  X ⊥⊥ Z in
-- the prior pXZ is then the condition under which intervention
-- and conditioning agree.
--
-- The witness is a structural Σ-type that records the
-- factorization.  It has the shape of the intersection-axiom
-- hypotheses in Section 4 of the paper (DoesNotDependOnY,
-- DoesNotDependOnW).
-- ============================================================

record X-indep-Z {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
       (m : SCM-conf X Z Y) : Type (ℓ-max ℓX (ℓ-max ℓZ ℓY)) where
  field
    pX-marg : FDist X
    pZ-marg : FDist Z
    factors : pXZ m ≡ (pX-marg ⊗D pZ-marg)

open X-indep-Z public

-- ============================================================
-- Section 4: cond-X-conf — HIT-level conditioning on X = x₀.
--
-- Given the structural CI witness, the conditional distribution
-- of Z given X = x₀ is the pZ-marg field of the witness.  Under
-- independence the conditional equals the marginal.  So we
-- define conditioning as kernel substitution with this
-- structural conditional:
--
--   cond-X-conf x₀ m ind = record m
--     { pXZ = mapF (x₀ ,_) (pZ-marg ind) }
--
-- The result is an SCM whose joint is the post-conditioning
-- distribution.  The operation works at the HIT level.  It sends
-- the FDist-valued joint pXZ m to a new FDist-valued joint,
-- through the structural CI witness.
--
-- The operation is defined for any SCM that carries an
-- X-indep-Z witness.  The witness connects intervention
-- semantics (kernel substitution) with conditioning semantics
-- (Bayesian update).  On a positive joint where X and Z are
-- correlated, one would obtain the same witness from bayes-cond
-- applied to the syntactic representation of pXZ.  The
-- structural form used here avoids the full-support requirement
-- of bayes-cond and works directly at the HIT level.
-- ============================================================

cond-X-conf : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
            → (x₀ : X) → (m : SCM-conf X Z Y) → X-indep-Z m
            → SCM-conf X Z Y
cond-X-conf x₀ m ind =
  record m { pXZ = mapF (x₀ ,_) (pZ-marg ind) }

-- ============================================================
-- Section 5: Agreement of intervention with conditioning.
--
-- The fusion lemma: under the structural CI witness, the
-- marginal Z of pXZ equals the pZ-marg field of the witness.
-- Independence is used at this step.  It gives that the
-- Z-marginal of pXZ agrees with the Z-marginal of the
-- factorized form, for every X-value one might condition on.
-- ============================================================

-- mapF snd of a product (pX ⊗D pZ) is pZ.  This is one
-- direction of the standard product-marginal lemma.
mapF-snd-⊗D : ∀ {ℓX ℓZ} {X : Type ℓX} {Z : Type ℓZ}
            → (pX : FDist X) (pZ : FDist Z)
            → mapF snd (pX ⊗D pZ) ≡ (pX >>= λ _ → pZ)
mapF-snd-⊗D pX pZ =
  -- mapF snd (pX >>= λ x → mapF (x ,_) pZ)
  -- = pX >>= λ x → mapF snd (mapF (x ,_) pZ)   [>>=-assoc + cong]
  -- = pX >>= λ x → pZ                          [mapF-snd-pair]
  >>=-assoc pX (λ x → mapF (x ,_) pZ) (λ p → pure (snd p))
  ∙ cong (pX >>=_) (funExt λ x → mapF-snd-pair x pZ)

-- Under X-indep-Z, the marginal Z of m equals the pZ-marg field
-- of the witness.
pZ-of-from-witness : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
                   → (m : SCM-conf X Z Y) (ind : X-indep-Z m)
                   → pZ-of m ≡ (pX-marg ind >>= λ _ → pZ-marg ind)
pZ-of-from-witness m ind =
  cong (mapF snd) (factors ind)
  ∙ mapF-snd-⊗D (pX-marg ind) (pZ-marg ind)

-- Under X-indep-Z, pZ-of m ≡ pZ-marg ind, once the constBind on
-- pX-marg collapses.
pZ-of-≡-pZ-marg : ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
                → (m : SCM-conf X Z Y) (ind : X-indep-Z m)
                → pZ-of m ≡ pZ-marg ind
pZ-of-≡-pZ-marg m ind =
  pZ-of-from-witness m ind ∙ constBind (pX-marg ind) (pZ-marg ind)

-- ============================================================
-- A fusion lemma for the joint of a do-X-conf-style SCM.
-- Let m' be an SCM with pXZ m' = mapF (x₀ ,_) q, for some
-- q : FDist Z.  The joint then reduces to
--   q >>= λ z → mapF (x₀ , z ,_) (kY m' x₀ z),
-- so q and kY at x₀ determine the joint.
-- ============================================================

joint-of-fixed-X-fuse :
  ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
  → (m : SCM-conf X Z Y) → (x₀ : X) → (q : FDist Z)
  → pXZ m ≡ mapF (x₀ ,_) q
  → joint-of-conf m
  ≡ (q >>= λ z → mapF (λ y → (x₀ , z , y)) (kY m x₀ z))
joint-of-fixed-X-fuse m x₀ q eq =
  cong (λ d → d >>= λ p → mapF (λ y → (fst p , snd p , y))
                                 (kY m (fst p) (snd p))) eq
  ∙ >>=-assoc q (λ z → pure (x₀ , z))
                (λ p → mapF (λ y → (fst p , snd p , y))
                              (kY m (fst p) (snd p)))

-- ============================================================
-- The main agreement theorem.
--
-- Under X-indep-Z, the joint of (do-X-conf x₀ m) equals the
-- joint of (cond-X-conf x₀ m ind).  Each side has pXZ of the
-- shape mapF (x₀ ,_) q.  On the do side q is pZ-of m, and on the
-- cond side q is pZ-marg ind.  The CI witness equates the two.
-- ============================================================

joint-do-≡-joint-cond :
  ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
  → (m : SCM-conf X Z Y) (ind : X-indep-Z m) (x₀ : X)
  → joint-of-conf (do-X-conf x₀ m) ≡ joint-of-conf (cond-X-conf x₀ m ind)
joint-do-≡-joint-cond m ind x₀ =
    joint-of-fixed-X-fuse (do-X-conf x₀ m) x₀ (pZ-of m) refl
  ∙ cong (λ q → q >>= λ z → mapF (λ y → (x₀ , z , y)) (kY m x₀ z))
         (pZ-of-≡-pZ-marg m ind)
  ∙ sym (joint-of-fixed-X-fuse (cond-X-conf x₀ m ind) x₀ (pZ-marg ind) refl)

-- ============================================================
-- Section 6: Rule 2 in kernel form.
--
-- Action/observation exchange: under the structural CI
-- hypothesis X-indep-Z, intervening on X (do-X-conf x₀) gives
-- the same (Z, Y)-marginal as conditioning on X (cond-X-conf
-- x₀).  This is Pearl's Rule 2 in kernel form.
--
-- The (Z, Y)-marginal version and the Y-marginal version both
-- follow from joint-do-≡-joint-cond.
-- ============================================================

rule2-marginal-ZY :
  ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
  → (m : SCM-conf X Z Y) (ind : X-indep-Z m) (x₀ : X)
  → marginal-ZY (do-X-conf x₀ m) ≡ marginal-ZY (cond-X-conf x₀ m ind)
rule2-marginal-ZY m ind x₀ =
  cong (mapF snd) (joint-do-≡-joint-cond m ind x₀)

rule2-marginal-Y :
  ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
  → (m : SCM-conf X Z Y) (ind : X-indep-Z m) (x₀ : X)
  → marginal-Y (do-X-conf x₀ m) ≡ marginal-Y (cond-X-conf x₀ m ind)
rule2-marginal-Y m ind x₀ =
  cong (mapF (λ p → snd (snd p))) (joint-do-≡-joint-cond m ind x₀)

-- ============================================================
-- Section 7: Reductions of both sides.
--
-- Under the CI witness, the do-X-conf marginal and the
-- cond-X-conf marginal both reduce to a kernel-form posterior.
-- That posterior integrates kY x₀ against the marginal pZ.  The
-- lemma below records this algebra.  No result above uses it.
-- ============================================================

-- The reduced form of the (Z, Y)-marginal, for either
-- operation:
--   pZ >>= λ z → mapF (z ,_) (kY m x₀ z)
-- where pZ = pZ-marg ind, which equals pZ-of m by independence.
rule2-RHS-form :
  ∀ {ℓX ℓZ ℓY} {X : Type ℓX} {Z : Type ℓZ} {Y : Type ℓY}
  → (m : SCM-conf X Z Y) (ind : X-indep-Z m) (x₀ : X)
  → marginal-ZY (cond-X-conf x₀ m ind)
  ≡ (pZ-marg ind >>= λ z → mapF (z ,_) (kY m x₀ z))
rule2-RHS-form m ind x₀ =
    cong (mapF snd)
         (joint-of-fixed-X-fuse (cond-X-conf x₀ m ind) x₀ (pZ-marg ind) refl)
  ∙ >>=-assoc (pZ-marg ind)
              (λ z → mapF (λ y → (x₀ , z , y)) (kY m x₀ z))
              (λ p → pure (snd p))
  ∙ cong (pZ-marg ind >>=_) (funExt (λ z → mapF-fuse-snd x₀ z (kY m x₀ z)))
  where
    -- mapF snd (mapF (λ y → (x₀ , z , y)) d) ≡ mapF (z ,_) d
    mapF-fuse-snd : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Z : Type ℓ'} {Y : Type ℓ''}
                  → (x₀ : X) (z : Z) (d : FDist Y)
                  → (mapF (λ y → (x₀ , z , y)) d >>= (λ p → pure (snd p)))
                  ≡ mapF (z ,_) d
    mapF-fuse-snd x₀ z d =
      >>=-assoc d (λ y → pure (x₀ , z , y)) (λ p → pure (snd p))
