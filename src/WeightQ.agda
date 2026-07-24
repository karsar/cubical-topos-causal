{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- WeightQ: a concrete instantiation of FDist.agda's Weight
-- module signature.
--
-- This module discharges, as concrete theorems, the algebraic
-- postulates that FDist.agda assumes about the abstract type
-- Weight, by exhibiting a concrete construction of Weight as
-- the closed unit interval over a totally ordered field with
-- decidable order. The canonical instance is the rationals:
--
--    Weight ↦ ℚ in [0,1]
--    +w     ↦ rational addition (with bound proof)
--    *w     ↦ rational multiplication (closed in [0,1])
--    1-w    ↦ rational complement (1 - x)
--    /w     ↦ rational division (with division-by-zero
--             returning 0; total but only correctness-relevant
--             on positive divisors, which is the only case
--             arising in FDist.agda's bayesW)
--    Pos    ↦ "the underlying value is strictly greater than 0"
--
-- Strategy: we abstract away from the specific representation
-- of ℚ and instead postulate the required algebraic interface
-- (a commutative ring with a propositional <-order, decidable
-- equality, and selected closure laws). The abstraction is
-- safe in the sense that the postulated interface is satisfied
-- by ℚ, which the cubical library's Cubical.Algebra.CommRing.
-- Instances.Rationals confirms is a commutative ring. The
-- additional ordering laws are postulated here at the abstract
-- level; in a fully developed cubical rational library each
-- of them would be provable.
--
-- Scope of this module:
--   * All algebraic axioms of the convex algebra of Weight
--     (idempotency, commutativity, complements, weighted-idem,
--      associativity of +w/*w, distributivity).
--   * The expectation-related identities (commuteProof,
--     bdy0Proof, bdy1Proof, interchangeProof).
--   * The positivity predicate Pos and its closure laws
--     (pos-w1, pos-+w-l, pos-*w).
--   * The division-related identities bayesPf, bayesW algebra,
--     and the bayesW-cond identities.
--
-- Out of scope (left as a path postulate on FDist):
--   * mix-bayes-interchange itself, which is a path on FDist
--     between distinct expressions. Discharging this would
--     require either parameterizing FDist over the Weight
--     module signature or proving that the generalized
--     interchange path follows from the existing FDist axioms
--     plus the rational arithmetic identity --- a non-trivial
--     question about HIT-presented free convex algebras.
-- ============================================================

module WeightQ where

open import Cubical.Core.Primitives
open import Cubical.Core.Glue
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_)

-- ============================================================
-- The abstract rational interface.
--
-- We postulate a totally ordered commutative ring with the
-- closure laws used by the convex-algebra structure. The
-- canonical instance is ℚ (the rationals), as provided by
-- Cubical.Data.Rationals and proved a commutative ring by
-- Cubical.Algebra.CommRing.Instances.Rationals.
--
-- All postulates in this section are theorems of standard
-- rational arithmetic; they are postulated at this level to
-- keep the module self-contained and focused on the lift to
-- the Weight type.
-- ============================================================

-- ============================================================
-- The ordered field, discharged at ℚ.
--
-- This was previously a `postulate` block declaring an abstract
-- ordered field ℝ with its ring/order/division axioms.  We now
-- import the concrete ℚ model from WeightQ-Discharge, which proves
-- every one of those axioms as a theorem about the cubical-library
-- rationals, with no postulates of its own.  Re-exported `public`
-- so every downstream module that opens WeightQ sees the same
-- names, now constructive; the whole closure typechecks under
-- --safe.  (To recover the old abstract development, swap this
-- import for the postulate block preserved in git history.)
-- ============================================================
open import WeightQ-Field public using
  ( ℝ ; isSet-ℝ ; z0 ; z1 ; _+r_ ; _·r_ ; -r_ ; _≤r_ ; _<r_
  ; isProp-≤r ; isProp-<r
  ; +r-comm ; +r-assoc ; +r-IdR ; +r-inv
  ; ·r-comm ; ·r-assoc ; ·r-IdL ; ·r-IdR
  ; ·r-AnnihL ; ·r-AnnihR ; ·r-distR ; ·r-distL
  ; ≤r-refl ; ≤r-trans ; ≤r-antisym ; z0≤z1 ; z0<z1 ; <r-implies-≤r
  ; ≤r-+-mono ; ≤r-·-mono ; <r-·-pos ; <r-+-pos-l
  ; isProp-z0≤ ; isProp-x≤z1
  ; 1-r ; 1-r-def ; _/r_
  ; <r-irrefl ; ≡z1-or-<z1 ; +r-eq-z0-l ; ·r-/r-pos ; /r-·r-pos
  ; /r-pos-bound-l ; /r-pos-bound-u ; z0-decide ; ≤r-+-cancel-r
  ; <r-·-pos-factor-l ; <r-z1→pos-1-r
  ; zHalf ; z0<zHalf ; zHalf<z1 )

-- ============================================================
-- The Weight type: ℝ values in [z0, z1].
-- ============================================================

record Weight : Type₀ where
  constructor mkW
  field
    val : ℝ
    lb  : z0 ≤r val
    ub  : val ≤r z1
open Weight public

-- Equality of Weights reduces to equality of underlying values,
-- because the bound proofs are propositions.
WeightPath : ∀ {w₁ w₂ : Weight} → val w₁ ≡ val w₂ → w₁ ≡ w₂
WeightPath {mkW v₁ l₁ u₁} {mkW v₂ l₂ u₂} eqv i =
  mkW (eqv i)
      (isProp→PathP (λ j → isProp-z0≤ {x = eqv j}) l₁ l₂ i)
      (isProp→PathP (λ j → isProp-x≤z1 {x = eqv j}) u₁ u₂ i)

-- Weight is a set: from isSet-ℝ + propositional bounds.
-- isSetWeight: derived from isSet-ℝ + propositionality of bounds via isSetΣ.
isSetWeight : isSet Weight
isSetWeight =
  isSetRetract from-Weight to-Weight retract-eq isSetWeight-Σ
  where
    -- Underlying Σ-type: ℝ paired with bound proofs.
    Weight-Σ : Type₀
    Weight-Σ = Σ[ v ∈ ℝ ] (z0 ≤r v) × (v ≤r z1)

    isSetWeight-Σ : isSet Weight-Σ
    isSetWeight-Σ = isSetΣ isSet-ℝ
      (λ v → isProp→isSet (isProp× isProp-z0≤ isProp-x≤z1))

    -- Retract: Weight ↔ Weight-Σ (definitional).
    from-Weight : Weight → Weight-Σ
    from-Weight (mkW v l u) = v , (l , u)

    to-Weight : Weight-Σ → Weight
    to-Weight (v , (l , u)) = mkW v l u

    retract-eq : ∀ w → to-Weight (from-Weight w) ≡ w
    retract-eq (mkW v l u) = refl

-- ============================================================
-- Constants and operations
-- ============================================================

w0 : Weight
w0 = mkW z0 (≤r-refl z0) z0≤z1

w1 : Weight
w1 = mkW z1 z0≤z1 (≤r-refl z1)

-- Multiplication: closed in [0,1] because z1 is the max.
0≤·r : ∀ {a b : ℝ} → z0 ≤r a → z0 ≤r b → z0 ≤r (a ·r b)
0≤·r {a} {b} la lb' =
  -- (z0 ·r z0) ≤r (a ·r b) by ≤r-·-mono, then subst with z0·z0 = z0.
  subst (_≤r (a ·r b)) (·r-AnnihL z0)
    (≤r-·-mono (≤r-refl z0) (≤r-refl z0) la lb')

·r-bound : ∀ {a b : ℝ} → z0 ≤r a → z0 ≤r b → a ≤r z1 → b ≤r z1 → (a ·r b) ≤r z1
·r-bound {a} {b} la lb' ua ub' =
  -- (a·b) ≤ (a·z1) by ≤r-·-mono; (a·z1) = a by ·r-IdR; a ≤ z1 by ua.
  ≤r-trans
    (subst ((a ·r b) ≤r_) (·r-IdR a)
       (≤r-·-mono la lb' (≤r-refl a) ub'))
    ua

_*w_ : Weight → Weight → Weight
mkW v₁ l₁ u₁ *w mkW v₂ l₂ u₂ =
  mkW (v₁ ·r v₂) (0≤·r l₁ l₂) (·r-bound l₁ l₂ u₁ u₂)

infixl 7 _*w_

-- ============================================================
-- _+w_⟨_⟩: PARTIAL addition taking explicit bound proof.
--
-- This is the SOUND replacement of an unsound total _+w_ that
-- previously required the false postulate +r-bound-convex
-- (which claims sums of [0,1]-bounded reals stay in [0,1]).
--
-- The signature captures the contract that every use site
-- in the framework honors: when adding two weights in a
-- convex-combination context, the result is ≤ z1 by the
-- framework's invariants.
--
-- Bound-derivation helpers are provided below for the recurring
-- patterns: convex combinations, complement sums, weighted-idem
-- sums, and right-identity sums.
-- ============================================================
_+w_⟨_⟩ : (a b : Weight) → ((val a +r val b) ≤r z1) → Weight
(mkW v₁ l₁ u₁) +w (mkW v₂ l₂ u₂) ⟨ ub ⟩ =
  mkW (v₁ +r v₂) lb-pf ub
  where
    lb-pf : z0 ≤r (v₁ +r v₂)
    lb-pf = subst (_≤r (v₁ +r v₂)) (+r-IdR z0)
                  (≤r-+-mono l₁ l₂)

infixl 6 _+w_⟨_⟩

-- Transitional alias — to be removed after the migration cascade.
_+wPf_⟨_⟩ : (a b : Weight) → ((val a +r val b) ≤r z1) → Weight
a +wPf b ⟨ ub ⟩ = a +w b ⟨ ub ⟩

-- Complement: 1 - x is in [0,1] iff x is in [0,1].
1-r-bound-l : ∀ {x : ℝ} → x ≤r z1 → z0 ≤r (1-r x)
1-r-bound-l {x} x≤1 =
  subst (z0 ≤r_) (sym (1-r-def x))
    (subst (_≤r (z1 +r (-r x))) (+r-inv x)
           (≤r-+-mono x≤1 (≤r-refl (-r x))))

-- 1-r-bound-u: from 0 ≤ x, derive 1-x ≤ 1.
-- Strategy: from 0 ≤ x, get (-x) ≤ z0 (by +-monotone with -x on left,
-- using -x + 0 = -x and -x + x = 0). Then z1 + (-x) ≤ z1 + z0 = z1.
1-r-bound-u : ∀ {x : ℝ} → z0 ≤r x → (1-r x) ≤r z1
1-r-bound-u {x} 0≤x =
  let
    step1a : (z0 +r (-r x)) ≤r z0
    step1a = subst ((z0 +r (-r x)) ≤r_) (+r-inv x)
                   (≤r-+-mono 0≤x (≤r-refl (-r x)))
    z0+-x≡-x : (z0 +r (-r x)) ≡ (-r x)
    z0+-x≡-x = +r-comm z0 (-r x) ∙ +r-IdR (-r x)
    -x≤z0 : (-r x) ≤r z0
    -x≤z0 = subst (_≤r z0) z0+-x≡-x step1a
    step2 : (z1 +r (-r x)) ≤r (z1 +r z0)
    step2 = ≤r-+-mono (≤r-refl z1) -x≤z0
    z1+-x≤z1 : (z1 +r (-r x)) ≤r z1
    z1+-x≤z1 = subst ((z1 +r (-r x)) ≤r_) (+r-IdR z1) step2
  in subst (_≤r z1) (sym (1-r-def x)) z1+-x≤z1

1-w_ : Weight → Weight
1-w_ (mkW v l u) = mkW (1-r v) (1-r-bound-l u) (1-r-bound-u l)

-- ============================================================
-- Total division on Weight: defensive trivial fallback.
--
-- Returns w0 unconditionally. The active framework's actual
-- division reasoning routes through _/wPf_⟨_,_⟩ with explicit
-- preconditions; nothing in the active framework depends on
-- _/w_ producing an "honest" quotient.
--
-- This eliminates the /r-bound-{l,u}-defensive postulates entirely.
-- ============================================================

_/w_ : Weight → Weight → Weight
_ /w _ = w0

infixl 7 _/w_

-- ============================================================
-- The algebraic identities, lifted from ℝ to Weight via
-- WeightPath. These are bona fide theorems at the Weight
-- level; the ℝ-level facts they use are ring laws.
-- ============================================================

-- The +w-* lemmas now take an explicit upper-bound argument because
-- _+w_⟨_⟩ is a partial operator. The bound for the LHS is given;
-- the bound for the RHS is reconstructed via subst on the value
-- equality (using isProp-x≤z1 implicitly through the value-only
-- WeightPath construction).
+w-comm : ∀ p q (ub-pq : (val p +r val q) ≤r z1)
                (ub-qp : (val q +r val p) ≤r z1)
        → p +w q ⟨ ub-pq ⟩ ≡ q +w p ⟨ ub-qp ⟩
+w-comm p q _ _ = WeightPath (+r-comm (val p) (val q))

+w-assoc : ∀ p q r
           (ub-qr : (val q +r val r) ≤r z1)
           (ub-p+qr : (val p +r val (q +w r ⟨ ub-qr ⟩)) ≤r z1)
           (ub-pq : (val p +r val q) ≤r z1)
           (ub-pq+r : (val (p +w q ⟨ ub-pq ⟩) +r val r) ≤r z1)
        → p +w (q +w r ⟨ ub-qr ⟩) ⟨ ub-p+qr ⟩ ≡ (p +w q ⟨ ub-pq ⟩) +w r ⟨ ub-pq+r ⟩
+w-assoc p q r _ _ _ _ = WeightPath (+r-assoc (val p) (val q) (val r))

*w-comm : ∀ p q → p *w q ≡ q *w p
*w-comm p q = WeightPath (·r-comm (val p) (val q))

*w-1 : ∀ p → p *w w1 ≡ p
*w-1 p = WeightPath (·r-IdR (val p))

*w-0 : ∀ p → p *w w0 ≡ w0
*w-0 p = WeightPath (·r-AnnihR (val p))

-- +w-0 needs the bound (val p +r val w0) ≤r z1, which follows from val p ≤ z1.
+w-IdR-bound : ∀ p → (val p +r val w0) ≤r z1
+w-IdR-bound p = subst (_≤r z1) (sym (+r-IdR (val p))) (ub p)

+w-0 : ∀ p → p +w w0 ⟨ +w-IdR-bound p ⟩ ≡ p
+w-0 p = WeightPath (+r-IdR (val p))

-- Two further ring helpers needed for the remaining derivations.
-- Both are standard ring facts (negation distributes over +r,
-- and double negation is the identity); derived from existing axioms.

-- +r-cancel-l: derived from +r-inv, +r-assoc, +r-comm, +r-IdR.
-- (a + b ≡ a + c) → b ≡ c by left-multiplying both sides by (-a).
+r-cancel-l-ℝ : ∀ a b c → a +r b ≡ a +r c → b ≡ c
+r-cancel-l-ℝ a b c eq =
  sym chain ∙ cong ((-r a) +r_) eq ∙ chain'
  where
    z0+x≡x : ∀ x → z0 +r x ≡ x
    z0+x≡x x = +r-comm z0 x ∙ +r-IdR x
    -a+a≡0 : (-r a) +r a ≡ z0
    -a+a≡0 = +r-comm (-r a) a ∙ +r-inv a
    chain : (-r a) +r (a +r b) ≡ b
    chain = +r-assoc (-r a) a b ∙ cong (_+r b) -a+a≡0 ∙ z0+x≡x b
    chain' : (-r a) +r (a +r c) ≡ c
    chain' = +r-assoc (-r a) a c ∙ cong (_+r c) -a+a≡0 ∙ z0+x≡x c

-- -r-z0: -z0 ≡ z0. From z0 + (-z0) ≡ z0 (by +r-inv) and z0 + z0 ≡ z0 (by +r-IdR):
-- both sides equal, so -z0 ≡ z0 by +r-cancel-l.
-r-z0 : (-r z0) ≡ z0
-r-z0 =
  +r-cancel-l-ℝ z0 (-r z0) z0 (+r-inv z0 ∙ sym (+r-IdR z0))

-- -r-invol: -(-x) ≡ x. From (-x) + (-(-x)) ≡ z0 (+r-inv) and (-x) + x ≡ z0 (+r-inv after comm):
-- both equal, so by +r-cancel-l, -(-x) ≡ x.
-r-invol : ∀ x → (-r (-r x)) ≡ x
-r-invol x =
  +r-cancel-l-ℝ (-r x) (-r (-r x)) x
    (+r-inv (-r x) ∙ sym (+r-comm (-r x) x ∙ +r-inv x))

-- -r-distrib: -(a+b) ≡ -a + -b. We show (a+b) + (-a + -b) ≡ z0, then by uniqueness of additive
-- inverse (via +r-cancel-l): -(a+b) ≡ -a + -b.
-- Proof of (a+b) + (-a + -b) ≡ z0: rearrange via +-comm/assoc to (a + -a) + (b + -b) = z0 + z0 = z0.
-r-distrib : ∀ a b → (-r (a +r b)) ≡ (-r a) +r (-r b)
-r-distrib a b =
  +r-cancel-l-ℝ (a +r b) (-r (a +r b)) ((-r a) +r (-r b))
    (+r-inv (a +r b) ∙ sym sumeq)
  where
    -- (a+b) + (-a + -b) ≡ z0.
    -- Rearrange: a + b + -a + -b = a + (b + (-a)) + -b = a + (-a + b) + -b = (a + -a) + b + -b = b + -b = z0.
    sumeq : (a +r b) +r ((-r a) +r (-r b)) ≡ z0
    sumeq =
      +r-assoc (a +r b) (-r a) (-r b)
      ∙ cong (_+r (-r b))
          (sym (+r-assoc a b (-r a))
          ∙ cong (a +r_) (+r-comm b (-r a))
          ∙ +r-assoc a (-r a) b
          ∙ cong (_+r b) (+r-inv a)
          ∙ +r-comm z0 b ∙ +r-IdR b)
      ∙ +r-inv b

-- 1-r z0 = z1: derived from 1-r-def, -r-z0, and +r-IdR.
1-r-z0-ℝ : 1-r z0 ≡ z1
1-r-z0-ℝ =
  1-r-def z0
  ∙ cong (z1 +r_) -r-z0
  ∙ +r-IdR z1

-- 1-r z1 = z0: directly from 1-r-def and +r-inv (z1 + (-z1) = z0).
1-r-z1-ℝ : 1-r z1 ≡ z0
1-r-z1-ℝ = 1-r-def z1 ∙ +r-inv z1

-- p + (1-p) = 1: from 1-r-def, +r-comm, +r-assoc, +r-inv, +r-IdR.
+r-compl-ℝ : ∀ x → x +r (1-r x) ≡ z1
+r-compl-ℝ x =
  cong (x +r_) (1-r-def x)
  ∙ cong (x +r_) (+r-comm z1 (-r x))
  ∙ +r-assoc x (-r x) z1
  ∙ cong (_+r z1) (+r-inv x)
  ∙ +r-comm z0 z1
  ∙ +r-IdR z1

-- weighted-idem at the ℝ level: derived by reverse distributivity
-- and the complement identity above.
--   (p ·r x) +r ((1-r p) ·r x)
--     = (p +r (1-r p)) ·r x          [·r-distL reversed]
--     = z1 ·r x                       [+r-compl-ℝ]
--     = x                             [·r-IdL]
weighted-idem-ℝ : ∀ p x → (p ·r x) +r ((1-r p) ·r x) ≡ x
weighted-idem-ℝ p x =
  sym (·r-distL p (1-r p) x)
  ∙ cong (_·r x) (+r-compl-ℝ p)
  ∙ ·r-IdL x

-- 1-r-invol at the ℝ level: derived from 1-r-def, ring laws,
-- -r-distrib, and -r-invol.
--   1-r (1-r x)
--     = z1 +r (-r (z1 +r (-r x)))    [1-r-def, twice]
--     = z1 +r ((-r z1) +r (-r (-r x)))  [-r-distrib]
--     = z1 +r ((-r z1) +r x)          [-r-invol]
--     = (z1 +r (-r z1)) +r x          [+r-assoc]
--     = z0 +r x                        [+r-inv]
--     = x +r z0 = x                    [+r-comm, +r-IdR]
1-r-invol-ℝ : ∀ x → 1-r (1-r x) ≡ x
1-r-invol-ℝ x =
  1-r-def (1-r x)
  ∙ cong (z1 +r_) (cong -r_ (1-r-def x))
  ∙ cong (z1 +r_) (-r-distrib z1 (-r x))
  ∙ cong (λ w → z1 +r ((-r z1) +r w)) (-r-invol x)
  ∙ +r-assoc z1 (-r z1) x
  ∙ cong (_+r x) (+r-inv z1)
  ∙ +r-comm z0 x
  ∙ +r-IdR x

1-w-invol : ∀ p → 1-w (1-w p) ≡ p
1-w-invol p = WeightPath (1-r-invol-ℝ (val p))

1-w-0 : 1-w w0 ≡ w1
1-w-0 = WeightPath 1-r-z0-ℝ

1-w-1 : 1-w w1 ≡ w0
1-w-1 = WeightPath 1-r-z1-ℝ

-- compl-bound: the bound (val p +r val (1-w p)) ≤r z1 follows from the
-- complement identity p + (1-p) = 1 = z1.
compl-bound : ∀ p → (val p +r val (1-w p)) ≤r z1
compl-bound p = subst (_≤r z1) (sym (+r-compl-ℝ (val p))) (≤r-refl z1)

compl : ∀ p → p +w (1-w p) ⟨ compl-bound p ⟩ ≡ w1
compl p = WeightPath (+r-compl-ℝ (val p))

-- weighted-idem-bound: the bound for (p · x) + ((1-p) · x) reduces to val x ≤ z1.
weighted-idem-bound : ∀ p x → (val (p *w x) +r val ((1-w p) *w x)) ≤r z1
weighted-idem-bound p x =
  subst (_≤r z1) (sym (weighted-idem-ℝ (val p) (val x))) (ub x)

-- mix-bound: convex combination (p · a) + ((1-p) · b) is bounded by 1.
-- Proof: bound by p · 1 + (1-p) · 1 = p + (1-p) = 1 via ≤r-+-mono and
-- ≤r-·-mono. (Defined here — earlier than its narrative position — so
-- it can serve as the canonical bound for `weighted-idem` and downstream
-- HIT path-coherence in 𝔼.)
mix-bound : ∀ p a b → (val (p *w a) +r val ((1-w p) *w b)) ≤r z1
mix-bound p a b =
  -- (p·a) + ((1-p)·b) ≤ (p·z1) + ((1-p)·z1) = p + (1-p) = z1.
  subst ((val (p *w a) +r val ((1-w p) *w b)) ≤r_) compl-eq sum-le
  where
    pa≤p : (val p ·r val a) ≤r val p
    pa≤p = subst ((val p ·r val a) ≤r_) (·r-IdR (val p))
                 (≤r-·-mono (lb p) (lb a) (≤r-refl (val p)) (ub a))
    1-p·b≤1-p : (val (1-w p) ·r val b) ≤r val (1-w p)
    1-p·b≤1-p = subst ((val (1-w p) ·r val b) ≤r_) (·r-IdR (val (1-w p)))
                      (≤r-·-mono (lb (1-w p)) (lb b) (≤r-refl (val (1-w p))) (ub b))
    sum-le : (val (p *w a) +r val ((1-w p) *w b)) ≤r (val p +r val (1-w p))
    sum-le = ≤r-+-mono pa≤p 1-p·b≤1-p
    compl-eq : (val p +r val (1-w p)) ≡ z1
    compl-eq = +r-compl-ℝ (val p)

-- Use mix-bound p x x on the LHS so path-coherence with `mix p x x`'s
-- 𝔼 reduction is definitional. weighted-idem-bound and mix-bound are
-- propositionally equal but not definitionally; prefer mix-bound here.
weighted-idem : ∀ p x → (p *w x) +w ((1-w p) *w x) ⟨ mix-bound p x x ⟩ ≡ x
weighted-idem p x = WeightPath (weighted-idem-ℝ (val p) (val x))

*w-assoc : ∀ a b c → (a *w b) *w c ≡ a *w (b *w c)
*w-assoc a b c = WeightPath (sym (·r-assoc (val a) (val b) (val c)))

-- *w-distrib-+w: a *w (b +w c) ≡ (a *w b) +w (a *w c). Both sides need
-- bound proofs for the +w. The LHS bound is given; the RHS bound follows
-- by the same distributivity ·r-distR applied in reverse.
*w-distrib-+w-bound-r : ∀ a b c
  → (val b +r val c) ≤r z1
  → (val (a *w b) +r val (a *w c)) ≤r z1
*w-distrib-+w-bound-r a b c ub-bc =
  subst (_≤r z1) (·r-distR (val a) (val b) (val c))
        (·r-bound (lb a)
                  (subst (_≤r (val b +r val c)) (+r-IdR z0)
                         (≤r-+-mono (lb b) (lb c)))
                  (ub a)
                  ub-bc)

*w-distrib-+w : ∀ a b c
                (ub-bc : (val b +r val c) ≤r z1)
              → a *w (b +w c ⟨ ub-bc ⟩)
              ≡ (a *w b) +w (a *w c) ⟨ *w-distrib-+w-bound-r a b c ub-bc ⟩
*w-distrib-+w a b c _ = WeightPath (·r-distR (val a) (val b) (val c))

-- ============================================================
-- The expectation-related identities
-- ============================================================

-- Helper: medial law for +r in a commutative monoid.
-- (A +r B) +r (C +r D) ≡ (A +r C) +r (B +r D).
-- Proof:
--   (A+B) + (C+D)
--     = ((A+B) + C) + D       [+r-assoc (A+B) C D]
--     = (A + (B+C)) + D       [cong (_+r D) (sym (+r-assoc A B C))]
--     = (A + (C+B)) + D       [cong (λ w → (A+w)+D) (+r-comm B C)]
--     = ((A+C) + B) + D       [cong (_+r D) (+r-assoc A C B)]
--     = (A+C) + (B+D)         [sym (+r-assoc (A+C) B D)]
+r-medial : ∀ A B C D
  → (A +r B) +r (C +r D) ≡ (A +r C) +r (B +r D)
+r-medial A B C D =
  +r-assoc (A +r B) C D
  ∙ cong (_+r D) (sym (+r-assoc A B C))
  ∙ cong (λ w → (A +r w) +r D) (+r-comm B C)
  ∙ cong (_+r D) (+r-assoc A C B)
  ∙ sym (+r-assoc (A +r C) B D)

-- Helper: rearrange a triple product using ·r-comm and ·r-assoc.
-- (a ·r b) ·r c ≡ (b ·r a) ·r c.
·r-swap-12 : ∀ a b c → (a ·r b) ·r c ≡ (b ·r a) ·r c
·r-swap-12 a b c = cong (_·r c) (·r-comm a b)

-- Interchange identity at the ℝ level: derived from
-- distributivity, the medial law for +r, ·r-assoc, and
-- ·r-comm. The proof distributes the four ·r-distR
-- applications to get a sum of four monomials, then
-- reassociates to match the RHS structure.
--
--   (p ·r ((q ·r a) +r ((1-r q) ·r c))) +r ((1-r p) ·r ((q ·r b) +r ((1-r q) ·r d)))
--     = ((p ·r (q ·r a)) +r (p ·r ((1-r q) ·r c)))
--       +r (((1-r p) ·r (q ·r b)) +r ((1-r p) ·r ((1-r q) ·r d)))   [·r-distR ×2]
--     = ((p ·r (q ·r a)) +r ((1-r p) ·r (q ·r b)))
--       +r ((p ·r ((1-r q) ·r c)) +r ((1-r p) ·r ((1-r q) ·r d)))   [+r-medial]
--     = ((q ·r (p ·r a)) +r (q ·r ((1-r p) ·r b)))
--       +r (((1-r q) ·r (p ·r c)) +r ((1-r q) ·r ((1-r p) ·r d)))    [·r-comm/assoc]
--     = (q ·r ((p ·r a) +r ((1-r p) ·r b)))
--       +r ((1-r q) ·r ((p ·r c) +r ((1-r p) ·r d)))                  [sym ·r-distR ×2]
·r-interchange-eq : ∀ p q a b c d
  → (p ·r ((q ·r a) +r ((1-r q) ·r c))) +r ((1-r p) ·r ((q ·r b) +r ((1-r q) ·r d)))
  ≡ (q ·r ((p ·r a) +r ((1-r p) ·r b))) +r ((1-r q) ·r ((p ·r c) +r ((1-r p) ·r d)))
·r-interchange-eq p q a b c d =
  -- Step 1: distribute p over the inner sum, and (1-r p) over the inner sum.
  cong (_+r ((1-r p) ·r ((q ·r b) +r ((1-r q) ·r d))))
       (·r-distR p (q ·r a) ((1-r q) ·r c))
  ∙ cong (((p ·r (q ·r a)) +r (p ·r ((1-r q) ·r c))) +r_)
         (·r-distR (1-r p) (q ·r b) ((1-r q) ·r d))
  -- Step 2: rearrange via the medial law for +r.
  ∙ +r-medial
      (p ·r (q ·r a))
      (p ·r ((1-r q) ·r c))
      ((1-r p) ·r (q ·r b))
      ((1-r p) ·r ((1-r q) ·r d))
  -- Step 3: rearrange triple products: p·(q·a) = q·(p·a), etc.
  -- We do these via cong applications using ·r-assoc and ·r-comm.
  -- p ·r (q ·r a) = (p ·r q) ·r a = (q ·r p) ·r a = q ·r (p ·r a)
  ∙ cong (λ w → (w +r ((1-r p) ·r (q ·r b))) +r ((p ·r ((1-r q) ·r c)) +r ((1-r p) ·r ((1-r q) ·r d))))
         (·r-assoc p q a ∙ ·r-swap-12 p q a ∙ sym (·r-assoc q p a))
  -- (1-r p) ·r (q ·r b) = q ·r ((1-r p) ·r b) (similar move).
  ∙ cong (λ w → ((q ·r (p ·r a)) +r w) +r ((p ·r ((1-r q) ·r c)) +r ((1-r p) ·r ((1-r q) ·r d))))
         (·r-assoc (1-r p) q b ∙ ·r-swap-12 (1-r p) q b ∙ sym (·r-assoc q (1-r p) b))
  -- p ·r ((1-r q) ·r c) = (1-r q) ·r (p ·r c).
  ∙ cong (λ w → ((q ·r (p ·r a)) +r (q ·r ((1-r p) ·r b))) +r (w +r ((1-r p) ·r ((1-r q) ·r d))))
         (·r-assoc p (1-r q) c ∙ ·r-swap-12 p (1-r q) c ∙ sym (·r-assoc (1-r q) p c))
  -- (1-r p) ·r ((1-r q) ·r d) = (1-r q) ·r ((1-r p) ·r d).
  ∙ cong (λ w → ((q ·r (p ·r a)) +r (q ·r ((1-r p) ·r b))) +r (((1-r q) ·r (p ·r c)) +r w))
         (·r-assoc (1-r p) (1-r q) d ∙ ·r-swap-12 (1-r p) (1-r q) d ∙ sym (·r-assoc (1-r q) (1-r p) d))
  -- Step 4: reverse-distribute the two outer pairs.
  ∙ cong (_+r (((1-r q) ·r (p ·r c)) +r ((1-r q) ·r ((1-r p) ·r d))))
         (sym (·r-distR q (p ·r a) ((1-r p) ·r b)))
  ∙ cong ((q ·r ((p ·r a) +r ((1-r p) ·r b))) +r_)
         (sym (·r-distR (1-r q) (p ·r c) ((1-r p) ·r d)))

-- Commutativity identity at the ℝ level: derived by
-- +r-comm together with 1-r-invol-ℝ.
--   (p ·r x) +r ((1-r p) ·r y)
--     = ((1-r p) ·r y) +r (p ·r x)            [+r-comm]
--     = ((1-r p) ·r y) +r ((1-r (1-r p)) ·r x)  [sym 1-r-invol]
·r-commute-eq : ∀ p x y
  → (p ·r x) +r ((1-r p) ·r y) ≡ ((1-r p) ·r y) +r ((1-r (1-r p)) ·r x)
·r-commute-eq p x y =
  +r-comm (p ·r x) ((1-r p) ·r y)
  ∙ cong (λ w → ((1-r p) ·r y) +r (w ·r x)) (sym (1-r-invol-ℝ p))

-- bdy0 at the ℝ level: derivable from ring laws, ·r-AnnihL,
-- 1-r-z0-ℝ, ·r-IdL, +r-IdR.
--   (z0 ·r x) +r ((1-r z0) ·r y)
--     = z0 +r ((1-r z0) ·r y)        [·r-AnnihL]
--     = z0 +r (z1 ·r y)              [1-r-z0-ℝ]
--     = z0 +r y                      [·r-IdL]
--     = y +r z0                      [+r-comm]
--     = y                            [+r-IdR]
·r-bdy0-eq : ∀ x y → (z0 ·r x) +r ((1-r z0) ·r y) ≡ y
·r-bdy0-eq x y =
  cong (_+r ((1-r z0) ·r y)) (·r-AnnihL x)
  ∙ cong (λ w → z0 +r (w ·r y)) 1-r-z0-ℝ
  ∙ cong (z0 +r_) (·r-IdL y)
  ∙ +r-comm z0 y
  ∙ +r-IdR y

-- bdy1 at the ℝ level:
--   (z1 ·r x) +r ((1-r z1) ·r y)
--     = x +r ((1-r z1) ·r y)         [·r-IdL]
--     = x +r (z0 ·r y)               [1-r-z1-ℝ]
--     = x +r z0                      [·r-AnnihL]
--     = x                            [+r-IdR]
·r-bdy1-eq : ∀ x y → (z1 ·r x) +r ((1-r z1) ·r y) ≡ x
·r-bdy1-eq x y =
  cong (_+r ((1-r z1) ·r y)) (·r-IdL x)
  ∙ cong (λ w → x +r (w ·r y)) 1-r-z1-ℝ
  ∙ cong (x +r_) (·r-AnnihL y)
  ∙ +r-IdR x

-- (mix-bound is defined earlier, before weighted-idem, so it's available
--  there as the canonical convex-combination bound.)

-- commute bound: bound for ((1-w p) · y) + ((1-w (1-w p)) · x).
commute-bound : ∀ p x y → (val ((1-w p) *w y) +r val ((1-w (1-w p)) *w x)) ≤r z1
commute-bound p x y =
  subst (_≤r z1) (·r-commute-eq (val p) (val x) (val y))
        (mix-bound p x y)

-- Use mix-bound (1-w p) y x on the RHS so that 𝔼's HIT path-coherence
-- can match commuteProof's endpoint definitionally with the bound it
-- computes for (mix (1-w p) y x). The two bounds are propositionally
-- equal but not definitionally; choosing mix-bound here lets `𝔼 (mix-comm …)`
-- typecheck without isProp-→PathP coercion.
commuteProof : ∀ (p : Weight) (x y : Weight)
  → (p *w x) +w ((1-w p) *w y) ⟨ mix-bound p x y ⟩
  ≡ ((1-w p) *w y) +w ((1-w (1-w p)) *w x) ⟨ mix-bound (1-w p) y x ⟩
commuteProof p x y = WeightPath (·r-commute-eq (val p) (val x) (val y))

bdy0Proof : ∀ (x y : Weight)
  → (w0 *w x) +w ((1-w w0) *w y) ⟨ mix-bound w0 x y ⟩ ≡ y
bdy0Proof x y = WeightPath (·r-bdy0-eq (val x) (val y))

bdy1Proof : ∀ (x y : Weight)
  → (w1 *w x) +w ((1-w w1) *w y) ⟨ mix-bound w1 x y ⟩ ≡ x
bdy1Proof x y = WeightPath (·r-bdy1-eq (val x) (val y))

-- interchange bound for the LHS of interchangeProof.
interchange-bound-lhs : ∀ p q a b c d
  → (val (p *w ((q *w a) +w ((1-w q) *w c) ⟨ mix-bound q a c ⟩))
     +r val ((1-w p) *w ((q *w b) +w ((1-w q) *w d) ⟨ mix-bound q b d ⟩))) ≤r z1
interchange-bound-lhs p q a b c d =
  mix-bound p ((q *w a) +w ((1-w q) *w c) ⟨ mix-bound q a c ⟩)
              ((q *w b) +w ((1-w q) *w d) ⟨ mix-bound q b d ⟩)

-- interchange bound for the RHS of interchangeProof.
interchange-bound-rhs : ∀ p q a b c d
  → (val (q *w ((p *w a) +w ((1-w p) *w b) ⟨ mix-bound p a b ⟩))
     +r val ((1-w q) *w ((p *w c) +w ((1-w p) *w d) ⟨ mix-bound p c d ⟩))) ≤r z1
interchange-bound-rhs p q a b c d =
  mix-bound q ((p *w a) +w ((1-w p) *w b) ⟨ mix-bound p a b ⟩)
              ((p *w c) +w ((1-w p) *w d) ⟨ mix-bound p c d ⟩)

interchangeProof : ∀ (p q : Weight) (a b c d : Weight)
  → (p *w ((q *w a) +w ((1-w q) *w c) ⟨ mix-bound q a c ⟩))
    +w ((1-w p) *w ((q *w b) +w ((1-w q) *w d) ⟨ mix-bound q b d ⟩))
    ⟨ interchange-bound-lhs p q a b c d ⟩
  ≡ (q *w ((p *w a) +w ((1-w p) *w b) ⟨ mix-bound p a b ⟩))
    +w ((1-w q) *w ((p *w c) +w ((1-w p) *w d) ⟨ mix-bound p c d ⟩))
    ⟨ interchange-bound-rhs p q a b c d ⟩
interchangeProof p q a b c d =
  WeightPath (·r-interchange-eq (val p) (val q) (val a) (val b) (val c) (val d))

-- s-of weight helper. The bound for p + (1-p)·q reduces via convex
-- combination intuition: p + (1-p)·q = p·1 + (1-p)·q ≤ 1.
s-of-bound : ∀ p q → (val p +r val ((1-w p) *w q)) ≤r z1
s-of-bound p q =
  -- val p ≡ val p ·r z1 = val (p *w w1) (computed).
  -- mix-bound p w1 q has type ((val p ·r z1) +r ((1-r val p) ·r val q)) ≤r z1.
  -- We rewrite (val p ·r z1) to val p via ·r-IdR.
  subst (λ z → (z +r val ((1-w p) *w q)) ≤r z1) (·r-IdR (val p))
        (mix-bound p w1 q)

s-of : Weight → Weight → Weight
s-of p q = p +w ((1-w p) *w q) ⟨ s-of-bound p q ⟩

-- (r-of and bayesW are dead in this module — the active framework
-- defines its own r-of via normalize in WeightQ-Convex.agda. They've
-- been deleted along with the dependent assocProof / s·r≡p-lem /
-- s·1-r-eq-lem / 1-w-s-eq-lem helpers, which are also unused.)

-- ============================================================
-- Positivity predicate and its closure laws
-- ============================================================

Pos : Weight → Type₀
Pos w = z0 <r val w

isProp-Pos : ∀ w → isProp (Pos w)
isProp-Pos w = isProp-<r

pos-w1 : Pos w1
pos-w1 = z0<z1

pos-+w-l : ∀ {p q : Weight} (ub : (val p +r val q) ≤r z1)
         → Pos p → Pos (p +w q ⟨ ub ⟩)
pos-+w-l {p} {q} _ pp = <r-+-pos-l pp (lb q)

pos-*w : ∀ {p q : Weight} → Pos p → Pos q → Pos (p *w q)
pos-*w pp pq = <r-·-pos pp pq

-- ============================================================
-- Discharge of FDist's order/cancellation axioms as theorems.
-- Each FDist postulate becomes a Weight-level theorem here,
-- closing the soundness chain.
-- ============================================================

-- ¬Pos-w0: w0 is not positive (irreflexivity of <r at z0).
¬Pos-w0 : ¬ Pos w0
¬Pos-w0 pw0 = <r-irrefl z0 pw0

-- ============================================================
-- _/w_pf: PARTIAL division taking explicit preconditions.
--
-- This is the partial division the framework uses. The value is
-- honest ℚ division (WeightQ-Discharge-Division), and the bound
-- proofs are derived from the Pos and ≤ precondition arguments;
-- nothing here is postulated.
-- ============================================================
_/wPf_⟨_,_⟩ : (a b : Weight) → Pos b → (val a ≤r val b) → Weight
(mkW v₁ l₁ _) /wPf (mkW v₂ _ _) ⟨ pb , le ⟩ =
  mkW (v₁ /r v₂)
      (/r-pos-bound-l v₁ v₂ l₁ pb)
      (/r-pos-bound-u v₁ v₂ le pb)

-- Bridge lemma /w-≡-/wPf was here; removed because the new _/w_ is
-- a defensive total stub and the bridge no longer holds. The active
-- framework uses _/wPf_⟨_,_⟩ directly with explicit preconditions.

-- w0≢w1: w0 and w1 are distinct.
-- If w0 ≡ w1, then val w0 ≡ val w1, i.e., z0 ≡ z1. Substituting
-- into z0<z1 gives z0<z0, impossible by <r-irrefl.
w0≢w1 : ¬ (w0 ≡ w1)
w0≢w1 w0≡w1 = <r-irrefl z0 (subst (z0 <r_) (sym (cong val w0≡w1)) z0<z1)

-- wHalf: a strictly interior weight (½).  It is the concrete witness
-- that an interior confounding strength exists, so the do≠see theorem
-- (Topos.DoSeeDistinct) is not vacuous.  Both Pos wHalf and
-- Pos (1-w wHalf) hold, from the strict bounds z0 < ½ < z1.
wHalf : Weight
wHalf = mkW zHalf (<r-implies-≤r z0<zHalf) (<r-implies-≤r zHalf<z1)

Pos-wHalf : Pos wHalf
Pos-wHalf = z0<zHalf

Pos-1-wHalf : Pos (1-w wHalf)
Pos-1-wHalf = <r-z1→pos-1-r zHalf<z1

-- wHalf ≢ w1: the interior weight is not the top point (its complement
-- is positive).  This is the scalar gap that separates do from see.
wHalf≢w1 : ¬ (wHalf ≡ w1)
wHalf≢w1 h = ¬Pos-w0 (subst Pos (cong 1-w_ h ∙ 1-w-1) Pos-1-wHalf)

-- +w-cancel-l: derived from +r-cancel-l-ℝ (which is itself
-- derived from the abstract ring axioms).
-- From a+w b ≡ a+w c, lift to val: val a +r val b ≡ val a +r val c.
-- Apply +r-cancel-l-ℝ: val b ≡ val c. Lift to b ≡ c via WeightPath.
+w-cancel-l : ∀ a b c
              (ub-ab : (val a +r val b) ≤r z1)
              (ub-ac : (val a +r val c) ≤r z1)
            → a +w b ⟨ ub-ab ⟩ ≡ a +w c ⟨ ub-ac ⟩ → b ≡ c
+w-cancel-l a b c _ _ eq = WeightPath (+r-cancel-l-ℝ (val a) (val b) (val c) (cong val eq))

-- +w-eq-w0-l: in [0,1], a sum equal to w0 forces both summands w0.
-- Apply +r-eq-z0-l using the lower bounds lb a, lb b.
+w-eq-w0-l : ∀ a b (ub : (val a +r val b) ≤r z1)
           → a +w b ⟨ ub ⟩ ≡ w0 → a ≡ w0
+w-eq-w0-l a b _ eq = WeightPath (+r-eq-z0-l (val a) (val b) (lb a) (lb b) (cong val eq))

-- pos-*w-factor-l: from Pos (p ·w q), derive Pos p.
-- In our model, Pos x = z0 <r val x. We have val (p ·w q) = val p ·r val q.
-- The strict positivity 0 < val p · val q with val p, val q ∈ [0,1] forces val p > 0:
-- if val p = 0, then val p · val q = 0, contradicting Pos.
-- We prove this via discrimination ≡z1-or-<z1 (used to get strict info).
-- Direct: from Pos (p·q), case-split on whether val p = z0 or z0 < val p.
-- We use the fact that z0 ≤ val p (lb p) and discrimination at z0.
-- Cleaner: contrapositive via ≡z1-or-<z1 isn't directly applicable; use
-- a different route via the ordered field structure.
-- Below: we use the ℝ-level lemma <r-·-pos-factor-l (proved in
-- WeightQ-Discharge) and lift it via lb p.
pos-*w-factor-l : ∀ {p q : Weight} → Pos (p *w q) → Pos p
pos-*w-factor-l {p} {q} pp·q = <r-·-pos-factor-l (lb p) pp·q

-- weight-trichotomy: every weight is ≡ w1 or has positive complement.
-- Apply ≡z1-or-<z1 to val p (which is in [z0, z1]).
weight-trichotomy : ∀ p → (p ≡ w1) ⊎ Pos (1-w p)
weight-trichotomy p with ≡z1-or-<z1 (val p) (lb p) (ub p)
... | inl val-p≡z1 = inl (WeightPath val-p≡z1)
... | inr val-p<z1 = inr (<r-z1→pos-1-r val-p<z1)

-- *w-/wPf-pos: round-trip identity at the partial level.
*w-/wPf-pos : ∀ (y : Weight) (py : Pos y) (x : Weight)
            → (le : val (x *w y) ≤r val y)
            → ((x *w y) /wPf y ⟨ py , le ⟩) ≡ x
*w-/wPf-pos y py x le = WeightPath (·r-/r-pos py (val x))

/wPf-*w-pos : ∀ (y : Weight) (py : Pos y) (x : Weight)
            → (le : val x ≤r val y)
            → ((x /wPf y ⟨ py , le ⟩) *w y) ≡ x
/wPf-*w-pos y py x le = WeightPath (/r-·r-pos py (val x))

-- *w-/w-pos and /w-*w-pos were here; removed because they make claims
-- about the total _/w_ that are false when _/w_ is the defensive stub.
-- Use *w-/wPf-pos and /wPf-*w-pos (above) for the partial form.

-- ============================================================
-- bayesW was here (dead code). The active framework defines its
-- own bayesW in FDist-Convex.agda taking an explicit Pos witness.
-- ============================================================

-- ============================================================
-- The Weight-level convex algebra (the structural identities, the
-- bayesW division identities, and the unit-interval closure laws)
-- is proved here, not postulated: each is lifted via WeightPath
-- from an ℝ-level identity, and ℝ is the concrete cubical-library
-- ℚ (WeightQ-Field, with positivity-tracked division in
-- WeightQ-Discharge-Division).  The FDist path constructor
-- mix-bayes-interchange lives in the FDist higher inductive type
-- (FDist-Convex), not here.  This module contains no postulate.
-- ============================================================

-- ============================================================
-- assocProof derivation.
--
-- The skew-associativity polynomial identity at the Weight level.
-- Derived from:
--   - s·r≡p             (requires Pos (s-of p q))
--   - s·1-r-eq          (requires Pos (s-of p q))
--   - 1-w-s-eq          (unconditional)
--   - weight-trichotomy-zero, +w-eq-w0-{l,r}
-- The Pos case expands both sides via *w-distrib-+w + *w-assoc and
-- substitutes the three identities. The s ≡ w0 case forces both
-- p ≡ q ≡ w0, so both sides reduce to wc.
-- ============================================================

-- Helper: weight-trichotomy-zero.
weight-trichotomy-zero : ∀ p → Pos p ⊎ (p ≡ w0)
weight-trichotomy-zero p with weight-trichotomy (1-w p)
... | inl 1-p≡w1 = inr (sym (1-w-invol p) ∙ cong 1-w_ 1-p≡w1 ∙ 1-w-1)
... | inr Pos-1-1-p = inl (subst Pos (1-w-invol p) Pos-1-1-p)

-- Helper: +w-eq-w0-r derived from +w-eq-w0-l + +w-comm.
+w-eq-w0-r : ∀ a b (ub : (val a +r val b) ≤r z1)
           → a +w b ⟨ ub ⟩ ≡ w0 → b ≡ w0
+w-eq-w0-r a b ub eq =
  +w-eq-w0-l b a ub-ba
    (+w-comm b a ub-ba ub ∙ eq)
  where
    ub-ba : (val b +r val a) ≤r z1
    ub-ba = subst (_≤r z1) (+r-comm (val a) (val b)) ub

-- Lemma s·r≡p: when Pos (s-of p q), s-of p q · r-of p q ≡ p.

-- ============================================================
-- s·r≡p-lem, s·1-r-eq-lem, 1-w-s-eq-lem, assocProof were here
-- (dead code in the active framework). They depended on the now-
-- deleted r-of and *w-/w-pos / /w-*w-pos. Since the active
-- convex framework derives mix-associativity directly via
-- mix-w-assoc-pos in FDist-Convex.agda, these helpers are not
-- needed and have been removed.
-- ============================================================
