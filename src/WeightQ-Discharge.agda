{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- WeightQ-Discharge.agda
--
-- This module discharges the abstract ordered-field interface
-- postulated in WeightQ.agda.  It exhibits ℚ, the rationals of
-- Cubical.Data.Rationals, as a concrete model.
--
-- WeightQ.agda lifts that abstract interface to the
-- [0,1]-bounded Weight type.  The two modules together complete
-- the soundness chain for the representation theorem:
--
--    FDist.agda                  (abstract Weight axioms)
--      ↑ discharged by
--    WeightQ.agda               (concrete Weight = [z0, z1] ⊆ ℝ)
--      ↑ ℝ discharged by
--    WeightQ-Discharge.agda     (this file: ℝ ≔ ℚ from cubical lib)
--
-- Every "ordered field with bounded division" axiom postulated
-- at the WeightQ level appears here as a concrete theorem about
-- ℚ.  The remaining gap is the bound-preservation laws on
-- division, which WeightQ postulates defensively.  Those need a
-- defensive total division operator on ℚ.  We define one here,
-- by case analysis on Q ≡ 0.
--
-- Status: this file demonstrates soundness.  It does not
-- replace WeightQ.agda.  It exhibits one concrete model.
-- WeightQ.agda is parametric over the abstract interface, so
-- anything proved there holds in every model of the interface.
-- ℚ is the canonical model.
-- ============================================================

module WeightQ-Discharge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Rationals.Base as Q using (ℚ; [_/_])
open import Cubical.Data.Rationals.Order as QO using (_≤_; _<_; ≤Dec; <Dec)
open import Cubical.Data.Rationals.Properties as QP
open import Cubical.Data.Int as ℤ using (ℤ; pos; negsuc)
open import Cubical.Data.Int.Order as ℤO using ()
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)

-- ============================================================
-- ℝ ≔ ℚ
-- ============================================================

ℝ : Type₀
ℝ = ℚ

isSet-ℝ : isSet ℝ
isSet-ℝ = Q.isSetℚ

z0 z1 : ℝ
z0 = [ pos 0 / 1 ]
z1 = [ pos 1 / 1 ]

-- Operations
_+r_ : ℝ → ℝ → ℝ
_+r_ = QP._+_

_·r_ : ℝ → ℝ → ℝ
_·r_ = QP._·_

-r_ : ℝ → ℝ
-r_ = QP.-_

infixl 7 _·r_
infixl 6 _+r_

-- Order
_≤r_ : ℝ → ℝ → Type₀
_≤r_ = QO._≤_

_<r_ : ℝ → ℝ → Type₀
_<r_ = QO._<_

isProp-≤r : ∀ {x y} → isProp (x ≤r y)
isProp-≤r {x} {y} = QO.isProp≤ x y

isProp-<r : ∀ {x y} → isProp (x <r y)
isProp-<r {x} {y} = QO.isProp< x y

-- ============================================================
-- Ring laws.  Every WeightQ ℝ-postulate is a theorem here.
-- ============================================================

+r-comm   : ∀ x y → x +r y ≡ y +r x
+r-comm = QP.+Comm

+r-assoc  : ∀ x y z → x +r (y +r z) ≡ (x +r y) +r z
+r-assoc = QP.+Assoc

+r-IdR    : ∀ x → x +r z0 ≡ x
+r-IdR = QP.+IdR

+r-inv    : ∀ x → x +r (-r x) ≡ z0
+r-inv = QP.+InvR

·r-comm   : ∀ x y → x ·r y ≡ y ·r x
·r-comm = QP.·Comm

·r-assoc  : ∀ x y z → x ·r (y ·r z) ≡ (x ·r y) ·r z
·r-assoc = QP.·Assoc

·r-IdL    : ∀ x → z1 ·r x ≡ x
·r-IdL = QP.·IdL

·r-IdR    : ∀ x → x ·r z1 ≡ x
·r-IdR = QP.·IdR

·r-AnnihL : ∀ x → z0 ·r x ≡ z0
·r-AnnihL = QP.·AnnihilL

·r-AnnihR : ∀ x → x ·r z0 ≡ z0
·r-AnnihR = QP.·AnnihilR

·r-distR  : ∀ a b c → a ·r (b +r c) ≡ (a ·r b) +r (a ·r c)
·r-distR = QP.·DistL+

·r-distL  : ∀ a b c → (a +r b) ·r c ≡ (a ·r c) +r (b ·r c)
·r-distL = QP.·DistR+

-- ============================================================
-- Order laws
-- ============================================================

≤r-refl  : ∀ x → x ≤r x
≤r-refl x = QO.isRefl≤ x

≤r-trans : ∀ {x y z} → x ≤r y → y ≤r z → x ≤r z
≤r-trans {x} {y} {z} = QO.isTrans≤ x y z

≤r-antisym : ∀ {x y} → x ≤r y → y ≤r x → x ≡ y
≤r-antisym {x} {y} = QO.isAntisym≤ x y

z0≤z1    : z0 ≤r z1
z0≤z1 = ℤO.zero-≤pos

-- 0 < 1 is constructed as (0 , refl), since
-- pos 1 = pos (suc 0) = pos 0 + 1.
z0<z1    : z0 <r z1
z0<z1 = 0 , refl

-- A strictly interior value ½ = [1/2].  It witnesses that the
-- unit interval has a point strictly between its endpoints.
-- Both strict bounds use the same (0 , refl) cross-multiplication
-- witness as z0<z1: 0·2 < 1·1, and 1·1 < 1·2.  Downstream this
-- value keeps a confounded model non-degenerate (WeightQ.wHalf).
zHalf : ℝ
zHalf = [ pos 1 / 2 ]

z0<zHalf : z0 <r zHalf
z0<zHalf = 0 , refl

zHalf<z1 : zHalf <r z1
zHalf<z1 = 0 , refl

<r-implies-≤r : ∀ {x y} → x <r y → x ≤r y
<r-implies-≤r {x} {y} = QO.<Weaken≤ x y

≤r-+-mono : ∀ {a b c d} → a ≤r b → c ≤r d → (a +r c) ≤r (b +r d)
≤r-+-mono {a} {b} {c} {d} ab cd = QO.≤Monotone+ a b c d ab cd

-- ============================================================
-- The two-factor monotone product inequality.
-- It chains two uses of single-factor monotonicity:
--   a ≤ b and 0 ≤ c give a·c ≤ b·c   (≤-·o, monotone in the
--                                     left factor)
--   c ≤ d and 0 ≤ b give b·c ≤ b·d   (the same after ·Comm)
-- The side condition 0 ≤ b follows from 0 ≤ a and a ≤ b, by
-- transitivity.
-- ============================================================
≤r-·-mono : ∀ {a b c d} → z0 ≤r a → z0 ≤r c
          → a ≤r b → c ≤r d → (a ·r c) ≤r (b ·r d)
≤r-·-mono {a} {b} {c} {d} z0≤a z0≤c a≤b c≤d =
  ≤r-trans {a ·r c} {b ·r c} {b ·r d} step1 step2
  where
    step1 : (a ·r c) ≤r (b ·r c)
    step1 = QO.≤-·o a b c z0≤c a≤b

    z0≤b : z0 ≤r b
    z0≤b = ≤r-trans {z0} {a} {b} z0≤a a≤b

    step2 : (b ·r c) ≤r (b ·r d)
    step2 = subst2 _≤r_ (·r-comm c b) (·r-comm d b)
                   (QO.≤-·o c d b z0≤b c≤d)

-- ============================================================
-- Strict positivity of products: 0 < a · b when 0 < a and
-- 0 < b.  Apply <-·o : 0 < o → m < n → m·o < n·o with m=0, n=a,
-- o=b, and use ·AnnihilL to rewrite 0·b as 0.
-- ============================================================
<r-·-pos  : ∀ {a b} → z0 <r a → z0 <r b → z0 <r (a ·r b)
<r-·-pos {a} {b} z0<a z0<b =
  subst (_<r (a ·r b)) (·r-AnnihL b)
        (QO.<-·o z0 a b z0<b z0<a)

-- ============================================================
-- 0 < a + b when 0 < a and 0 ≤ b.
-- For a < a + b, translate the hypothesis 0 < a by
-- +-monotonicity, with b on the right.
-- In detail: 0 < a means there is a k with a = pos (suc k) + 0,
-- lifted to ℚ.  Then <-+o, additive monotonicity, gives
-- (0 + b) < (a + b), that is b < a+b.  With 0 ≤ b this gives
-- 0 < a+b.
-- ============================================================
<r-+-pos-l : ∀ {a b} → z0 <r a → z0 ≤r b → z0 <r (a +r b)
<r-+-pos-l {a} {b} z0<a z0≤b =
  -- z0 ≤ b combined with b < a + b gives z0 < a + b by isTrans≤<.
  QO.isTrans≤< z0 b (a +r b) z0≤b b<a+b
  where
    -- b < a + b: translate z0 < a by adding b on the left.
    -- <-o+ : ∀ m n o → m < n → o + m < o + n
    -- With m=z0, n=a, o=b: b + z0 < b + a.
    b+0<b+a : (b +r z0) <r (b +r a)
    b+0<b+a = QO.<-o+ z0 a b z0<a

    -- Simplify: b + z0 = b, b + a = a + b.
    b<a+b : b <r (a +r b)
    b<a+b = subst2 _<r_ (+r-IdR b) (+r-comm b a) b+0<b+a

-- ============================================================
-- Propositionality of order on the boundary points.
-- ============================================================
isProp-z0≤ : ∀ {x} → isProp (z0 ≤r x)
isProp-z0≤ {x} = QO.isProp≤ z0 x

isProp-x≤z1 : ∀ {x} → isProp (x ≤r z1)
isProp-x≤z1 {x} = QO.isProp≤ x z1

-- ============================================================
-- Subtraction (1 - x).
-- ============================================================
1-r : ℝ → ℝ
1-r x = z1 +r (-r x)

1-r-def : ∀ x → 1-r x ≡ z1 +r (-r x)
1-r-def x = refl

-- ============================================================
-- Division: defensive total operator.
--
-- In the abstract WeightQ.agda development, _/r_ is used only
-- through the bayesW formulas.  Only the algebraic identities on
-- _/w_ matter there, and those are postulated separately as
-- bayesW-*.  No theorem in Representation.agda or
-- Intersection.agda uses the concrete value that _/r_ returns in
-- WeightQ-Discharge.
--
-- So, to remove the last ℝ-interface postulate, we give a
-- trivial implementation that always returns z0.  The discharge
-- is sound.  Every Weight axiom and theorem holds without any
-- appeal to the semantic content of _/r_, because every
-- _/r_-using lemma is postulated separately as a bayesW-*
-- identity.  A semantically correct ℚ division would refine this
-- implementation.  Such a division returns z0 on a zero divisor
-- and the standard quotient otherwise.  The trivial version is
-- enough to discharge the postulate.
-- ============================================================
-- ============================================================
-- Honest division on ℚ.
--
-- Imported from WeightQ-Discharge-Division.agda.  That module
-- builds the inverse construction on Cubical.Data.Rationals.ℚ,
-- using SetQuot.elimProp together with inverseUniqueness from the
-- ℚ-CommRing instance.
--
-- For non-zero y: x /r y returns the actual quotient.
-- For y ≡ z0:     returns z0 (defensive default).
--
-- This closes the soundness gap.  ·r-/r-pos and /r-·r-pos are
-- now derived theorems, not postulates.
-- ============================================================
open import WeightQ-Discharge-Division
  using (honest/r; ·r-/r-pos-derived; /r-·r-pos-derived)
  renaming (ℚ-0 to ℚ-zero)

_/r_ : ℝ → ℝ → ℝ
_/r_ = honest/r

infixl 7 _/r_

-- ============================================================
-- Additional ℝ-level axioms used by WeightQ for discharging
-- the remaining order/division postulates of FDist.
-- ============================================================

-- Strict ordering is irreflexive.
-- ℚ has < as a strict order.  The witness (0, refl) for 0 < 1
-- cannot match 0 < 0.  We use QO.isIrrefl< where the library
-- supplies it, and otherwise refute directly from the Σ-type.
-- For ℚ, x < x means there is a k with x ≡ pos (suc k) + x.
-- That forces pos (suc k) ≡ pos 0, which is false.
-- ============================================================
-- Order/positivity axioms, derived.
--
-- Five of the seven earlier postulates are now theorems.  They
-- are built from the ℚ order infrastructure of cubical-stdlib.
-- ============================================================

-- Item 1: irreflexivity of the strict order.  Direct from the
-- cubical library.
<r-irrefl : ∀ x → ¬ (x <r x)
<r-irrefl x = QO.isIrrefl< x

-- Item 2: at z1, totality decomposes ≤ into < or ≡.
-- Use trichotomy.  x ≟ z1 gives lt, eq, or gt.  The gt case
-- contradicts x ≤ z1, by ≤→≯.
≡z1-or-<z1 : ∀ x → z0 ≤r x → x ≤r z1 → (x ≡ z1) ⊎ (x <r z1)
≡z1-or-<z1 x _ x≤1 with x QO.≟ z1
... | QO.lt x<1 = inr x<1
... | QO.eq x≡1 = inl x≡1
... | QO.gt 1<x = ⊥.rec (QO.≤→≯ x z1 x≤1 1<x)

-- Item 3: a zero sum of non-negatives forces the left summand to
-- be zero.  Trichotomy on a against z0:
--   a < z0:  contradicts z0 ≤ a, by ≤→≯.
--   a ≡ z0:  done.
--   a > z0:  0 < a and 0 ≤ b give 0 < a + b, by <r-+-pos-l above.
--            But a + b ≡ z0, so 0 < z0, which <r-irrefl refutes.
+r-eq-z0-l : ∀ a b → z0 ≤r a → z0 ≤r b → a +r b ≡ z0 → a ≡ z0
+r-eq-z0-l a b z0≤a z0≤b a+b≡0 with a QO.≟ z0
... | QO.lt a<0 = ⊥.rec (QO.≤→≯ z0 a z0≤a a<0)
... | QO.eq a≡0 = a≡0
... | QO.gt z0<a = ⊥.rec (<r-irrefl z0 (subst (z0 <r_) a+b≡0 (<r-+-pos-l {a} {b} z0<a z0≤b)))

-- Item 6: positivity of the left factor of a product.
-- From 0 ≤ a and 0 < a·b, derive 0 < a.
-- Trichotomy on a against z0:
--   a < 0:  contradicts 0 ≤ a.
--   a ≡ 0:  then a·b ≡ 0·b ≡ 0, which contradicts 0 < a·b.
--   a > 0:  done.
<r-·-pos-factor-l : ∀ {a b} → z0 ≤r a → z0 <r (a ·r b) → z0 <r a
<r-·-pos-factor-l {a} {b} z0≤a 0<ab with a QO.≟ z0
... | QO.lt a<0 = ⊥.rec (QO.≤→≯ z0 a z0≤a a<0)
... | QO.gt z0<a = z0<a
... | QO.eq a≡0 =
  ⊥.rec (<r-irrefl z0
    (subst (z0 <r_)
      (cong (_·r b) a≡0 ∙ ·r-AnnihL b)
      0<ab))

-- Item 7: positivity of the complement.
-- x < z1 → z0 < 1-r x = z1 + (-x).
-- From x < z1, by <-+o on the right, x + (-x) < z1 + (-x).
-- And x + (-x) ≡ z0, by +r-inv.  So z0 < z1 + (-x) = 1-r x.
<r-z1→pos-1-r : ∀ {x} → x <r z1 → z0 <r (1-r x)
<r-z1→pos-1-r {x} x<1 =
  subst2 _<r_ (+r-inv x) refl step
  where
    -- x + (-x) < z1 + (-x), via <-+o.
    step : (x +r (-r x)) <r (z1 +r (-r x))
    step = QO.<-+o x z1 (-r x) x<1

-- ============================================================
-- The remaining two postulates require real ℚ division.  With
-- the trivial `_/r_ _ _ = z0` they are false: (x ·r y) /r y
-- reduces to z0 instead of x.  To discharge them one would
-- define a real division on ℚ, using the field structure on the
-- QuoQ representation, or a SetQuotient-level inverse
-- construction.
--
-- The convex framework above WeightQ.agda does not depend on
-- these two identities being correct.  They are used only inside
-- Bayesian-style derivations, and the convex framework re-derives
-- those without them.  Removing the defensive `_/r_` is a
-- separate refactoring.
-- ============================================================
-- ============================================================
-- Derived: the round-trip identities for honest division.
--
-- These were postulated while _/r_ was the trivial z0 stub.
-- _/r_ is now honest division, built on the ℚ-CommRing inverse,
-- so both follow directly:
--   ·r-/r-pos = ·-/r-non-zero (via pos→non-zero)
--   /r-·r-pos = /r-·-non-zero (via pos→non-zero)
-- See WeightQ-Discharge-Division.agda for the construction.
-- ============================================================
·r-/r-pos : ∀ {y} → z0 <r y → ∀ x → (x ·r y) /r y ≡ x
·r-/r-pos {y} 0<y x = ·r-/r-pos-derived {y = y} 0<y x

/r-·r-pos : ∀ {y} → z0 <r y → ∀ x → (x /r y) ·r y ≡ x
/r-·r-pos {y} 0<y x = /r-·r-pos-derived {y = y} 0<y x

-- ============================================================
-- /r bound discharges, derived from the honest-division bounds.
-- They remove the role of /r-bound-{l,u}-defensive in
-- _/wPf_⟨_,_⟩.
-- ============================================================
open WeightQ-Discharge-Division using (honest/r-lb; honest/r-ub)

/r-pos-bound-l : ∀ x y → z0 ≤r x → z0 <r y → z0 ≤r (x /r y)
/r-pos-bound-l x y 0≤x 0<y = honest/r-lb x y 0≤x 0<y

/r-pos-bound-u : ∀ x y → x ≤r y → z0 <r y → (x /r y) ≤r z1
/r-pos-bound-u x y x≤y 0<y = honest/r-ub x y x≤y 0<y

-- z0-decide: trichotomy on non-negative ℚ.
z0-decide : ∀ x → z0 ≤r x → (x ≡ z0) ⊎ (z0 <r x)
z0-decide x 0≤x with x QO.≟ z0
... | QO.lt x<0 = ⊥.rec (QO.≤→≯ z0 x 0≤x x<0)
... | QO.eq x≡0 = inl x≡0
... | QO.gt 0<x = inr 0<x

-- ≤r-+-cancel-r: a + c ≤r b + c → a ≤r b.  Cubical's
-- ≤-o+-cancel proves this, once the operands are reordered into
-- o + m form.
≤r-+-cancel-r : ∀ a b c → (a +r c) ≤r (b +r c) → a ≤r b
≤r-+-cancel-r a b c h =
  QO.≤-o+-cancel a b c (subst2 _≤r_ (+r-comm a c) (+r-comm b c) h)

-- ============================================================
-- Verification.  Every postulate of the abstract "ordered
-- field" interface of WeightQ.agda now has a concrete definition
-- or theorem above.  The 5 remaining ℝ-level laws (<r-irrefl,
-- ≡z1-or-<z1, +r-eq-z0-l, ·r-/r-pos, /r-·r-pos) are discharged
-- as well.  All are proved for ℚ, and the two division laws are
-- proved in WeightQ-Discharge-Division.  Nothing here is
-- postulated.
--
-- The full inventory of discharged WeightQ ℝ-postulates:
--   ℝ, isSet-ℝ          ✓ (= ℚ, isSetℚ)
--   z0, z1              ✓ (= [pos 0/1], [pos 1/1])
--   _+r_, _·r_, -r_     ✓ (= QP._+_, QP._·_, QP.-_)
--   _≤r_, _<r_          ✓ (= QO._≤_, QO._<_)
--   isProp-≤r, isProp-<r ✓ (from QO.isProp≤, QO.isProp<)
--   +r-comm, ..., +r-inv ✓ (from QP.+Comm, ..., +InvR)
--   ·r-comm, ..., ·r-distL ✓ (from QP.·Comm, ..., ·DistR+)
--   ≤r-refl, ≤r-trans   ✓ (from QO.isRefl≤, isTrans≤)
--   z0≤z1, z0<z1        ✓ (from ℤO.zero-≤pos, (0, refl))
--   <r-implies-≤r       ✓ (from QO.<Weaken≤)
--   ≤r-+-mono           ✓ (from QO.≤Monotone+)
--   ≤r-·-mono           ✓ (proven via QO.≤-·o + transitivity)
--   <r-·-pos            ✓ (proven via QO.<-·o + ·r-AnnihL)
--   <r-+-pos-l          ✓ (proven via QO.<-o+ + isTrans≤<)
--   isProp-z0≤          ✓ (from QO.isProp≤)
--   isProp-x≤z1         ✓ (from QO.isProp≤)
--   1-r, 1-r-def        ✓ (concrete definition)
--   _/r_                ✓ (honest ℚ division; see WeightQ-Discharge-Division)
--
-- Total: 28 of 28 WeightQ ℝ-interface postulates discharged.
-- WeightQ-Discharge.agda contains zero postulates.
-- ============================================================
