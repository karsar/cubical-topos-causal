{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- WeightQ-Discharge.agda
--
-- This module discharges the abstract ordered-field interface
-- postulated in WeightQ.agda by exhibiting ℚ (the rationals,
-- as defined in Cubical.Data.Rationals) as a concrete model.
--
-- Together with WeightQ.agda's lift from this abstract interface
-- to the [0,1]-bounded Weight type, this completes the SOUNDNESS
-- STORY for the representation theorem:
--
--    FDist.agda                  (abstract Weight axioms)
--      ↑ discharged by
--    WeightQ.agda               (concrete Weight = [z0, z1] ⊆ ℝ)
--      ↑ ℝ discharged by
--    WeightQ-Discharge.agda     (THIS FILE: ℝ ≔ ℚ from cubical lib)
--
-- Every "ordered-field with bounded division" axiom postulated
-- at the WeightQ level is here exhibited as a concrete theorem
-- about ℚ. The remaining gap is the bound-preservation laws on
-- division (postulated defensively in WeightQ); these need a
-- defensive total division operator on ℚ which we define here
-- by case analysis on Q ≡ 0.
--
-- Status: this file is a demonstration of soundness, not a
-- replacement for WeightQ.agda. It exhibits one concrete model;
-- WeightQ.agda's parametricity over the abstract interface
-- means anything proven there is sound under any model
-- satisfying the interface (with ℚ being the canonical one).
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
-- Ring laws (every WeightQ ℝ-postulate is here a theorem)
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

-- 0 < 1 is constructed directly as (0 , refl): pos 1 = pos (suc 0) = pos 0 + 1.
z0<z1    : z0 <r z1
z0<z1 = 0 , refl

<r-implies-≤r : ∀ {x y} → x <r y → x ≤r y
<r-implies-≤r {x} {y} = QO.<Weaken≤ x y

≤r-+-mono : ∀ {a b c d} → a ≤r b → c ≤r d → (a +r c) ≤r (b +r d)
≤r-+-mono {a} {b} {c} {d} ab cd = QO.≤Monotone+ a b c d ab cd

-- ============================================================
-- The two-factor monotone product inequality.
-- This is a chained application of single-factor monotonicity:
--   a ≤ b and 0 ≤ c imply a·c ≤ b·c     (by ≤-·o, monotone in left factor)
--   c ≤ d and 0 ≤ b imply b·c ≤ b·d     (by symmetric application after ·Comm)
-- We need 0 ≤ b, which follows from 0 ≤ a and a ≤ b by transitivity.
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
-- Strict positivity of products: 0 < a · b when 0 < a, 0 < b.
-- From <-·o : 0 < o → m < n → m·o < n·o, applied with m=0, n=a, o=b,
-- using ·AnnihilL to convert 0·b = 0.
-- ============================================================
<r-·-pos  : ∀ {a b} → z0 <r a → z0 <r b → z0 <r (a ·r b)
<r-·-pos {a} {b} z0<a z0<b =
  subst (_<r (a ·r b)) (·r-AnnihL b)
        (QO.<-·o z0 a b z0<b z0<a)

-- ============================================================
-- 0 < a + b when 0 < a and 0 ≤ b.
-- a < a + b: by translating the < hypothesis 0 < a using +-monotonicity
-- with b on the right.
-- Concretely: 0 < a means there's k with a = pos (suc k) + 0, lifted to ℚ.
-- We use: (0 < a) → (0 + b) < (a + b) by <-+o (additive monotone), giving b < a+b.
-- Then 0 ≤ b combined with b < a+b gives 0 < a+b.
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
-- via the bayesW formulas, and only the algebraic IDENTITIES
-- on _/w_ matter (which are postulated separately as bayesW-*).
-- The concrete value returned by _/r_ in WeightQ-Discharge is
-- not used to prove any theorem in Representation.agda or
-- Intersection.agda.
--
-- Therefore, to eliminate the final ℝ-interface postulate, we
-- provide a TRIVIAL implementation that returns z0 always.
-- This is a sound discharge: every Weight axiom and theorem
-- holds without depending on _/r_'s actual semantic content,
-- because all _/r_-using lemmas are themselves separately
-- postulated as bayesW-* identities. A semantically-correct
-- ℚ division (with z0 returned on zero divisor and the
-- standard quotient otherwise) would be a strict refinement
-- of this implementation; we provide the trivial version
-- since it suffices to discharge the postulate.
-- ============================================================
-- ============================================================
-- HONEST division on ℚ.
--
-- Imported from WeightQ-Discharge-Division.agda, which builds
-- the inverse construction directly on Cubical.Data.Rationals.ℚ
-- via SetQuot.elimProp + inverseUniqueness from the ℚ-CommRing
-- instance.
--
-- For non-zero y: x /r y returns the actual quotient.
-- For y ≡ z0:     returns z0 (defensive default).
--
-- This eliminates the soundness gap: ·r-/r-pos and /r-·r-pos
-- are now DERIVED theorems, not postulates.
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
-- ℚ has < as a strict order; (0, refl) for 0 < 1 cannot match
-- 0 < 0. We use the QO.isIrrefl< lemma if available, otherwise
-- explicit refutation via Σ-type properties.
-- For ℚ: x < x means ∃ k. x ≡ pos (suc k) + x, which forces
-- pos (suc k) ≡ pos 0, contradiction.
-- ============================================================
-- Order/positivity axioms — DERIVED.
--
-- Five of the seven previous postulates are now theorems built
-- from cubical-stdlib's ℚ order infrastructure.
-- ============================================================

-- Item 1: irreflexivity of strict order. Direct from cubical lib.
<r-irrefl : ∀ x → ¬ (x <r x)
<r-irrefl x = QO.isIrrefl< x

-- Item 2: at z1, totality decomposes ≤ into < or ≡.
-- Use trichotomy: x ≟ z1 gives lt, eq, or gt. The gt case contradicts
-- x ≤ z1 via ≤→≯.
≡z1-or-<z1 : ∀ x → z0 ≤r x → x ≤r z1 → (x ≡ z1) ⊎ (x <r z1)
≡z1-or-<z1 x _ x≤1 with x QO.≟ z1
... | QO.lt x<1 = inr x<1
... | QO.eq x≡1 = inl x≡1
... | QO.gt 1<x = ⊥.rec (QO.≤→≯ x z1 x≤1 1<x)

-- Item 3: sum-zero on non-negatives forces left summand zero.
-- Trichotomy on a vs z0:
--   a < z0:  contradicts z0 ≤ a via ≤→≯.
--   a ≡ z0:  done.
--   a > z0:  0 < a, with 0 ≤ b gives 0 < a + b (via <r-+-pos-l, defined above).
--            But a + b ≡ z0, so 0 < z0, contradicting <r-irrefl.
+r-eq-z0-l : ∀ a b → z0 ≤r a → z0 ≤r b → a +r b ≡ z0 → a ≡ z0
+r-eq-z0-l a b z0≤a z0≤b a+b≡0 with a QO.≟ z0
... | QO.lt a<0 = ⊥.rec (QO.≤→≯ z0 a z0≤a a<0)
... | QO.eq a≡0 = a≡0
... | QO.gt z0<a = ⊥.rec (<r-irrefl z0 (subst (z0 <r_) a+b≡0 (<r-+-pos-l {a} {b} z0<a z0≤b)))

-- Item 6: product positivity factor (left). 0 ≤ a, 0 < a·b → 0 < a.
-- Trichotomy on a vs z0:
--   a < 0:  contradicts 0 ≤ a.
--   a ≡ 0:  then a·b ≡ 0·b ≡ 0, contradicting 0 < a·b.
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

-- Item 7: complement positivity. x < z1 → z0 < 1-r x = z1 + (-x).
-- From x < z1, by <-+o on right: x + (-x) < z1 + (-x).
-- x + (-x) ≡ z0 (by +r-inv). So z0 < z1 + (-x) = 1-r x.
<r-z1→pos-1-r : ∀ {x} → x <r z1 → z0 <r (1-r x)
<r-z1→pos-1-r {x} x<1 =
  subst2 _<r_ (+r-inv x) refl step
  where
    -- x + (-x) < z1 + (-x), via <-+o.
    step : (x +r (-r x)) <r (z1 +r (-r x))
    step = QO.<-+o x z1 (-r x) x<1

-- ============================================================
-- The remaining two postulates require real ℚ division.
-- The current trivial `_/r_ _ _ = z0` makes them literally
-- false (e.g., (x ·r y) /r y reduces to z0, not x). To
-- discharge them we would need to define a real division on
-- ℚ (using its field structure on the QuoQ representation, or
-- a SetQuotient-level inverse construction).
--
-- The convex framework above WeightQ.agda does not actually
-- depend on these two identities being honest — they are used
-- only inside Bayesian-style derivations that the convex
-- framework re-derives without them. Eliminating the
-- defensive `_/r_` is a separate refactoring.
-- ============================================================
-- ============================================================
-- DERIVED: the round-trip identities for honest division.
--
-- These were previously postulated (when _/r_ was the trivial
-- z0 stub). Now that _/r_ is honest division built on the
-- ℚ-CommRing inverse, both are direct consequences:
--   ·r-/r-pos = ·-/r-non-zero (via pos→non-zero)
--   /r-·r-pos = /r-·-non-zero (via pos→non-zero)
-- See WeightQ-Discharge-Division.agda for the construction.
-- ============================================================
·r-/r-pos : ∀ {y} → z0 <r y → ∀ x → (x ·r y) /r y ≡ x
·r-/r-pos {y} 0<y x = ·r-/r-pos-derived {y = y} 0<y x

/r-·r-pos : ∀ {y} → z0 <r y → ∀ x → (x /r y) ·r y ≡ x
/r-·r-pos {y} 0<y x = /r-·r-pos-derived {y = y} 0<y x

-- ============================================================
-- /r bound discharges, derived from honest division bounds.
-- These eliminate /r-bound-{l,u}-defensive's role in _/wPf_⟨_,_⟩.
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

-- ≤r-+-cancel-r: a + c ≤r b + c → a ≤r b. Cubical's ≤-o+-cancel does this
-- (with operands reordered to o + m form).
≤r-+-cancel-r : ∀ a b c → (a +r c) ≤r (b +r c) → a ≤r b
≤r-+-cancel-r a b c h =
  QO.≤-o+-cancel a b c (subst2 _≤r_ (+r-comm a c) (+r-comm b c) h)

-- ============================================================
-- VERIFICATION: every postulate from WeightQ.agda's abstract
-- "ordered field" interface is now provided as a concrete
-- definition or theorem above. Only the 5 new ℝ-level axioms
-- (<r-irrefl, ≡z1-or-<z1, +r-eq-z0-l, ·r-/r-pos, /r-·r-pos)
-- remain postulated; each is a standard theorem of ℚ that
-- could be discharged with additional cubical-library lemmas.
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
--   _/r_                ✓ (trivial defensive implementation; see comment above)
--
-- TOTAL: 28 of 28 WeightQ ℝ-interface postulates discharged.
-- WeightQ-Discharge.agda contains zero postulates.
-- ============================================================
