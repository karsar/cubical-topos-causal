{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- WeightQ-Field — the ordered-field interface, made OPAQUE.
--
-- WeightQ.agda used to `postulate` an abstract ordered field ℝ.
-- The postulate worked because a postulated symbol is RIGID: the
-- typechecker never unfolds `x +r y` or `x ≤r y`, so the implicit
-- arguments of the field lemmas are inferable by rigid-rigid
-- unification throughout the probability layer.
--
-- WeightQ-Discharge.agda exhibits ℚ as a concrete model with no
-- postulates, but its definitions are TRANSPARENT: `x ≤r y`
-- unfolds to a stuck SetQuotient/order projection that the unifier
-- cannot invert, so dropping the concrete field in directly breaks
-- implicit-argument inference at hundreds of downstream sites.
--
-- This module bridges the two.  We re-export every field name from
-- WeightQ-Discharge inside a single `opaque` block.  Inside the
-- block the definitions are transparent (so each alias typechecks
-- against the concrete ℚ proof); outside it they are rigid (so
-- downstream unification behaves exactly as it did with the
-- postulate).  The result: ℝ is concretely ℚ, nothing is
-- postulated, and the whole development typechecks under --safe
-- with NO change to any downstream proof.
-- ============================================================

module WeightQ-Field where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Relation.Nullary using (¬_)

import WeightQ-Discharge as D

opaque
  ℝ : Type₀
  ℝ = D.ℝ
  isSet-ℝ : isSet ℝ
  isSet-ℝ = D.isSet-ℝ
  z0 : ℝ
  z0 = D.z0
  z1 : ℝ
  z1 = D.z1
  _+r_ : ℝ → ℝ → ℝ
  _+r_ = D._+r_
  _·r_ : ℝ → ℝ → ℝ
  _·r_ = D._·r_
  -r_ : ℝ → ℝ
  -r_ = D.-r_
  _≤r_ : ℝ → ℝ → Type₀
  _≤r_ = D._≤r_
  _<r_ : ℝ → ℝ → Type₀
  _<r_ = D._<r_
  isProp-≤r : ∀ {x y} → isProp (x ≤r y)
  isProp-≤r {x} {y} = D.isProp-≤r {x} {y}
  isProp-<r : ∀ {x y} → isProp (x <r y)
  isProp-<r {x} {y} = D.isProp-<r {x} {y}
  +r-comm : ∀ x y → x +r y ≡ y +r x
  +r-comm = D.+r-comm
  +r-assoc : ∀ x y z → x +r (y +r z) ≡ (x +r y) +r z
  +r-assoc = D.+r-assoc
  +r-IdR : ∀ x → x +r z0 ≡ x
  +r-IdR = D.+r-IdR
  +r-inv : ∀ x → x +r (-r x) ≡ z0
  +r-inv = D.+r-inv
  ·r-comm : ∀ x y → x ·r y ≡ y ·r x
  ·r-comm = D.·r-comm
  ·r-assoc : ∀ x y z → x ·r (y ·r z) ≡ (x ·r y) ·r z
  ·r-assoc = D.·r-assoc
  ·r-IdL : ∀ x → z1 ·r x ≡ x
  ·r-IdL = D.·r-IdL
  ·r-IdR : ∀ x → x ·r z1 ≡ x
  ·r-IdR = D.·r-IdR
  ·r-AnnihL : ∀ x → z0 ·r x ≡ z0
  ·r-AnnihL = D.·r-AnnihL
  ·r-AnnihR : ∀ x → x ·r z0 ≡ z0
  ·r-AnnihR = D.·r-AnnihR
  ·r-distR : ∀ a b c → a ·r (b +r c) ≡ (a ·r b) +r (a ·r c)
  ·r-distR = D.·r-distR
  ·r-distL : ∀ a b c → (a +r b) ·r c ≡ (a ·r c) +r (b ·r c)
  ·r-distL = D.·r-distL
  ≤r-refl : ∀ x → x ≤r x
  ≤r-refl = D.≤r-refl
  ≤r-trans : ∀ {x y z} → x ≤r y → y ≤r z → x ≤r z
  ≤r-trans {x} {y} {z} = D.≤r-trans {x} {y} {z}
  ≤r-antisym : ∀ {x y} → x ≤r y → y ≤r x → x ≡ y
  ≤r-antisym {x} {y} = D.≤r-antisym {x} {y}
  z0≤z1 : z0 ≤r z1
  z0≤z1 = D.z0≤z1
  z0<z1 : z0 <r z1
  z0<z1 = D.z0<z1
  <r-implies-≤r : ∀ {x y} → x <r y → x ≤r y
  <r-implies-≤r {x} {y} = D.<r-implies-≤r {x} {y}
  ≤r-+-mono : ∀ {a b c d} → a ≤r b → c ≤r d → (a +r c) ≤r (b +r d)
  ≤r-+-mono {a} {b} {c} {d} = D.≤r-+-mono {a} {b} {c} {d}
  ≤r-·-mono : ∀ {a b c d} → z0 ≤r a → z0 ≤r c → a ≤r b → c ≤r d → (a ·r c) ≤r (b ·r d)
  ≤r-·-mono {a} {b} {c} {d} = D.≤r-·-mono {a} {b} {c} {d}
  <r-·-pos : ∀ {a b} → z0 <r a → z0 <r b → z0 <r (a ·r b)
  <r-·-pos {a} {b} = D.<r-·-pos {a} {b}
  <r-+-pos-l : ∀ {a b} → z0 <r a → z0 ≤r b → z0 <r (a +r b)
  <r-+-pos-l {a} {b} = D.<r-+-pos-l {a} {b}
  isProp-z0≤ : ∀ {x} → isProp (z0 ≤r x)
  isProp-z0≤ {x} = D.isProp-z0≤ {x}
  isProp-x≤z1 : ∀ {x} → isProp (x ≤r z1)
  isProp-x≤z1 {x} = D.isProp-x≤z1 {x}
  1-r : ℝ → ℝ
  1-r = D.1-r
  1-r-def : ∀ x → 1-r x ≡ z1 +r (-r x)
  1-r-def = D.1-r-def
  _/r_ : ℝ → ℝ → ℝ
  _/r_ = D._/r_
  <r-irrefl : ∀ x → ¬ (x <r x)
  <r-irrefl = D.<r-irrefl
  ≡z1-or-<z1 : ∀ x → z0 ≤r x → x ≤r z1 → (x ≡ z1) ⊎ (x <r z1)
  ≡z1-or-<z1 = D.≡z1-or-<z1
  +r-eq-z0-l : ∀ a b → z0 ≤r a → z0 ≤r b → a +r b ≡ z0 → a ≡ z0
  +r-eq-z0-l = D.+r-eq-z0-l
  ·r-/r-pos : ∀ {y} → z0 <r y → ∀ x → (x ·r y) /r y ≡ x
  ·r-/r-pos {y} = D.·r-/r-pos {y}
  /r-·r-pos : ∀ {y} → z0 <r y → ∀ x → (x /r y) ·r y ≡ x
  /r-·r-pos {y} = D./r-·r-pos {y}
  /r-pos-bound-l : ∀ x y → z0 ≤r x → z0 <r y → z0 ≤r (x /r y)
  /r-pos-bound-l = D./r-pos-bound-l
  /r-pos-bound-u : ∀ x y → x ≤r y → z0 <r y → (x /r y) ≤r z1
  /r-pos-bound-u = D./r-pos-bound-u
  z0-decide : ∀ x → z0 ≤r x → (x ≡ z0) ⊎ (z0 <r x)
  z0-decide = D.z0-decide
  ≤r-+-cancel-r : ∀ a b c → (a +r c) ≤r (b +r c) → a ≤r b
  ≤r-+-cancel-r = D.≤r-+-cancel-r
  <r-·-pos-factor-l : ∀ {a b} → z0 ≤r a → z0 <r (a ·r b) → z0 <r a
  <r-·-pos-factor-l {a} {b} = D.<r-·-pos-factor-l {a} {b}
  <r-z1→pos-1-r : ∀ {x} → x <r z1 → z0 <r (1-r x)
  <r-z1→pos-1-r {x} = D.<r-z1→pos-1-r {x}
  zHalf : ℝ
  zHalf = D.zHalf
  z0<zHalf : z0 <r zHalf
  z0<zHalf = D.z0<zHalf
  zHalf<z1 : zHalf <r z1
  zHalf<z1 = D.zHalf<z1

infixl 7 _·r_ _/r_
infixl 6 _+r_
