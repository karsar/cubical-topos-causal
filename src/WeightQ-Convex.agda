{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- WeightQ-Convex.agda
--
-- Discharge layer for FDist-Convex.agda's algebra postulates.
--
-- This module provides concrete definitions of the convex-algebra
-- operations (mix-w, ≤w, normalize) on top of WeightQ.agda's
-- Weight type (which is itself ℝ ∩ [0,1] for an abstract ordered
-- field ℝ; canonical instance ℚ in WeightQ-Discharge.agda). All
-- the convex-algebra axioms postulated by FDist-Convex.agda are
-- proved here as theorems.
--
-- Specifically:
--   * mix-w p a b := (p *w a) +w ((1-w p) *w b)        (derived)
--   * x ≤w y      := val x ≤r val y                    (derived)
--   * normalize num den _ _ := num /w den              (derived)
--
-- All FDist-Convex.agda's algebra axioms become theorems, lifted
-- from ℝ-level ring identities via WeightPath.
-- ============================================================

module WeightQ-Convex where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as Empty using (⊥)

-- Re-export everything from WeightQ that we want to make available
-- as part of the convex-framing interface.
open import WeightQ public
  using ( Weight ; w0 ; w1 ; isSetWeight ; _*w_ ; _+w_⟨_⟩ ; 1-w_
        ; *w-comm ; *w-assoc ; *w-1 ; *w-0
        ; *w-distrib-+w
        ; +w-comm ; +w-assoc ; +w-0
        ; 1-w-invol ; 1-w-0 ; 1-w-1
        ; Pos ; isProp-Pos ; pos-w1
        ; pos-+w-l ; pos-*w ; pos-*w-factor-l
        ; weight-trichotomy ; w0≢w1 ; ¬Pos-w0
        ; compl ; weighted-idem
        ; +w-cancel-l
        ; mix-bound ; +w-IdR-bound ; compl-bound ; weighted-idem-bound
        )

-- We need a few WeightQ-internal items not exported by the using-list
-- above; pull them in privately.
open import WeightQ
  using ( val ; lb ; ub ; mkW ; WeightPath
        ; ℝ ; z0 ; z1 ; _+r_ ; _·r_ ; -r_ ; _≤r_ ; _<r_ ; 1-r ; _/r_
        ; isProp-≤r ; ≤r-refl ; ≤r-trans ; ≤r-antisym ; ≤r-+-mono ; ≤r-·-mono
        ; +r-comm ; +r-assoc ; +r-IdR ; +r-inv
        ; ·r-comm ; ·r-assoc ; ·r-IdL ; ·r-IdR ; ·r-AnnihL ; ·r-AnnihR
        ; ·r-distR ; ·r-distL
        ; 1-r-def ; +r-compl-ℝ ; weighted-idem-ℝ ; ·r-interchange-eq
        ; -r-distrib ; isProp-z0≤ ; isProp-x≤z1
        ; z0≤z1 ; +r-cancel-l-ℝ
        )

-- ============================================================
-- Section 1: derived operations.
-- ============================================================

-- Convex combination, derived from _+w_⟨_⟩ and *w.
-- The bound (val (p *w a) +r val ((1-w p) *w b)) ≤r z1 holds
-- by mix-bound (a convex combination is bounded by 1).
mix-w : Weight → Weight → Weight → Weight
mix-w p a b = (p *w a) +w ((1-w p) *w b) ⟨ mix-bound p a b ⟩

-- Order on Weight, lifted from ℝ ordering.
_≤w_ : Weight → Weight → Type₀
x ≤w y = val x ≤r val y
infix 4 _≤w_

isProp-≤w : ∀ {x y} → isProp (x ≤w y)
isProp-≤w = isProp-≤r

-- Normalize: PARTIAL operator using _/wPf with both preconditions
-- explicit. This is the migration target for safe Bayesian-style
-- division. Currently uses the same trivial _/r_ stub internally
-- as _/w_; the value-level correctness depends on the same
-- postulates (·r-/r-pos, /r-·r-pos in WeightQ-Discharge) and is
-- thus subject to the same DEEPER issue documented in SOUNDNESS.md
-- regarding the structural inconsistency of those postulates with
-- the trivial _/r_ stub.
--
-- The signature improvement is real (preconditions are now explicit
-- and obligations cannot be silently violated at the call site),
-- but full soundness requires an honest ℚ division, which is the
-- next planned step.
normalize : (num den : Weight) → Pos den → num ≤w den → Weight
normalize num den pd le = num /wPf den ⟨ pd , le ⟩
  where open import WeightQ using (_/wPf_⟨_,_⟩)

-- ============================================================
-- Section 2: convex-algebra axioms (Stone 1949).
-- ============================================================

-- mix-w-comm: mix-w p a b ≡ mix-w (1-w p) b a.
-- Lifted directly to ℝ-level via WeightPath:
--   val LHS = (val p · val a) + (val (1-p) · val b)
--   val RHS = (val (1-p) · val b) + (val (1-(1-p)) · val a)
-- Equal by +r-comm + 1-w-invol.
mix-w-comm : ∀ p a b → mix-w p a b ≡ mix-w (1-w p) b a
mix-w-comm p a b = WeightPath
  (+r-comm (val p ·r val a) (val (1-w p) ·r val b)
   ∙ cong (λ z → (val (1-w p) ·r val b) +r (z ·r val a)) (cong val (sym (1-w-invol p))))

-- mix-w-idem: mix-w p a a ≡ a.
-- = p·a + (1-p)·a = (p + (1-p))·a = a   [by weighted-idem].
mix-w-idem : ∀ p a → mix-w p a a ≡ a
mix-w-idem p a = WeightPath (weighted-idem-ℝ (val p) (val a))

-- mix-w-bdy0: mix-w w0 a b ≡ b.
-- Lifted to ℝ-level via WeightPath. The ℝ-level fact is:
--   (z0 · val a) + (val (1-w w0) · val b) ≡ val b
-- proved by ·r-bdy0-eq.
mix-w-bdy0 : ∀ a b → mix-w w0 a b ≡ b
mix-w-bdy0 a b =
  WeightPath (·r-bdy0-eq (val a) (val b))
  where
    open import WeightQ using (·r-bdy0-eq)

-- mix-w-bdy1 derivable from mix-w-comm + mix-w-bdy0 + 1-w-1.
mix-w-bdy1 : ∀ a b → mix-w w1 a b ≡ a
mix-w-bdy1 a b =
  mix-w-comm w1 a b
  ∙ cong (λ q → mix-w q b a) 1-w-1
  ∙ mix-w-bdy0 b a

-- mix-w-interchange: this is exactly the ·r-interchange-eq lemma
-- already proven in WeightQ.agda, lifted to Weight via WeightPath.
-- Note: the arg order in ·r-interchange-eq matches mix-w's pattern after
-- swapping b ↔ c (because LHS of mix-w-interchange has (q a b)(q c d) but
-- ·r-interchange-eq's LHS has p·((q·_₁)+(1-q)·_₃) + (1-p)·((q·_₂)+(1-q)·_₄)).
mix-w-interchange : ∀ p q a b c d
  → mix-w p (mix-w q a b) (mix-w q c d)
  ≡ mix-w q (mix-w p a c) (mix-w p b d)
mix-w-interchange p q a b c d =
  WeightPath (·r-interchange-eq (val p) (val q) (val a) (val c) (val b) (val d))

-- ============================================================
-- Section 3: Multiplication & complement axioms (mostly from WeightQ).
-- ============================================================

-- *w-distrib-mix-w: a *w (mix-w p x y) ≡ mix-w p (a *w x) (a *w y).
-- = a · (p·x + (1-p)·y)
-- Lifted to ℝ via WeightPath. The ℝ-level identity is just
-- ·r-distR (val a) (val p ·r val x) (val (1-w p) ·r val y),
-- followed by ·r-assoc/·r-comm rearrangements.
*w-distrib-mix-w : ∀ a p x y → a *w (mix-w p x y) ≡ mix-w p (a *w x) (a *w y)
*w-distrib-mix-w a p x y = WeightPath
  (·r-distR (val a) (val p ·r val x) (val (1-w p) ·r val y)
   ∙ cong₂ _+r_
       (·r-assoc (val a) (val p) (val x)
        ∙ cong (_·r val x) (·r-comm (val a) (val p))
        ∙ sym (·r-assoc (val p) (val a) (val x)))
       (·r-assoc (val a) (val (1-w p)) (val y)
        ∙ cong (_·r val y) (·r-comm (val a) (val (1-w p)))
        ∙ sym (·r-assoc (val (1-w p)) (val a) (val y))))

-- 1-w-mix-w: 1-w (mix-w p a b) ≡ mix-w p (1-w a) (1-w b).
-- This is the involution-distributes-over-mix axiom.
-- Proof at ℝ level:
--   1 - (p·a + (1-p)·b)
--     = 1 - p·a - (1-p)·b                  [-r-distrib]
--     = 1 + (-1)·(p·a + (1-p)·b)
--   p·(1-a) + (1-p)·(1-b)
--     = p·1 - p·a + (1-p)·1 - (1-p)·b      [·r-distR + 1-r-def]
--     = (p + (1-p))·1 - p·a - (1-p)·b
--     = 1 - p·a - (1-p)·b
-- Equal. We do this at the ℝ level with a focused lemma.
  --     = 1 + (-(p·x) + -((1-p)·y))                [weighted-idem on first part]
  --     = 1 - (p·x + (1-p)·y)                      [-r-distrib]
  --     = 1-r (p·x + (1-p)·y)                      [1-r-def]

-- For ·r with -r:  a ·r (-r b) ≡ -r (a ·r b).
·r-neg : ∀ a b → a ·r (-r b) ≡ -r (a ·r b)
·r-neg a b =
  sym (+r-IdR (a ·r (-r b)))
  ∙ cong ((a ·r (-r b)) +r_) (sym (+r-inv (a ·r b)))
  ∙ +r-assoc (a ·r (-r b)) (a ·r b) (-r (a ·r b))
  ∙ cong (_+r (-r (a ·r b)))
         (sym (·r-distR a (-r b) b)
          ∙ cong (a ·r_) (+r-comm (-r b) b ∙ +r-inv b)
          ∙ ·r-AnnihR a)
  ∙ +r-comm z0 (-r (a ·r b))
  ∙ +r-IdR (-r (a ·r b))

-- a ·r (1-r b) ≡ a +r (-r (a ·r b)) — useful for skew-associativity.
·r-1-r : ∀ a b → a ·r (1-r b) ≡ a +r (-r (a ·r b))
·r-1-r a b =
  cong (a ·r_) (1-r-def b)
  ∙ ·r-distR a z1 (-r b)
  ∙ cong₂ _+r_ (·r-IdR a) (·r-neg a b)

-- 1-r distributes over +r: 1-r (a +r b) ≡ (1-r a) +r (-r b).
1-r-+r : ∀ a b → 1-r (a +r b) ≡ (1-r a) +r (-r b)
1-r-+r a b =
  1-r-def (a +r b)
  ∙ cong (z1 +r_) (-r-distrib a b)
  ∙ +r-assoc z1 (-r a) (-r b)
  ∙ cong (_+r (-r b)) (sym (1-r-def a))

-- ============================================================
-- Section 3a: 1-w-mix-w (preserved private helper).
-- ============================================================

-- 1-w-mix-w: 1-w (mix-w p a b) ≡ mix-w p (1-w a) (1-w b).
-- Direct ℝ-level proof.
private
  1-w-mix-w-ℝ : ∀ p a b
    → 1-r ((p ·r a) +r ((1-r p) ·r b))
    ≡ (p ·r (1-r a)) +r ((1-r p) ·r (1-r b))
  1-w-mix-w-ℝ p a b =
    1-r-def ((p ·r a) +r ((1-r p) ·r b))
    ∙ cong (z1 +r_) (-r-distrib (p ·r a) ((1-r p) ·r b))
    ∙ sym (cong (_+r ((-r (p ·r a)) +r (-r ((1-r p) ·r b))))
                (+r-compl-ℝ p))
    ∙ +r-medial p (1-r p) (-r (p ·r a)) (-r ((1-r p) ·r b))
    ∙ cong₂ _+r_
            (cong (p +r_) (sym (·r-neg p a))
             ∙ cong (_+r (p ·r (-r a))) (sym (·r-IdR p))
             ∙ sym (·r-distR p z1 (-r a))
             ∙ cong (p ·r_) (sym (1-r-def a)))
            (cong ((1-r p) +r_) (sym (·r-neg (1-r p) b))
             ∙ cong (_+r ((1-r p) ·r (-r b))) (sym (·r-IdR (1-r p)))
             ∙ sym (·r-distR (1-r p) z1 (-r b))
             ∙ cong ((1-r p) ·r_) (sym (1-r-def b)))
    where
      open import WeightQ using (+r-medial)

1-w-mix-w : ∀ p a b → 1-w (mix-w p a b) ≡ mix-w p (1-w a) (1-w b)
1-w-mix-w p a b = WeightPath (1-w-mix-w-ℝ (val p) (val a) (val b))

-- ============================================================
-- Section 4: order axioms.
-- ============================================================

≤w-refl : ∀ x → x ≤w x
≤w-refl x = ≤r-refl (val x)

≤w-trans : ∀ {x y z} → x ≤w y → y ≤w z → x ≤w z
≤w-trans = ≤r-trans

w0≤w-all : ∀ x → w0 ≤w x
w0≤w-all x = lb x

all-≤w-w1 : ∀ x → x ≤w w1
all-≤w-w1 x = ub x

-- ≤w-antisym derived from ≤r-antisym (which is part of WeightQ.agda's
-- abstract ordered-field interface and discharged in WeightQ-Discharge.agda
-- for ℚ via the cubical library's QO.isAntisym≤).
≤w-antisym : ∀ {x y} → x ≤w y → y ≤w x → x ≡ y
≤w-antisym {x} {y} le1 le2 = WeightPath (≤r-antisym le1 le2)

-- ============================================================
-- Section 5: monotonicity of mix-w.
-- ============================================================

-- mix-w-mono: mix-w is monotone in both arguments (with same weight).
-- Follows from ≤r-+-mono and ≤r-·-mono.
mix-w-mono : ∀ p {a b c d} → a ≤w c → b ≤w d → mix-w p a b ≤w mix-w p c d
mix-w-mono p {a} {b} {c} {d} ac bd =
  ≤r-+-mono
    (≤r-·-mono (lb p) (lb a) (≤r-refl (val p)) ac)
    (≤r-·-mono (lb (1-w p)) (lb b) (≤r-refl (val (1-w p))) bd)

-- mix-w-right-w0: mix-w p a w0 ≡ p *w a.
-- Lifted to ℝ via WeightPath:
--   (val p · val a) +r (val (1-w p) · z0) ≡ val p · val a
-- by ·r-AnnihR + +r-IdR.
mix-w-right-w0 : ∀ p a → mix-w p a w0 ≡ p *w a
mix-w-right-w0 p a = WeightPath
  (cong ((val p ·r val a) +r_) (·r-AnnihR (val (1-w p)))
   ∙ +r-IdR (val p ·r val a))

-- p-≤w-mix-w-w1: p ≤w mix-w p w1 q.
-- val(mix-w p w1 q) = (val p · z1) +r (val(1-w p) · val q)
--                   = val p +r (val(1-w p) · val q)         [·r-IdR]
-- Want: val p ≤r val p +r [val(1-w p) · val q].
-- Since val(1-w p) ≥ z0 and val q ≥ z0, their product ≥ z0.
-- Adding ≥ z0 to val p doesn't decrease.
private
  -- z0 ≤r (a · b) when z0 ≤r a and z0 ≤r b.
  ·r-non-neg : ∀ {a b} → z0 ≤r a → z0 ≤r b → z0 ≤r (a ·r b)
  ·r-non-neg {a} {b} 0≤a 0≤b =
    subst (_≤r (a ·r b)) (·r-AnnihL z0)
          (≤r-·-mono (≤r-refl z0) (≤r-refl z0) 0≤a 0≤b)

p-≤w-mix-w-w1 : ∀ p q → p ≤w (mix-w p w1 q)
p-≤w-mix-w-w1 p q =
  -- We rewrite val(mix-w p w1 q) to (val p +r (val(1-w p) · val q)),
  -- then apply ≤r-+-mono with refl on val p and z0 ≤r (val(1-w p) · val q),
  -- after rewriting val p ≡ val p +r z0.
  subst (val p ≤r_)
        (sym (cong (_+r (val (1-w p) ·r val q)) (·r-IdR (val p))))
        bigger
  where
    nn : z0 ≤r (val (1-w p) ·r val q)
    nn = ·r-non-neg (lb (1-w p)) (lb q)
    -- val p ≡ val p +r z0
    p-≡ : val p ≡ val p +r z0
    p-≡ = sym (+r-IdR (val p))
    -- val p +r z0 ≤r val p +r (val(1-w p) · val q) by ≤r-+-mono.
    bigger : val p ≤r (val p +r (val (1-w p) ·r val q))
    bigger = subst (_≤r (val p +r (val (1-w p) ·r val q)))
                   (sym p-≡)
                   (≤r-+-mono (≤r-refl (val p)) nn)

-- ============================================================
-- Section 6: positivity.
-- ============================================================

-- Note: pos-w1, pos-+w-l, pos-*w, pos-*w-factor-l, ¬Pos-w0,
-- weight-trichotomy, w0≢w1 are all from WeightQ already.

-- ============================================================
-- Section 7: normalize laws.
-- ============================================================

-- normalize-*w: normalize (a *w b) b pb le ≡ a.
-- Uses partial division round-trip directly via *w-/wPf-pos.
open import WeightQ using (_/wPf_⟨_,_⟩; *w-/wPf-pos; /wPf-*w-pos)

normalize-*w : ∀ a b (pb : Pos b) (le : (a *w b) ≤w b)
             → normalize (a *w b) b pb le ≡ a
normalize-*w a b pb le = *w-/wPf-pos b pb a le

-- normalize-*w-back: (normalize num den pd le) *w den ≡ num.
normalize-*w-back : ∀ num den (pd : Pos den) (le : num ≤w den)
                  → (normalize num den pd le) *w den ≡ num
normalize-*w-back num den pd le = /wPf-*w-pos den pd num le

-- ============================================================
-- Section 9: Stone's skew-associativity (mix-w-assoc-pos).
--
-- Statement: mix-w p a (mix-w q b c)
--          ≡ mix-w (s-of p q) (mix-w (r-of p q ps) a b) c
-- where:
--   s-of p q = mix-w p w1 q             (the "weight sum")
--   r-of p q ps = p /w (s-of p q)       (the renormalized inner weight)
--   ps : Pos (s-of p q)
--
-- Proof at ℝ level. Set s = val(s-of p q), r = val(r-of p q ps),
--   p_v = val p, etc. Then:
--   * s_v = p_v + (1-p_v)·q_v               [from s-of definition + ·r-IdR]
--   * r_v = p_v / s_v                        [from r-of definition]
--   * s_v · r_v ≡ p_v                        [/r-·r-pos at positive s_v]
--   * s_v · (1-r_v) ≡ (1-p_v) · q_v          [from above + arithmetic]
--   * 1 - s_v ≡ (1-p_v) · (1-q_v)            [from arithmetic]
-- Both LHS and RHS expand to the same sum p·a + (1-p)q·b + (1-p)(1-q)·c.
-- ============================================================

-- s-of and r-of at the Weight level (used here).
s-of : Weight → Weight → Weight
s-of p q = mix-w p w1 q

-- p ≤w s-of p q (already proven as p-≤w-mix-w-w1 above; renamed here).
p-≤w-s-of : ∀ p q → p ≤w (s-of p q)
p-≤w-s-of = p-≤w-mix-w-w1

-- r-of via normalize.
r-of : ∀ p q → Pos (s-of p q) → Weight
r-of p q ps = normalize p (s-of p q) ps (p-≤w-s-of p q)

-- Helper: val (s-of p q) reduces to (val p) +r ((1-r (val p)) ·r val q).
val-s-of : ∀ p q → val (s-of p q) ≡ (val p) +r ((1-r (val p)) ·r val q)
val-s-of p q = cong (_+r ((1-r (val p)) ·r val q)) (·r-IdR (val p))

-- Helper: val (r-of p q ps) ≡ val p /r val (s-of p q).
val-r-of : ∀ p q (ps : Pos (s-of p q)) → val (r-of p q ps) ≡ val p /r val (s-of p q)
val-r-of p q ps = refl  -- by definition of normalize and /w

-- Lemma A: val(s-of p q) · val(r-of p q ps) ≡ val p.
sof-rof : ∀ p q (ps : Pos (s-of p q))
        → val (s-of p q) ·r val (r-of p q ps) ≡ val p
sof-rof p q ps =
  cong (val (s-of p q) ·r_) (val-r-of p q ps)
  ∙ ·r-comm (val (s-of p q)) (val p /r val (s-of p q))
  ∙ /r-·r-pos ps (val p)
  where
    open import WeightQ using (/r-·r-pos)

-- Lemma B: val(s-of p q) · (1 - val(r-of p q ps))) ≡ (1 - val p) · val q.
-- Derivation:
--   s · (1 - r) = s + (-(s·r)) = s + (-p)         [·r-1-r, then sof-rof]
--               = (p + (1-p)·q) + (-p)            [val-s-of]
--               = ((1-p)·q + p) + (-p)            [+r-comm]
--               = (1-p)·q + (p + (-p))            [+r-assoc]
--               = (1-p)·q + z0                     [+r-inv]
--               = (1-p)·q                          [+r-IdR]
sof-1-rof : ∀ p q (ps : Pos (s-of p q))
          → val (s-of p q) ·r (1-r (val (r-of p q ps))) ≡ (1-r (val p)) ·r val q
sof-1-rof p q ps =
  ·r-1-r (val (s-of p q)) (val (r-of p q ps))
  ∙ cong ((val (s-of p q)) +r_) (cong -r_ (sof-rof p q ps))
  ∙ cong (_+r (-r val p)) (val-s-of p q)
  ∙ cong (_+r (-r val p)) (+r-comm (val p) ((1-r (val p)) ·r val q))
  ∙ sym (+r-assoc ((1-r (val p)) ·r val q) (val p) (-r val p))
  ∙ cong (((1-r (val p)) ·r val q) +r_) (+r-inv (val p))
  ∙ +r-IdR ((1-r (val p)) ·r val q)

-- Lemma C: 1 - val(s-of p q) ≡ (1 - val p) · (1 - val q).
-- Derivation:
--   1-s = 1 - (p + (1-p)·q)                [val-s-of]
--       = (1 - p) - (1-p)·q                 [1-r-+r]
--       = (1-p) + (-((1-p)·q))              [+r-comm or already there]
--       = (1-p) + (1-p)·(-q)                [·r-neg, sym]
--       = (1-p) · 1 + (1-p) · (-q)          [·r-IdR sym]
--       = (1-p) · (1 + (-q))                [·r-distR sym]
--       = (1-p) · (1-q)                     [1-r-def sym]
1-w-s-of : ∀ p q → 1-r (val (s-of p q)) ≡ (1-r (val p)) ·r (1-r (val q))
1-w-s-of p q =
  cong (λ x → 1-r x) (val-s-of p q)
  ∙ 1-r-+r (val p) ((1-r (val p)) ·r val q)
  ∙ cong ((1-r (val p)) +r_) (sym (·r-neg (1-r (val p)) (val q)))
  ∙ cong (_+r ((1-r (val p)) ·r (-r val q))) (sym (·r-IdR (1-r (val p))))
  ∙ sym (·r-distR (1-r (val p)) z1 (-r val q))
  ∙ cong ((1-r (val p)) ·r_) (sym (1-r-def (val q)))

-- Now the main proof: skew-associativity at ℝ level.
-- Goal: val(LHS) ≡ val(RHS) where:
--   LHS = mix-w p a (mix-w q b c)   = p·a + (1-p)·(q·b + (1-q)·c)
--   RHS = mix-w s (mix-w r a b) c    = s·(r·a + (1-r)·b) + (1-s)·c
-- Both expand to: p·a + (1-p)q·b + (1-p)(1-q)·c.

mix-w-assoc-pos-ℝ : ∀ p q (ps : Pos (s-of p q)) a b c
  → val (mix-w p a (mix-w q b c))
  ≡ val (mix-w (s-of p q) (mix-w (r-of p q ps) a b) c)
mix-w-assoc-pos-ℝ p q ps a b c =
  -- LHS = (p·a) +r ((1-p) ·r ((q·b) +r ((1-q)·c)))
  -- Step 1: distribute (1-p) over the inner sum.
  cong ((val p ·r val a) +r_)
       (·r-distR (1-r (val p)) (val q ·r val b) ((1-r (val q)) ·r val c))
  -- Now: (p·a) +r (((1-p)·(q·b)) +r ((1-p)·((1-q)·c)))
  -- Step 2: rearrange triple products.
  ∙ cong (λ z → (val p ·r val a) +r (z +r ((1-r (val p)) ·r ((1-r (val q)) ·r val c))))
         (·r-assoc (1-r (val p)) (val q) (val b))
  ∙ cong (λ z → (val p ·r val a) +r ((((1-r (val p)) ·r val q) ·r val b) +r z))
         (·r-assoc (1-r (val p)) (1-r (val q)) (val c))
  -- Now: (p·a) +r ((((1-p)·q)·b) +r (((1-p)·(1-q))·c))
  -- This is the "expanded form" ε.
  -- Now show RHS reduces to the same ε.
  ∙ sym rhs-eq-ε
  where
    s = val (s-of p q)
    r = val (r-of p q ps)

    rhs-eq-ε :
      val (mix-w (s-of p q) (mix-w (r-of p q ps) a b) c)
      ≡ (val p ·r val a) +r ((((1-r (val p)) ·r val q) ·r val b) +r (((1-r (val p)) ·r (1-r (val q))) ·r val c))
    rhs-eq-ε =
      -- val RHS = (s ·r ((r·a) +r ((1-r)·b))) +r ((1-s)·c)
      -- Step A: distribute s over inner sum: (s·(r·a) + s·((1-r)·b)) + (1-s)·c
      cong (_+r ((1-r s) ·r val c))
           (·r-distR s (r ·r val a) ((1-r r) ·r val b))
      -- Step B: rearrange (s·(r·a)) = (s·r)·a, and (s·((1-r)·b)) = (s·(1-r))·b
      ∙ cong (λ z → (z +r (s ·r ((1-r r) ·r val b))) +r ((1-r s) ·r val c))
             (·r-assoc s r (val a))
      ∙ cong (λ z → ((s ·r r) ·r val a +r z) +r ((1-r s) ·r val c))
             (·r-assoc s (1-r r) (val b))
      -- Step C: substitute s·r = p, s·(1-r) = (1-p)q, 1-s = (1-p)(1-q).
      ∙ cong (λ z → (z ·r val a +r ((s ·r (1-r r)) ·r val b)) +r ((1-r s) ·r val c))
             (sof-rof p q ps)
      ∙ cong (λ z → (val p ·r val a +r (z ·r val b)) +r ((1-r s) ·r val c))
             (sof-1-rof p q ps)
      ∙ cong (λ z → (val p ·r val a +r (((1-r (val p)) ·r val q) ·r val b)) +r (z ·r val c))
             (1-w-s-of p q)
      -- Now: ((p·a) +r ((1-p)·q ·r b)) +r ((1-p)·(1-q) ·r c)
      -- Step D: re-associate to match ε's parenthesization.
      ∙ sym (+r-assoc (val p ·r val a) (((1-r (val p)) ·r val q) ·r val b) (((1-r (val p)) ·r (1-r (val q))) ·r val c))

mix-w-assoc-pos : ∀ p q (ps : Pos (s-of p q)) a b c
  → mix-w p a (mix-w q b c)
  ≡ mix-w (s-of p q) (mix-w (r-of p q ps) a b) c
mix-w-assoc-pos p q ps a b c = WeightPath (mix-w-assoc-pos-ℝ p q ps a b c)

-- ============================================================
-- Section 9b: mix-w-eq-w0/w1 helpers.
--
-- If mix-w p X Y ≡ w0 (or w1), and one factor is positive, the
-- corresponding component is forced to w0 (or w1). These follow
-- from the additive structure +w (which is hidden from FDist-Convex
-- but accessible internally here).
-- ============================================================

open import WeightQ using (+w-eq-w0-l)

-- *w-cancel-l: from p *w x ≡ p *w y with Pos p, conclude x ≡ y.
-- MIGRATED to use partial division _/wPf_⟨_,_⟩ via *w-/wPf-pos.
-- The precondition val (x *w p) ≤r val p follows from val x ≤r z1 (ub x).
*w-cancel-l-WC : ∀ {p} → Pos p → ∀ x y → p *w x ≡ p *w y → x ≡ y
*w-cancel-l-WC {p} pp x y eq =
  sym (*w-/wPf-pos p pp x x*p≤p)
  ∙ cong-/wPf
  ∙ *w-/wPf-pos p pp y y*p≤p
  where
    open import WeightQ
      using (val; ub; lb; ≤r-refl; ≤r-·-mono; ·r-IdL; _≤r_; _·r_;
             isProp-≤r; _/wPf_⟨_,_⟩; *w-/wPf-pos; *w-comm)
    open import Cubical.Foundations.Prelude using (subst; PathP; isProp→PathP)

    -- (x *w p) ≤w p:  val x ·r val p ≤r val p
    -- via ≤r-·-mono (lb x) (lb p) (ub x) (≤r-refl (val p)) gives
    --     val x ·r val p ≤r z1 ·r val p, then rewrite z1 ·r val p = val p.
    x*p≤p : (x *w p) ≤w p
    x*p≤p = subst (λ z → (val x ·r val p) ≤r z) (·r-IdL (val p))
                  (≤r-·-mono (lb x) (lb p) (ub x) (≤r-refl (val p)))
    y*p≤p : (y *w p) ≤w p
    y*p≤p = subst (λ z → (val y ·r val p) ≤r z) (·r-IdL (val p))
                  (≤r-·-mono (lb y) (lb p) (ub y) (≤r-refl (val p)))

    -- The middle congruence: equate two partial divisions across a path
    -- in the value (induced by x*p≡y*p) and a Prop-valued path in the precondition.
    x*p≡y*p : x *w p ≡ y *w p
    x*p≡y*p = *w-comm x p ∙ eq ∙ *w-comm p y

    cong-/wPf : (x *w p) /wPf p ⟨ pp , x*p≤p ⟩ ≡ (y *w p) /wPf p ⟨ pp , y*p≤p ⟩
    cong-/wPf i = (x*p≡y*p i) /wPf p ⟨ pp , prec-path i ⟩
      where
        prec-path : PathP (λ i → val (x*p≡y*p i) ≤r val p) x*p≤p y*p≤p
        prec-path = isProp→PathP (λ _ → isProp-≤r) x*p≤p y*p≤p

-- (w0-/w-p was previously a private helper proving w0 /w p ≡ w0 for Pos p,
-- using *w-/w-pos and /w-*w-pos. After the partial-division migration,
-- *w-cancel-l-WC no longer depends on the total-/w identities, and this
-- helper has no remaining users. Removed.)

-- pos-*w-eq-w0: if Pos p and p *w x ≡ w0, then x ≡ w0.
pos-*w-eq-w0-helper : ∀ {p} → Pos p → ∀ x → p *w x ≡ w0 → x ≡ w0
pos-*w-eq-w0-helper {p} pp x p·x≡w0 =
  *w-cancel-l-WC pp x w0 (p·x≡w0 ∙ sym (*w-0 p))

-- mix-w-eq-w0-pos-l: from mix-w p X Y ≡ w0 and Pos p, conclude X ≡ w0.
-- The bound argument to +w-eq-w0-l is mix-bound p X Y, since
-- mix-w p X Y is built using exactly that bound proof.
mix-w-eq-w0-pos-l : ∀ {p X Y} → Pos p → mix-w p X Y ≡ w0 → X ≡ w0
mix-w-eq-w0-pos-l {p} {X} {Y} pp eq =
  pos-*w-eq-w0-helper pp X (+w-eq-w0-l (p *w X) ((1-w p) *w Y) (mix-bound p X Y) eq)

-- mix-w-eq-w0-pos-r: from mix-w p X Y ≡ w0 and Pos (1-w p), conclude Y ≡ w0.
-- Drops to ℝ-level: val (mix-w p X Y) ≡ z0 and a sum of non-negatives is
-- zero iff each is zero — so val ((1-w p) *w Y) ≡ z0, hence Y ≡ w0 by
-- pos-*w-eq-w0-helper.
mix-w-eq-w0-pos-r : ∀ {p X Y} → Pos (1-w p) → mix-w p X Y ≡ w0 → Y ≡ w0
mix-w-eq-w0-pos-r {p} {X} {Y} pp eq =
  pos-*w-eq-w0-helper {p = 1-w p} pp Y
    (WeightPath
      (+r-eq-z0-l (val ((1-w p) *w Y)) (val (p *w X))
        (lb ((1-w p) *w Y)) (lb (p *w X))
        (+r-comm (val ((1-w p) *w Y)) (val (p *w X)) ∙ cong val eq)))
  where
    open import WeightQ using (+r-eq-z0-l)

-- mix-w-eq-w1-pos-l: from mix-w p X Y ≡ w1 and Pos p, conclude X ≡ w1.
-- Proof via complement: 1-w (mix-w p X Y) ≡ w0, then 1-w-mix-w gives
-- mix-w p (1-w X) (1-w Y) ≡ w0. By mix-w-eq-w0-pos-l, 1-w X ≡ w0.
-- By 1-w-invol: X ≡ w1.
mix-w-eq-w1-pos-l : ∀ {p X Y} → Pos p → mix-w p X Y ≡ w1 → X ≡ w1
mix-w-eq-w1-pos-l {p} {X} {Y} pp eq =
  sym (1-w-invol X)
  ∙ cong 1-w_ (mix-w-eq-w0-pos-l pp
                 (sym (1-w-mix-w p X Y) ∙ cong 1-w_ eq ∙ 1-w-1))
  ∙ 1-w-0

-- mix-w-eq-w1-pos-r: symmetric.
mix-w-eq-w1-pos-r : ∀ {p X Y} → Pos (1-w p) → mix-w p X Y ≡ w1 → Y ≡ w1
mix-w-eq-w1-pos-r {p} {X} {Y} pp eq =
  sym (1-w-invol Y)
  ∙ cong 1-w_ (mix-w-eq-w0-pos-r pp
                 (sym (1-w-mix-w p X Y) ∙ cong 1-w_ eq ∙ 1-w-1))
  ∙ 1-w-0

-- ============================================================
-- Section 10: Bayesian-complement and renorm-rebase as theorems.
--
-- These are abstract versions parameterized over an arbitrary b
-- with the property b *w Z ≡ p *w t₁ (where Z = mix-w p t₁ t₂).
-- In FDist-Convex.agda, b is instantiated to bayesW p t₁ t₂ pTM,
-- and the hypothesis is supplied by bayesW-*w-Z (which is itself
-- normalize-*w-back).
-- ============================================================

-- bayesW-complement-abstract: from b·Z ≡ p·t₁, derive (1-b)·Z ≡ (1-p)·t₂
-- where Z = mix-w p t₁ t₂.
--
-- Proof: weighted-idem says (b·Z) +w ((1-b)·Z) ≡ Z.
-- By definition of mix-w, Z ≡ (p·t₁) +w ((1-p)·t₂).
-- So (b·Z) +w ((1-b)·Z) ≡ (p·t₁) +w ((1-p)·t₂).
-- Substituting b·Z ≡ p·t₁ on the LHS:
--   (p·t₁) +w ((1-b)·Z) ≡ (p·t₁) +w ((1-p)·t₂).
-- By +w-cancel-l: (1-b)·Z ≡ (1-p)·t₂.
-- The proof drops to ℝ-level via WeightPath and uses +r-cancel-l-ℝ
-- to cancel (val p · val t₁) from both sides. The chain at ℝ level:
--   (val p · val t₁) + val ((1-w b)·Z)
--     = val (b·Z) + val ((1-w b)·Z)         [from sym (cong val b·Z≡p·t₁)]
--     = val Z                                [weighted-idem-ℝ at val b, val Z]
--     = (val p · val t₁) + val ((1-w p)·t₂)  [definitional, val of mix-w]
-- Cancel-l yields val ((1-w b)·Z) ≡ val ((1-w p)·t₂), then WeightPath.
bayesW-complement-abstract : ∀ b p t₁ t₂
  → b *w (mix-w p t₁ t₂) ≡ p *w t₁
  → (1-w b) *w (mix-w p t₁ t₂) ≡ (1-w p) *w t₂
bayesW-complement-abstract b p t₁ t₂ b·Z≡p·t₁ = WeightPath
  (+r-cancel-l-ℝ (val p ·r val t₁) _ _
    (cong (_+r val ((1-w b) *w (mix-w p t₁ t₂))) (sym (cong val b·Z≡p·t₁))
     ∙ weighted-idem-ℝ (val b) (val (mix-w p t₁ t₂))))

-- renorm-rebase-abstract: from b·Z ≡ p·t₁ and (1-b)·Z ≡ (1-p)·t₂, derive
-- mix-w b X Y *w Z ≡ mix-w p (t₁·X) (t₂·Y).
--
-- Proof at Weight level. Z = mix-w p t₁ t₂ on RHS context, but the proof
-- only uses b·Z ≡ p·t₁ and (1-b)·Z ≡ (1-p)·t₂.
-- mix-w b X Y *w Z = ((b·X) +w ((1-b)·Y)) *w Z              [defn of mix-w; refl]
--                 = (Z·(b·X)) +w (Z·((1-b)·Y))              [via *w-comm, *w-distrib-+w, *w-comm again]
--                 = ((Z·b)·X) +w ((Z·(1-b))·Y)              [*w-assoc]
--                 = ((b·Z)·X) +w (((1-b)·Z)·Y)              [*w-comm]
--                 = ((p·t₁)·X) +w (((1-p)·t₂)·Y)            [substitute hypotheses]
--                 = (p·(t₁·X)) +w ((1-p)·(t₂·Y))            [*w-assoc]
--                 = mix-w p (t₁·X) (t₂·Y)                    [defn of mix-w; refl]
-- Lifted to ℝ-level via WeightPath. The val-chain (with Z = mix-w p t₁ t₂):
--   val (mix-w b X Y *w Z)
--     = val (mix-w b X Y) ·r val Z                [defn of *w]
--     = ((val b · val X) + (val (1-w b) · val Y)) · val Z   [defn of mix-w]
--     = (val b · val X · val Z) + (val (1-w b) · val Y · val Z)  [·r-distL]
--     = (val b · val Z · val X) + (val (1-w b) · val Z · val Y)  [·r-comm/assoc]
--     = (val p · val t₁ · val X) + (val (1-w p) · val t₂ · val Y) [hypotheses]
--     = (val p · (val t₁ · val X)) + (val (1-w p) · (val t₂ · val Y)) [·r-assoc]
--     = val (mix-w p (t₁ *w X) (t₂ *w Y))         [defn of mix-w]
renorm-rebase-abstract : ∀ b p t₁ t₂ X Y
  → b *w (mix-w p t₁ t₂) ≡ p *w t₁
  → (1-w b) *w (mix-w p t₁ t₂) ≡ (1-w p) *w t₂
  → mix-w b X Y *w (mix-w p t₁ t₂) ≡ mix-w p (t₁ *w X) (t₂ *w Y)
renorm-rebase-abstract b p t₁ t₂ X Y b·Z≡p·t₁ 1-b·Z≡1-p·t₂ = WeightPath
  (·r-distL (val b ·r val X) (val (1-w b) ·r val Y) (val (mix-w p t₁ t₂))
   ∙ cong₂ _+r_
       (sym (·r-assoc (val b) (val X) (val (mix-w p t₁ t₂)))
        ∙ cong (val b ·r_) (·r-comm (val X) (val (mix-w p t₁ t₂)))
        ∙ ·r-assoc (val b) (val (mix-w p t₁ t₂)) (val X)
        ∙ cong (_·r val X) (cong val b·Z≡p·t₁)
        ∙ sym (·r-assoc (val p) (val t₁) (val X)))
       (sym (·r-assoc (val (1-w b)) (val Y) (val (mix-w p t₁ t₂)))
        ∙ cong (val (1-w b) ·r_) (·r-comm (val Y) (val (mix-w p t₁ t₂)))
        ∙ ·r-assoc (val (1-w b)) (val (mix-w p t₁ t₂)) (val Y)
        ∙ cong (_·r val Y) (cong val 1-b·Z≡1-p·t₂)
        ∙ sym (·r-assoc (val (1-w p)) (val t₂) (val Y))))
