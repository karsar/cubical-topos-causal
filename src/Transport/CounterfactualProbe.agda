{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.CounterfactualProbe — a feasibility probe.
--
-- QUESTION.  Does the sheaf-gluing machinery this development
-- already has host Pearl's structural COUNTERFACTUALS?  That
-- machinery is Topos.Gluing, with the pullback X ×_Z Y and its
-- universal property, and Topos.Contextuality, with the
-- no-global-section obstruction.  A twin network is two copies of an
-- SCM that share their exogenous noise U, and that is a pullback
-- over U.  Suppose the glued twin network computes Pearl's
-- abduction-action-prediction value, and suppose a case that fails
-- to glue is counterfactual non-identifiability.  Then the two topos
-- pillars carry genuine causal content.
--
-- WHAT THIS PROBE ESTABLISHES (machine-checked, --safe):
--   * twin≡aap          : the glued twin-network counterfactual
--                         equals Pearl's abduction-action-prediction
--                         value.  The proof uses the ⊕-algebra, so
--                         it is not refl.
--   * twinCF-welldefined: the counterfactual does not depend on the
--                         abduction witness.  This is the set-level
--                         form of pullback uniqueness (glue-uniq).
--   * no-twin           : inconsistent factual evidence admits NO
--                         twin world.  This is the set-level form of
--                         the no-global-section result
--                         Contextuality.no-global, and it says the
--                         counterfactual is non-identifiable from
--                         that evidence.
--
-- WHAT IT DOES NOT DO (the honest caveats, and the actual paper):
--   * It is a single DETERMINISTIC SCM at one context, the
--     set-level single-context case of Topos.Gluing.Pullback.  The
--     probabilistic case must use the FDist monad, with mechanisms
--     as kernels, where abduction is Bayesian conditioning.
--   * The obstruction here is the DEGENERATE one, inconsistent
--     evidence.  The research-grade obstruction is
--     non-identifiability across observationally-equivalent SCMs.
--   * The counterfactual is not yet INTERNALISED as a Kripke-Joyal
--     forced proposition (Topos.Forcing).  That internalisation is
--     what would make the result topos-internal rather than a
--     re-description.  These three are the next steps; they are not
--     done here.
-- ============================================================

module Transport.CounterfactualProbe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; not; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)

-- exclusive-or, with the one algebraic fact we need.
xorb : Bool → Bool → Bool
xorb false b = b
xorb true  b = not b

xor-cancelL : (a b : Bool) → xorb a (xorb a b) ≡ b
xor-cancelL false false = refl
xor-cancelL false true  = refl
xor-cancelL true  false = refl
xor-cancelL true  true  = refl

-- ----------------------------------------------------------
-- A deterministic two-variable SCM  X → Y  with explicit noise.
--   exogenous u = (uX , uY)
--   X(u) = uX
--   Y(u) = X(u) ⊕ uY
-- ----------------------------------------------------------
U : Type
U = Bool × Bool

Xeq : U → Bool
Xeq (uX , uY) = uX

Yeq : U → Bool
Yeq (uX , uY) = xorb uX uY

-- Pearl's counterfactual outcome Y_{X := x}(u): override X by x,
-- keep the same noise, recompute Y.
cfOut : Bool → U → Bool
cfOut x (uX , uY) = xorb x uY

-- Abduction–action–prediction, given factual evidence X=x', Y=y':
-- abduction recovers uY = x' ⊕ y'; prediction returns x ⊕ uY.
aap : (x x' y' : Bool) → Bool
aap x x' y' = xorb x (xorb x' y')

-- A factual world consistent with the evidence (x' , y') is a noise
-- value producing it.
Factual : Bool → Bool → Type
Factual x' y' = Σ[ u ∈ U ] ((Xeq u ≡ x') × (Yeq u ≡ y'))

-- ----------------------------------------------------------
-- The twin network as a pullback over the shared noise.  Abduction
-- pins u in the factual world.  The counterfactual world uses
-- do(X:=x) with that same u.  The two worlds agree on u, which is
-- the sheaf-compatibility condition on the overlap.  The glued
-- counterfactual outcome reads Y off the counterfactual world:
-- ----------------------------------------------------------
twinCF : (x x' y' : Bool) → Factual x' y' → Bool
twinCF x x' y' (u , _ , _) = cfOut x u

-- THEOREM 1.  The twin-network counterfactual equals Pearl's
-- abduction-action-prediction value.
twin≡aap : (x x' y' : Bool) (w : Factual x' y')
         → twinCF x x' y' w ≡ aap x x' y'
twin≡aap x x' y' ((uX , uY) , px , py) =
  cong (xorb x) (uY≡ ∙ cong (λ z → xorb z y') px)
  where
    uY≡ : uY ≡ xorb uX y'
    uY≡ = sym (xor-cancelL uX uY) ∙ cong (xorb uX) py

-- THEOREM 2.  The counterfactual does not depend on which abduction
-- witness is chosen, so it is well-defined.  This is the set-level
-- form of pullback uniqueness (glue-uniq).
twinCF-welldefined : (x x' y' : Bool) (w₁ w₂ : Factual x' y')
                   → twinCF x x' y' w₁ ≡ twinCF x x' y' w₂
twinCF-welldefined x x' y' w₁ w₂ =
  twin≡aap x x' y' w₁ ∙ sym (twin≡aap x x' y' w₂)

-- ----------------------------------------------------------
-- The obstruction.  Take a model where Y copies X, so Y ignores its
-- own noise.  The evidence X=true, Y=false is then unrealisable:
-- there is NO factual world, and so no twin to glue.  The
-- counterfactual is non-identifiable from that evidence.  This is
-- the no-global-section phenomenon of Topos.Contextuality, stated
-- here for a counterfactual query.
-- ----------------------------------------------------------
Yeq′ : U → Bool
Yeq′ (uX , uY) = uX

Factual′ : Bool → Bool → Type
Factual′ x' y' = Σ[ u ∈ U ] ((Xeq u ≡ x') × (Yeq′ u ≡ y'))

no-twin : ¬ Factual′ true false
no-twin ((uX , uY) , px , py) = true≢false (sym px ∙ py)
