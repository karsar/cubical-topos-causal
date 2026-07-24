{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.CounterfactualProbe — a feasibility probe.
--
-- QUESTION.  Does the sheaf-gluing machinery this development
-- already has (Topos.Gluing: the pullback X ×_Z Y with its
-- universal property; Topos.Contextuality: the no-global-section
-- obstruction) actually host Pearl's structural COUNTERFACTUALS?
-- A twin network is two copies of an SCM sharing their exogenous
-- noise U; that is a pullback over U.  If the glued twin network
-- computes Pearl's abduction-action-prediction value, and a
-- non-gluing case is counterfactual non-identifiability, then the
-- two topos pillars carry genuine causal content.
--
-- WHAT THIS PROBE ESTABLISHES (machine-checked, --safe):
--   * twin≡aap          : the glued twin-network counterfactual
--                         equals Pearl's abduction-action-prediction
--                         value (genuine ⊕-algebra, not refl);
--   * twinCF-welldefined: the counterfactual is independent of the
--                         abduction witness (the pullback-uniqueness
--                         / glue-uniq shadow);
--   * no-twin           : inconsistent factual evidence admits NO
--                         twin world (the no-global-section /
--                         Contextuality.no-global shadow), i.e. the
--                         counterfactual is non-identifiable from it.
--
-- WHAT IT DOES NOT (the honest caveats / the actual paper):
--   * It is a single DETERMINISTIC SCM at one context, the
--     set-level (single-context) shadow of Topos.Gluing.Pullback;
--     the probabilistic case must use the FDist monad (mechanisms
--     as kernels), where abduction is Bayesian conditioning.
--   * The obstruction here is the DEGENERATE one (inconsistent
--     evidence); the research-grade obstruction is non-identifiability
--     across observationally-equivalent SCMs.
--   * The counterfactual is not yet INTERNALISED as a Kripke-Joyal
--     forced proposition (Topos.Forcing); that internalisation is
--     what would make the result topos-internal rather than a
--     re-description.  These three are the next steps, not done here.
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
-- keep the SAME noise, recompute Y.
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
-- The twin network as a pullback over the shared noise.  The
-- factual world (which pins u by abduction) and the counterfactual
-- world (do(X:=x), same u) agree on u — the sheaf-compatibility
-- condition on the overlap.  The glued counterfactual outcome reads
-- Y off the counterfactual world:
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

-- THEOREM 2.  The counterfactual is independent of which abduction
-- witness is chosen — the pullback-uniqueness (glue-uniq) shadow,
-- i.e. the counterfactual is well-defined.
twinCF-welldefined : (x x' y' : Bool) (w₁ w₂ : Factual x' y')
                   → twinCF x x' y' w₁ ≡ twinCF x x' y' w₂
twinCF-welldefined x x' y' w₁ w₂ =
  twin≡aap x x' y' w₁ ∙ sym (twin≡aap x x' y' w₂)

-- ----------------------------------------------------------
-- The obstruction.  In a model where Y copies X (Y ignores its own
-- noise), the evidence X=true, Y=false is unrealisable: there is NO
-- factual world, hence no twin to glue — the counterfactual is
-- non-identifiable from that evidence.  This is the no-global-section
-- phenomenon of Topos.Contextuality, here for a counterfactual query.
-- ----------------------------------------------------------
Yeq′ : U → Bool
Yeq′ (uX , uY) = uX

Factual′ : Bool → Bool → Type
Factual′ x' y' = Σ[ u ∈ U ] ((Xeq u ≡ x') × (Yeq′ u ≡ y'))

no-twin : ¬ Factual′ true false
no-twin ((uX , uY) , px , py) = true≢false (sym px ∙ py)
