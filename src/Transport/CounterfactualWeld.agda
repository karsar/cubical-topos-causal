{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.CounterfactualWeld — welding the two probes.
--
-- CounterfactualProbe: the GLUING pillar computes Pearl's
--   counterfactual (twin network = pullback over shared noise;
--   the value is the abduction-action-prediction value `aap`).
-- CounterfactualForcing: the INTERNAL LOGIC (Kripke-Joyal forcing)
--   distinguishes local from global truth over a regime category.
--
-- THIS MODULE connects them: the computed counterfactual outcome
-- becomes an Ω-valued predicate (a sieve over the regime category),
-- and its FORCING at the global context is TRANSPORTABILITY.
--
--   * cfoE / cfoG  — the counterfactual outcome (do(X:=true), query
--                    Y=true) in the environment regime e and the
--                    global regime g.  cfoE is exactly Pearl's
--                    abduction-action-prediction value (link-E:
--                    cfoE u ≡ aap …), so this is the SAME
--                    counterfactual CounterfactualProbe computed via
--                    the twin-network gluing — not a fresh assertion.
--   * cfSieve u    — that counterfactual as an internal truth value.
--                    Its sieve CLOSURE is the proof pg2pe that a
--                    globally-true counterfactual is locally true:
--                    the causal restriction-stability condition.
--   * transportable     — at world (true,false) the counterfactual is
--                    forced at the GLOBAL context g: it transports.
--   * holds-locally + not-transportable — at world (false,false) it is
--                    forced in the environment e but NOT at g: it holds
--                    locally and does NOT transport.  Local truth ≠
--                    global truth is now a fact about the COMPUTED
--                    counterfactual, not a toy sieve.
--   * invariance   — transport ⟹ forced at every regime (⊩-mono).
--
-- So "the counterfactual is forced at the global context" = "the
-- counterfactual (computed by the twin-network gluing) transports
-- across the regimes that context covers" — a statement with no
-- single-graph analogue.  This is the end-to-end weld.
--
-- HONEST LIMITS (the actual paper).  Deterministic; two regimes; the
-- predicate is given as per-world sieves rather than one natural
-- transformation W ⇒ Ω; and "transportability" here is the internal
-- notion, NOT yet proved equivalent to the Bareinboim-Pearl s-hedge
-- criterion.  The probabilistic case (abduction = Bayesian
-- conditioning in the FDist monad) and that equivalence are the work
-- that would make this a theorem rather than a proof of concept.
-- ============================================================

module Transport.CounterfactualWeld where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Bool using (Bool; true; false; not; false≢true; isSetBool)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty using () renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Cat
open import Topos.Omega
open import Topos.Forcing
open import Transport.CounterfactualForcing using (Obj; g; e; Hom₀; ι; C)
open import Transport.CounterfactualProbe as CP using (U; aap)

-- ----------------------------------------------------------
-- The counterfactual outcome under do(X := true), query Y = true,
-- per regime.  The environment realises it whenever uY = false;
-- the global regime additionally requires uX = true.
-- ----------------------------------------------------------
andb : Bool → Bool → Bool
andb true  b = b
andb false _ = false

andb-R : (a b : Bool) → andb a b ≡ true → b ≡ true
andb-R true  b p = p
andb-R false b p = ⊥rec (false≢true p)

cfoE : U → Bool
cfoE u = not (snd u)

cfoG : U → Bool
cfoG u = andb (fst u) (not (snd u))

-- The environment outcome IS Pearl's abduction-action-prediction
-- value (do(X:=true), evidence X=false): cfoE u = aap true false (snd u).
-- This is the same counterfactual CounterfactualProbe computed via the
-- twin-network gluing, now reused.
link-E : (u : U) → cfoE u ≡ aap true false (snd u)
link-E u = refl

-- ----------------------------------------------------------
-- The counterfactual as an internal truth value: the sieve on the
-- global context whose membership is "the counterfactual holds at
-- this regime".  Its closure is the causal restriction-stability
-- (global truth ⟹ local truth).
-- ----------------------------------------------------------
cfSieve : U → Sieve {C = C} g
cfSieve u = mem , clo
  where
    Pg Pe : hProp ℓ-zero
    Pg = (cfoG u ≡ true) , isSetBool (cfoG u) true
    Pe = (cfoE u ≡ true) , isSetBool (cfoE u) true
    mem : SieveMem {C = C} g
    mem g _ = Pg
    mem e _ = Pe
    -- the causal content: a globally-true counterfactual is locally true
    pg2pe : cfoG u ≡ true → cfoE u ≡ true
    pg2pe = andb-R (fst u) (not (snd u))
    clo : Closure {C = C} g mem
    clo g g k f pf = pf
    clo g e k f pf = pg2pe pf
    clo e g k f pf = ⊥rec k
    clo e e k f pf = pf

-- ----------------------------------------------------------
-- Forcing = transportability.
-- ----------------------------------------------------------

-- At world (true , false): forced at the GLOBAL context — the
-- counterfactual transports across the regimes g covers.
transportable : _⊩_ {C = C} g (cfSieve (true , false))
transportable = refl

-- At world (false , false): forced in the environment e…
holds-locally : _⊩_ {C = C} e (pull {C = C} ι (cfSieve (false , false)))
holds-locally = refl

-- …but NOT at the global context: it holds locally and does not transport.
not-transportable : ¬ (_⊩_ {C = C} g (cfSieve (false , false)))
not-transportable p = false≢true p

-- Invariance for free: a transported counterfactual is forced at every regime.
invariance : (d : Obj) (f : Hom₀ d g)
           → _⊩_ {C = C} d (pull {C = C} f (cfSieve (true , false)))
invariance d f = ⊩-mono {C = C} (cfSieve (true , false)) transportable f
