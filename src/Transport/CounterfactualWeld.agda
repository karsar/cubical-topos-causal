{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Transport.CounterfactualWeld — welding the two probes.
--
-- CounterfactualProbe: the GLUING pillar computes Pearl's
--   counterfactual.  A twin network is a pullback over shared noise,
--   and its value is the abduction-action-prediction value `aap`.
-- CounterfactualForcing: the INTERNAL LOGIC (Kripke-Joyal forcing)
--   separates local truth from global truth over a regime category.
--
-- THIS MODULE connects them.  The computed counterfactual outcome
-- becomes an Ω-valued predicate, a sieve over the regime category,
-- and its FORCING at the global context is TRANSPORTABILITY.
--
--   * cfoE / cfoG  — the counterfactual outcome for do(X:=true) with
--                    query Y=true, in the environment regime e and in
--                    the global regime g.  cfoE equals Pearl's
--                    abduction-action-prediction value; link-E proves
--                    cfoE u ≡ aap ….  So this is the SAME
--                    counterfactual that CounterfactualProbe computed
--                    through the twin-network gluing, reused here.
--   * cfSieve u    — that counterfactual as an internal truth value.
--                    Its sieve CLOSURE is the proof pg2pe: a
--                    globally-true counterfactual is locally true.
--                    That is the causal restriction-stability
--                    condition.
--   * transportable     — at world (true,false) the counterfactual is
--                    forced at the GLOBAL context g, so it
--                    transports.
--   * holds-locally + not-transportable — at world (false,false) it
--                    is forced in the environment e and NOT at g.  It
--                    holds locally and does not transport.  Local
--                    truth and global truth differ, and here that is
--                    a fact about the COMPUTED counterfactual, since
--                    cfSieve is built from cfoG and cfoE rather than
--                    posited.
--   * invariance   — transport gives forcing at every regime
--                    (⊩-mono).
--
-- Reading: "the counterfactual is forced at the global context"
-- means "the counterfactual computed by the twin-network gluing
-- transports across the regimes that context covers".  A single
-- causal graph cannot state this.  That is the end-to-end weld.
--
-- HONEST LIMITS (the actual paper).  The model is deterministic and
-- has two regimes.  The predicate is given as one sieve per world
-- rather than as a single natural transformation W ⇒ Ω.
-- "Transportability" here is the internal notion, and it is NOT yet
-- proved equivalent to the Bareinboim-Pearl s-hedge criterion.  That
-- equivalence, and the probabilistic case where abduction is
-- Bayesian conditioning in the FDist monad, are the work that would
-- turn this proof of concept into a theorem.
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
-- The counterfactual outcome per regime, under do(X := true) with
-- query Y = true.  The environment realises it whenever uY = false.
-- The global regime also requires uX = true.
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

-- The environment outcome equals Pearl's abduction-action-prediction
-- value for do(X:=true) with evidence X=false:
-- cfoE u = aap true false (snd u).  This is the same counterfactual
-- that CounterfactualProbe computed by twin-network gluing, reused
-- here.
link-E : (u : U) → cfoE u ≡ aap true false (snd u)
link-E u = refl

-- ----------------------------------------------------------
-- The counterfactual as an internal truth value.  It is the sieve on
-- the global context whose membership at a regime is "the
-- counterfactual holds at this regime".  Its closure condition is
-- causal restriction-stability: global truth gives local truth.
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

-- At world (true , false) the counterfactual is forced at the GLOBAL
-- context, so it transports across the regimes g covers.
transportable : _⊩_ {C = C} g (cfSieve (true , false))
transportable = refl

-- At world (false , false) it is forced in the environment e.
holds-locally : _⊩_ {C = C} e (pull {C = C} ι (cfSieve (false , false)))
holds-locally = refl

-- The same world is NOT forced at the global context: the
-- counterfactual holds locally and does not transport.
not-transportable : ¬ (_⊩_ {C = C} g (cfSieve (false , false)))
not-transportable p = false≢true p

-- A transported counterfactual is forced at every regime.
invariance : (d : Obj) (f : Hom₀ d g)
           → _⊩_ {C = C} d (pull {C = C} f (cfSieve (true , false)))
invariance d f = ⊩-mono {C = C} (cfSieve (true , false)) transportable f
