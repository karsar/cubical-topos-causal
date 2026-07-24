{-# OPTIONS --cubical --guardedness #-}

-- ============================================================
-- Transport.Transportability — from witness to theorem.
--
-- The weld (Transport.CounterfactualWeld) showed, for two specific
-- worlds, that forcing the computed counterfactual at the global
-- context is transportability.  Here we upgrade it twice:
--
--   1.  The counterfactual becomes a PROPER internal predicate
--       χ : W ⇒ Ω — an actual natural transformation (classified
--       subobject) over a presheaf W of worlds, with naturality
--       PROVED (not per-world sieves).
--
--   2.  The transport result becomes a GENERAL theorem, quantified
--       over predicates, not a pair of witnesses:
--         global-transport→everywhere :
--           for ANY restriction-stable regime predicate, if the
--           counterfactual transports to the global context then it
--           transports to every regime the context covers.
--       The hypothesis (restriction-stability) is exactly the sieve
--       closure — the causal condition that a globally-true
--       counterfactual is locally true.  Predicates that fail it are
--       not internalisable as truth values at all: that is the
--       obstruction to transportability, internal-logically.
--
-- We then instantiate at the SCM counterfactual of the weld
-- (do(X:=true), query Y=true), recovering the transportable and
-- non-transportable worlds as corollaries of the general theorem.
--
-- HONEST LIMITS (unchanged from the weld).  Deterministic; finite
-- regime category; worlds are the shared exogenous noise.  "Transport"
-- is the internal notion (forcing at a context), NOT yet proved
-- equivalent to the Bareinboim-Pearl s-hedge criterion — that
-- equivalence, and the probabilistic (FDist-kernel) case, are the
-- remaining theory.  What is new here over the weld: the predicate is
-- a genuine W ⇒ Ω, and transport-invariance is a theorem about a class
-- of models.
-- ============================================================

module Transport.Transportability where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp; isSet×)
open import Cubical.Data.Bool using (Bool; true; false; not; isSetBool; false≢true)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Empty using () renaming (rec to ⊥rec)
open import Cubical.Relation.Nullary using (¬_)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.Forcing

open import Transport.CounterfactualForcing using (Obj; g; e; Hom₀; ι; C)
open import Transport.CounterfactualProbe using (U)
open import Transport.CounterfactualWeld using (cfoG; cfoE; andb-R)

open PSh

-- ----------------------------------------------------------
-- The presheaf of worlds: the shared exogenous noise (twin network),
-- the same in every regime, so restriction is the identity.
-- ----------------------------------------------------------
W : PSh C ℓ-zero
W = record
  { F₀ = λ _ → U
  ; F₁ = λ _ a → a
  ; F-id = λ _ → refl
  ; F-comp = λ _ _ _ → refl
  ; isSetF₀ = λ _ → isSet× isSetBool isSetBool }

-- ----------------------------------------------------------
-- A regime predicate: "the counterfactual holds at regime c, world u",
-- prop-valued and RESTRICTION-STABLE (holds at c and d → c implies
-- holds at d).  Stability is exactly what makes the predicate a sieve.
-- ----------------------------------------------------------
record RegPred : Type₁ where
  field
    P       : Obj → U → Type
    isPropP : (c : Obj) (u : U) → isProp (P c u)
    stable  : (c d : Obj) (k : Hom₀ d c) (u : U) → P c u → P d u

-- ----------------------------------------------------------
-- Every restriction-stable regime predicate is a genuine internal
-- predicate χ : W ⇒ Ω.  Naturality is proved (it holds because sieve
-- membership reads only the source regime).
-- ----------------------------------------------------------
χ : (R : RegPred) → Nat W Ω
χ R = α , nat
  where
    open RegPred R
    α : (c : Obj) → U → Sieve {C = C} c
    α c u = (λ d h → P d u , isPropP d u) , (λ d e' k f pf → stable d e' k u pf)
    nat : IsNat W Ω α
    nat x y f u = Sieve≡ {C = C} (α x u) (pull {C = C} f (α y u)) refl

-- The counterfactual TRANSPORTS to regime c (at world u) iff it is
-- forced there, i.e. c ⊩ (the sieve component of χ at c, u).
transports-to : RegPred → Obj → U → Type
transports-to R c u = _⊩_ {C = C} c (fst (χ R) c u)

-- Forcing the predicate at a regime is exactly the predicate holding
-- there (definitional — the forcing IS the per-regime truth).
forced→holds : (R : RegPred) (c : Obj) (u : U)
             → transports-to R c u → RegPred.P R c u
forced→holds R c u h = h
holds→forced : (R : RegPred) (c : Obj) (u : U)
             → RegPred.P R c u → transports-to R c u
holds→forced R c u h = h

-- THE GENERAL THEOREM.  If the counterfactual transports to the global
-- context, it transports to every regime that context covers.  This is
-- the internal-logic locality (sieve closure = restriction-stability),
-- and it is the content the graphical single-graph view cannot state.
global-transport→everywhere :
    (R : RegPred) (u : U)
  → transports-to R g u → (d : Obj) → transports-to R d u
global-transport→everywhere R u tg g = tg
global-transport→everywhere R u tg e = RegPred.stable R g e ι u tg

-- ----------------------------------------------------------
-- Instantiation: the SCM counterfactual of the weld
-- (do(X:=true), query Y=true).  cfoG / cfoE are its global and
-- environment outcomes; restriction-stability is andb-R.
-- ----------------------------------------------------------
cfo : Obj → U → Bool
cfo g u = cfoG u
cfo e u = cfoE u

scmPred : RegPred
RegPred.P scmPred c u = cfo c u ≡ true
RegPred.isPropP scmPred c u = isSetBool (cfo c u) true
RegPred.stable scmPred g g k u p = p
RegPred.stable scmPred g e k u p = andb-R (fst u) (not (snd u)) p
RegPred.stable scmPred e g k u p = ⊥rec k
RegPred.stable scmPred e e k u p = p

-- Transport-invariance for the SCM counterfactual, as a corollary.
scm-transport-invariance :
    (u : U) → transports-to scmPred g u → (d : Obj) → transports-to scmPred d u
scm-transport-invariance = global-transport→everywhere scmPred

-- The two worlds of the weld, recovered as instances.
scm-transportable : transports-to scmPred g (true , false)
scm-transportable = refl

scm-local : transports-to scmPred e (false , false)
scm-local = refl

scm-not-transportable : ¬ (transports-to scmPred g (false , false))
scm-not-transportable p = false≢true p
