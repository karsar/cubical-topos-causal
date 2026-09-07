{-# OPTIONS --safe --cubical --guardedness #-}

-- ============================================================
-- Topos.VersionSite — well-definedness is graded.
--
-- Topos.VersionFactoring builds the classifier χ-wd of treatment
-- variation irrelevance.  This module runs it on the intervention
-- site of Topos.InterventionSite and reads off a truth value that
-- is neither ⊥ nor ⊤.
--
-- The regimes are read as availability of means:
--     do0 ─→ obs ←─ do1
--   obs : the value of the variable is named, no means is named;
--   do0 : the diet-only regime.  One version of "BMI = x";
--   do1 : the regime where surgery is available too.  Two
--         versions of the same "BMI = x".
--
-- So the version presheaf is
--     Ver obs = Unit,  Ver do0 = Unit,  Ver do1 = Bool,
-- restriction to do1 picking out the diet version.  Refinement
-- ADDS a version.  The value presheaf is Unit throughout: both
-- versions realise the same BMI.  The outcome (mortality) is Bool
-- throughout with identity restriction.
--
-- The mechanism mI returns the outcome of the version.  It cannot
-- see the surgery version from obs, because obs has only one
-- version; it sees it from do1.
--
-- Results:
--   wd-at-e0        the effect IS well defined over do0;
--   wd-not-e1       it is NOT well defined over do1;
--   wd-non-max      hence the classifying sieve is {e0}, strictly
--                   between ⊥ and ⊤;
--   here-obs        the STAGEWISE reading holds at obs;
--   here-do1-fails  and fails after restriction along e1, so the
--                   stagewise predicate is NOT closed under
--                   restriction and is not a truth value at all;
--   liftpairs-fails and the site condition LiftPairs fails here,
--                   which is why the two readings come apart.
--
-- Both Pearl and Hernán argue over a yes-or-no question.  On this
-- site the internal answer is a proper sieve.
-- ============================================================

module Topos.VersionSite where

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit; tt; isSetUnit)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Empty as E using (⊥; isProp⊥; rec*)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁)

open import FDist-Convex using (FDist; pure; mapF; trunc; 𝔼)
open import WeightQ using (Weight; w0; w1; w0≢w1)

open import Topos.Cat
open import Topos.PSh
open import Topos.Omega
open import Topos.InternalDist
open import Topos.InternalDist using (mapF-id)
open import Topos.Exponential
open import Topos.DoubleNegation using (⊥S)
open import Topos.InterventionSite
open import Topos.VersionFactoring

-- ------------------------------------------------------------
-- Outcome: Bool at every regime, restriction the identity.  The
-- outcome is visible in every regime; nothing is hidden by the
-- site itself.
-- ------------------------------------------------------------
OutI : PSh Iv ℓ-zero
OutI = record
  { F₀ = λ _ → Bool ; F₁ = λ _ b → b
  ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → isSetBool }

-- ------------------------------------------------------------
-- Versions.  One at obs, one at do0, two at do1.  Refinement
-- along e1 makes a NEW version available; restriction along e1
-- names the diet version.
-- ------------------------------------------------------------
VerI-Ob : IObj → Type
VerI-Ob obs = Unit
VerI-Ob do0 = Unit
VerI-Ob do1 = Bool

VerI-restr : {d c : IObj} → IHom d c → VerI-Ob c → VerI-Ob d
VerI-restr idₒ v = v
VerI-restr id₀ v = v
VerI-restr id₁ v = v
VerI-restr e0  _ = tt
VerI-restr e1  _ = true

VerI-isSet : (c : IObj) → isSet (VerI-Ob c)
VerI-isSet obs = isSetUnit
VerI-isSet do0 = isSetUnit
VerI-isSet do1 = isSetBool

VerI : PSh Iv ℓ-zero
VerI = record
  { F₀ = VerI-Ob ; F₁ = VerI-restr
  ; F-id = λ {x} v → lemId x v
  ; F-comp = λ {x} {y} {z} f g v → lemComp f g v
  ; isSetF₀ = VerI-isSet }
  where
    lemId : (x : IObj) (v : VerI-Ob x) → VerI-restr (idI {x}) v ≡ v
    lemId obs v = refl
    lemId do0 v = refl
    lemId do1 v = refl
    lemComp : {x y z : IObj} (f : IHom x y) (g : IHom y z) (v : VerI-Ob z)
            → VerI-restr (f ⋆I g) v ≡ VerI-restr f (VerI-restr g v)
    lemComp idₒ idₒ v = refl
    lemComp id₀ id₀ v = refl
    lemComp id₁ id₁ v = refl
    lemComp e0  idₒ v = refl
    lemComp e1  idₒ v = refl
    lemComp id₀ e0  v = refl
    lemComp id₁ e1  v = refl

-- ------------------------------------------------------------
-- Values.  Pearl's object: the BMI value alone.  Here every
-- version realises the same value, so the value object is a
-- point and the coarsening is the unique map.  This is the
-- extreme case of Hernán's complaint, and the cleanest one.
-- ------------------------------------------------------------
ValU : PSh Iv ℓ-zero
ValU = record
  { F₀ = λ _ → Unit ; F₁ = λ _ _ → tt
  ; F-id = λ _ → refl ; F-comp = λ _ _ _ → refl ; isSetF₀ = λ _ → isSetUnit }

pU : Nat {C = Iv} VerI ValU
pU = (λ _ _ → tt) , (λ _ _ _ _ → refl)

-- ------------------------------------------------------------
-- The mechanism object and the mechanism.
-- ------------------------------------------------------------
MechI : PSh Iv ℓ-zero
MechI = MechV VerI ValU pU OutI

-- The outcome is the version: diet and surgery kill differently.
-- From obs only the diet version is nameable, so the mechanism
-- looks constant there; the surgery version appears only at do1.
mI : PSh.F₀ MechI obs
mI = app , nat
  where
    app : (d : IObj) → IHom d obs → VerI-Ob d → FDist Bool
    app obs idₒ _ = pure true
    app do0 e0  _ = pure true
    app do1 e1  b = pure b
    nat : ExpNat {C = Iv} VerI (Dist_E {C = Iv} OutI) obs app
    nat obs obs idₒ idₒ a = refl
    nat do0 do0 id₀ e0  a = refl
    nat do1 do1 id₁ e1  a = refl
    nat do0 obs e0  idₒ a = refl
    nat do1 obs e1  idₒ a = refl

-- ------------------------------------------------------------
-- The classifying sieve of well-definedness at obs.
-- ------------------------------------------------------------
wdSieve : Sieve {C = Iv} obs
wdSieve = χ-wd-sieve VerI ValU pU OutI obs mI

-- WELL DEFINED OVER do0.  In the diet-only regime there is one
-- version, so factoring through the value is free.
wd-at-e0 : fst (fst wdSieve do0 e0)
wd-at-e0 do0 id₀ a b q = refl

-- NOT WELL DEFINED OVER do1.  Diet and surgery have the same BMI
-- value and different mortality, so the mechanism does not factor.
indTrue : Bool → Weight
indTrue true  = w1
indTrue false = w0

wd-not-e1 : ¬ (fst (fst wdSieve do1 e1))
wd-not-e1 h =
  w0≢w1 (sym (cong (λ d → 𝔼 d indTrue) (h do1 id₁ true false refl)))

-- ------------------------------------------------------------
-- So the truth value is strictly between ⊥ and ⊤.  It is the
-- sieve {e0}: the effect of BMI is well defined exactly in the
-- diet-only regime.
-- ------------------------------------------------------------
wd-not-⊤ : ¬ (wdSieve ≡ maximal {C = Iv} obs)
wd-not-⊤ p = wd-not-e1 (transport (λ i → fst (fst (p (~ i)) do1 e1)) _)

wd-not-⊥ : ¬ (wdSieve ≡ ⊥S {C = Iv} obs)
wd-not-⊥ p = rec* (transport (λ i → fst (fst (p i) do0 e0)) wd-at-e0)

wd-non-max : ( fst (fst wdSieve do0 e0) ) × ( ¬ (fst (fst wdSieve do1 e1)) )
wd-non-max = wd-at-e0 , wd-not-e1

-- The identity is not in either, so the sieve is pinned exactly.
-- The only arrows into obs are idₒ, e0 and e1, so the three facts
-- below determine wdSieve completely: it is the principal sieve
-- generated by e0.  That is the same discriminating truth value
-- that Topos.MechanismSite.copy-non-max produces for
-- admissibility, reached here by a different route: there the
-- outcome type is trivial at do0, here the outcome stays Bool at
-- every regime and it is the VERSIONS that are narrowed.
wd-not-idₒ : ¬ (fst (fst wdSieve obs idₒ))
wd-not-idₒ h =
  w0≢w1 (sym (cong (λ d → 𝔼 d indTrue) (h do1 e1 true false refl)))

wd-sieve-exactly :
    ( ¬ (fst (fst wdSieve obs idₒ)) )
  × ( fst (fst wdSieve do0 e0) )
  × ( ¬ (fst (fst wdSieve do1 e1)) )
wd-sieve-exactly = wd-not-idₒ , wd-at-e0 , wd-not-e1

-- ------------------------------------------------------------
-- THE STAGEWISE PREDICATE IS NOT A TRUTH VALUE.
--
-- "The effect is well defined in this regime", read at obs alone,
-- holds: obs names one version.  Restricted along e1 it fails.  A
-- predicate that can fail on restriction is not closed under
-- precomposition, so it is not a sieve, so it is not an element of
-- Ω.  Only the hereditary reading is.
-- ------------------------------------------------------------
here-obs : Here VerI ValU pU OutI obs mI
here-obs a b q = refl

here-do1-fails : ¬ (Here VerI ValU pU OutI do1 (PSh.F₁ MechI e1 mI))
here-do1-fails h =
  w0≢w1 (sym (cong (λ d → 𝔼 d indTrue) (h true false refl)))

here-not-restriction-stable :
    ( Here VerI ValU pU OutI obs mI )
  × ( ¬ (Here VerI ValU pU OutI do1 (PSh.F₁ MechI e1 mI)) )
here-not-restriction-stable = here-obs , here-do1-fails

-- ------------------------------------------------------------
-- AND THE SITE CONDITION FAILS.  The pair (diet, surgery) at do1
-- has the same value but is not the restriction of any pair at
-- obs, because obs has a single version.  This is the exact sense
-- in which refinement ADDS versions here, and it is why the two
-- readings come apart.
-- ------------------------------------------------------------
liftpairs-fails : ¬ (LiftPairs VerI ValU pU OutI obs)
liftpairs-fails lp =
  PT.rec isProp⊥ (λ { (a , b , sv , ea , eb) → true≢false eb })
         (lp do1 e1 true false refl)

-- ------------------------------------------------------------
-- AND THE GRADING IS NOT AN ARTEFACT OF A COLLAPSING OUTCOME.
--
-- The outcome presheaf here is Bool at every regime with identity
-- restriction, so no refinement loses outcome information.  That
-- is Topos.VersionFactoring.OutFaithful.  Topos.MechanismSite
-- gets its non-maximal sieve the other way, by collapsing the
-- value type at do0; this module does not.
-- ------------------------------------------------------------
outI-faithful : OutFaithful VerI ValU pU OutI
outI-faithful d e k u v pth = sym (mapF-id u) ∙ pth ∙ mapF-id v

-- Consequently the failure of LiftPairs is FORCED, not chosen.
-- The dichotomy theorem says that with faithful outcomes and
-- LiftPairs a non-maximal sieve must be empty; this one is not.
-- So the grading here is caused by, and only by, the fact that
-- refinement makes a new version of "BMI = x" available.
liftpairs-forced : ¬ (LiftPairs VerI ValU pU OutI obs)
liftpairs-forced lp =
  wd-not-⊥ (two-valued VerI ValU pU OutI outI-faithful obs lp mI wd-not-⊤)
